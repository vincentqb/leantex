module

public import Tests.Support
public import LeanTex.Cli.FontAssembly
import LeanTex.Core.BlockTemplate

public section

open LeanTex.Core LeanTex.Cli

namespace Tests.BlockTemplate

/-!
# A block template's rule stands beside its box

beamer sets a block between two templates, `block begin` and `block end`
(beamerbaselocalstructure.sty), and a theme that replaces the pair writes its
look in TeX's box-and-rule vocabulary: the title boxed with `\setbox`, a
`\vrule` reading the box's `\ht` and `\dp` in an `\llap` beside it, the box
placed with `\box`. The engine reads the pair (`BlockTemplate.read`) into the
record both artifacts set a block by (`Ir.BlockShape`), so the rule a
template draws is drawn, where TeX draws it.

lualatex (TeX Live 2026, beamer with moloch at 10 pt, OpenSans Regular as the
only face, every frame `[t]` with room to spare so each glue keeps its natural
size) ships these invented probes with the distances below, read by a node
walker over the page lists in four-decimal TeX points: three templates of one
shape — a rule beside the title's box, hanging in the margin in `em`s of the
body font; a rule beside the box holding title and body (its `\vbox\bgroup`
opened in `block begin`, closed in `block end`); a rule inside the line at
the text edge, the title's box narrowed to make room — titled, untitled and
wrapped, plain, alerted (a right-hand rule, the box placed with `\copy`) and
example blocks. TeX's semantics the distances show: a `\usebeamercolor[fg]`
before the title in its box puts a colour change on the box's list, so the
title's paragraph spends `\parskip` inside the box as well as before the line
holding it; the box joins its list by the interline rule from its height, so
a two-line title box takes `\lineskip` where a one-line one takes the
baseline skip; and an `\addtobeamertemplate` before the template's install is
dropped with the template it modified.

Four more probes hold what a review of the reading found, the same way: each
arm of the title test stands its own skips, inside the box holding title and
body where it stands them there (`armed`); a template that keeps an empty
title box sets the box, a line of its struts or of nothing, and every rule
beside it once (`boxed`); a title's `\strut` and its lines read its own
font's `\baselineskip` (`sized`); and beamer's default blocks place a sized
title by the page's interline rule (`plainsized`).

A second review's probes hold the rest: an empty title box under a declared
size, strutted and not, in both artifacts (`emptybox`); a title with no box of
its own, a paragraph of the block's list, empty the struts' line or no line at
all (`plainempty`); a title font declared
with `size*` standing its own `\baselineskip`, templated and in the default
blocks (`starsized`, `plainstar`); `\usebeamercolor` binding only the channels
its element sets (`chain`); a title font declared before the theme, and one
declared with the star (`parentChecks`); and a block's unread style keys kept
out of both artifacts, each the one refusal at its site.

A rule reaching by its title's lines, read in the title's font, is held the
same way (`capitals`): a `\dimexpr` over the title box's height and depth
less the `\parskip` its list opens on, `\baselineskip` and
`\fontcharht\font`H`, and length registers assigned with `\global` inside
the box; lualatex centres such a rule on the capitals, grows a line whose
rule reaches past its box, and spaces what follows from a rule deeper than
the box, and both artifacts do (`capitalChecks`, `capitalHtmlChecks`).

A rule beside the whole block is held so too (`wholebar`): a template that
sets the body in a box to measure its lines, puts them back where they stood
and stands the body's part of the rule on the last baseline is read as one
rule from the title's capitals to its depth below that baseline
(`wholeBarChecks`, `wholeBarHtmlChecks`), and one that would move a line or
the rule is named (`wholeBarReadingChecks`).
-/

/-- A rule beside the title's box, hanging `.6em` into the margin, `.3em`
wide; the alerted kind's rule on the right, `4pt` out, `3pt` wide, placed
after `\copy`; and an `\addtobeamertemplate` small skip after the install. -/
def hanging : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n" ++
  "\\usetheme{moloch}\n" ++
  "\\definecolor{probeInk}{HTML}{1F2A44}\n" ++
  "\\definecolor{probeEdge}{HTML}{2E8B57}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setbeamercolor{probe edge}{bg=probeEdge}\n" ++
  "\\setlength{\\parskip}{4pt}\n" ++
  "\\makeatletter\n" ++
  "\\newbox\\probe@box\n" ++
  "\\newcommand{\\probe@open}[1]{%\n" ++
  "  \\par\\vskip\\medskipamount\n" ++
  "  \\ifx\\insertblocktitle\\@empty\\else\n" ++
  "    \\setbox\\probe@box\\vbox{\\hsize\\linewidth\n" ++
  "      \\usebeamerfont*{block title#1}\\usebeamercolor[fg]{block title#1}%\n" ++
  "      \\strut\\insertblocktitle\\strut\\par}%\n" ++
  "    \\noindent\\llap{{\\usebeamercolor[bg]{probe edge}%\n" ++
  "        \\vrule width .3em height \\ht\\probe@box depth \\dp\\probe@box}%\n" ++
  "      \\hskip .6em}%\n" ++
  "    \\box\\probe@box\\par\\nobreak\n" ++
  "  \\fi\n" ++
  "  \\usebeamerfont{block body#1}\\usebeamercolor[fg]{block body#1}}\n" ++
  "\\newcommand{\\probe@close}{\\par\\vskip\\smallskipamount}\n" ++
  "\\defbeamertemplate*{block begin}{probe}{\\probe@open{}}\n" ++
  "\\defbeamertemplate*{block end}{probe}{\\probe@close}\n" ++
  "\\defbeamertemplate*{block alerted begin}{probe}{%\n" ++
  "  \\par\\vskip\\medskipamount\n" ++
  "  \\ifx\\insertblocktitle\\@empty\\else\n" ++
  "    \\setbox\\probe@box\\vbox{\\hsize\\linewidth\n" ++
  "      \\usebeamerfont*{block title alerted}\\usebeamercolor[fg]{block title alerted}%\n" ++
  "      \\strut\\insertblocktitle\\strut\\par}%\n" ++
  "    \\noindent\\copy\\probe@box\n" ++
  "    \\rlap{\\hskip 4pt{\\usebeamercolor[fg]{alerted text}%\n" ++
  "        \\vrule width 3pt height \\ht\\probe@box depth \\dp\\probe@box}}%\n" ++
  "    \\par\\nobreak\n" ++
  "  \\fi\n" ++
  "  \\usebeamerfont{block body alerted}\\usebeamercolor[fg]{block body alerted}}\n" ++
  "\\defbeamertemplate*{block alerted end}{probe}{\\probe@close}\n" ++
  "\\defbeamertemplate*{block example begin}{probe}{\\probe@open{ example}}\n" ++
  "\\defbeamertemplate*{block example end}{probe}{\\probe@close}\n" ++
  "\\makeatother\n" ++
  "\\addtobeamertemplate{block begin}{}{\\smallskip}\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[t]{Hanging}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Alpha title words}\n" ++
  "Body words here.\n" ++
  "\n" ++
  "Second body paragraph.\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Right}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{alertblock}{Beta title words}\n" ++
  "Third body words.\n" ++
  "\\end{alertblock}\n" ++
  "\\begin{block}{}\n" ++
  "Untitled body words.\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Example}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{exampleblock}{Gamma title words}\n" ++
  "Fourth body words.\n" ++
  "\\end{exampleblock}\n" ++
  "\\begin{block}{A very long block title that certainly wraps onto a second line of text because it keeps going and going}\n" ++
  "Fifth body words.\n" ++
  "\\end{block}\n" ++
  "\\end{frame}\n" ++
  "\\end{document}\n"

/-- A rule beside the box holding title and body, `5pt` out, `2.5pt` wide. -/
def whole : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n" ++
  "\\usetheme{moloch}\n" ++
  "\\definecolor{probeInk}{HTML}{1F2A44}\n" ++
  "\\definecolor{probeEdge}{HTML}{2E8B57}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setbeamercolor{probe edge}{fg=probeEdge}\n" ++
  "\\setlength{\\parskip}{4pt}\n" ++
  "\\makeatletter\n" ++
  "\\newbox\\probe@whole\n" ++
  "\\newcommand{\\probe@open}[1]{%\n" ++
  "  \\par\\vskip\\medskipamount\n" ++
  "  \\setbox\\probe@whole\\vbox\\bgroup\\hsize\\linewidth\n" ++
  "  \\ifx\\insertblocktitle\\@empty\\else\n" ++
  "    {\\usebeamerfont*{block title#1}\\usebeamercolor[fg]{block title#1}%\n" ++
  "      \\strut\\insertblocktitle\\strut\\par}%\n" ++
  "  \\fi\n" ++
  "  \\usebeamerfont{block body#1}\\usebeamercolor[fg]{block body#1}}\n" ++
  "\\newcommand{\\probe@close}{\\par\\egroup\n" ++
  "  \\noindent\\llap{{\\usebeamercolor[fg]{probe edge}%\n" ++
  "      \\vrule width 2.5pt height \\ht\\probe@whole depth \\dp\\probe@whole}%\n" ++
  "    \\hskip 5pt}%\n" ++
  "  \\box\\probe@whole\\par\\vskip\\smallskipamount}\n" ++
  "\\defbeamertemplate*{block begin}{probe}{\\probe@open{}}\n" ++
  "\\defbeamertemplate*{block end}{probe}{\\probe@close}\n" ++
  "\\makeatother\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[t]{Whole}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Alpha title words}\n" ++
  "Body words here.\n" ++
  "\n" ++
  "Second body paragraph.\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Untitled}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{}\n" ++
  "Untitled body words.\n" ++
  "\\end{block}\n" ++
  "\\begin{block}{}\n" ++
  "One untitled line.\n" ++
  "\n" ++
  "And another paragraph.\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\end{document}\n"

/-- A rule inside the line at the text edge, `2pt` wide and `5pt` from the
title's box, which is `7pt` narrower; no `\parskip`, the colour selected
before the box, and an addition made before the install. -/
def inside : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n" ++
  "\\usetheme{moloch}\n" ++
  "\\definecolor{probeInk}{HTML}{1F2A44}\n" ++
  "\\definecolor{probeEdge}{HTML}{2E8B57}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setbeamercolor{probe edge}{bg=probeEdge}\n" ++
  "\\addtobeamertemplate{block begin}{}{\\bigskip}\n" ++
  "\\makeatletter\n" ++
  "\\newbox\\probe@box\n" ++
  "\\setbeamertemplate{block begin}{%\n" ++
  "  \\par\\vskip\\medskipamount\n" ++
  "  \\ifx\\insertblocktitle\\@empty\\else\n" ++
  "    \\usebeamerfont*{block title}\\usebeamercolor[fg]{block title}%\n" ++
  "    \\setbox\\probe@box\\vbox{\\hsize\\dimexpr\\linewidth-7pt\\relax\n" ++
  "      \\strut\\insertblocktitle\\strut\\par}%\n" ++
  "    \\noindent{\\usebeamercolor[bg]{probe edge}%\n" ++
  "        \\vrule width 2pt height \\ht\\probe@box depth \\dp\\probe@box}%\n" ++
  "      \\hskip 5pt%\n" ++
  "    \\box\\probe@box\\par\\nobreak\n" ++
  "  \\fi\n" ++
  "  \\usebeamerfont{block body}\\usebeamercolor[fg]{block body}}\n" ++
  "\\setbeamertemplate{block end}{\\par\\vskip\\smallskipamount}\n" ++
  "\\makeatother\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[t]{Inside}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Alpha title words}\n" ++
  "Body words here.\n" ++
  "\n" ++
  "Second body paragraph.\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Wrapped}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{A very long block title that certainly wraps onto a second line of text because it keeps going and going}\n" ++
  "Fourth body words.\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\end{document}\n"

/-- A template whose title test stands skips of its own in each arm: `5pt` where
the title is empty, `4pt` after the title's box; and the alerted kind's box
holding title and body, `3pt` inside it where the title is empty, `2pt` after
the title, its rule on the right after `\copy`, at `\parskip` 3pt. -/
def armedSource : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n" ++
  "\\usetheme{moloch}\n" ++
  "\\definecolor{probeInk}{HTML}{1F2A44}\n" ++
  "\\definecolor{probeEdge}{HTML}{2E8B57}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setbeamercolor{probe edge}{bg=probeEdge}\n" ++
  "\\setlength{\\parskip}{3pt}\n" ++
  "\\makeatletter\n" ++
  "\\newbox\\probe@box\n" ++
  "\\setbeamertemplate{block begin}{%\n" ++
  "  \\par\\vskip\\medskipamount\n" ++
  "  \\ifx\\insertblocktitle\\@empty\n" ++
  "    \\vskip 5pt\n" ++
  "  \\else\n" ++
  "    \\setbox\\probe@box\\vbox{\\hsize\\linewidth\n" ++
  "      \\usebeamerfont*{block title}\\usebeamercolor[fg]{block title}%\n" ++
  "      \\strut\\insertblocktitle\\strut\\par}%\n" ++
  "    \\noindent\\llap{{\\usebeamercolor[bg]{probe edge}%\n" ++
  "        \\vrule width 1.2pt height \\ht\\probe@box depth \\dp\\probe@box}\\hskip 2pt}%\n" ++
  "    \\box\\probe@box\\par\\nobreak\\vskip 4pt\n" ++
  "  \\fi\n" ++
  "  \\usebeamerfont{block body}\\usebeamercolor[fg]{block body}}\n" ++
  "\\setbeamertemplate{block end}{\\par\\vskip\\smallskipamount}\n" ++
  "\\newbox\\probe@whole\n" ++
  "\\setbeamertemplate{block alerted begin}{%\n" ++
  "  \\par\\vskip\\bigskipamount\n" ++
  "  \\setbox\\probe@whole\\vbox\\bgroup\\hsize\\linewidth\n" ++
  "  \\ifx\\insertblocktitle\\@empty\n" ++
  "    \\vskip 3pt\n" ++
  "  \\else\n" ++
  "    {\\usebeamerfont*{block title alerted}\\usebeamercolor[fg]{block title alerted}%\n" ++
  "      \\strut\\insertblocktitle\\strut\\par}%\n" ++
  "    \\vskip 2pt\n" ++
  "  \\fi\n" ++
  "  \\usebeamerfont{block body alerted}\\usebeamercolor[fg]{block body alerted}}\n" ++
  "\\setbeamertemplate{block alerted end}{\\par\\egroup\n" ++
  "  \\noindent\\copy\\probe@whole\\rlap{\\hskip 4pt{\\usebeamercolor[bg]{probe edge}%\n" ++
  "      \\vrule width 1pt height \\ht\\probe@whole depth \\dp\\probe@whole}}%\n" ++
  "  \\par\\vskip\\smallskipamount}\n" ++
  "\\makeatother\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[t]{Armed}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Alpha title words}\n" ++
  "Body words here.\n" ++
  "\\end{block}\n" ++
  "Middle paragraph here.\n" ++
  "\\begin{block}{}\n" ++
  "Untitled body words.\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Armed whole}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{alertblock}{Beta title words}\n" ++
  "Third body words.\n" ++
  "\n" ++
  "Second body paragraph.\n" ++
  "\\end{alertblock}\n" ++
  "Middle paragraph here.\n" ++
  "\\begin{alertblock}{}\n" ++
  "Untitled whole words.\n" ++
  "\\end{alertblock}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\end{document}\n"

/-- A template with no title test, so an untitled block keeps the title's box,
empty: rules inside the line on both sides of the box at `\parskip` 2pt;
the alerted kind unstrutted, so its empty box holds no paragraph. -/
def boxedSource : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n" ++
  "\\usetheme{moloch}\n" ++
  "\\definecolor{probeInk}{HTML}{1F2A44}\n" ++
  "\\definecolor{probeEdge}{HTML}{2E8B57}\n" ++
  "\\definecolor{probeEdgeTwo}{HTML}{8B2E57}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setbeamercolor{probe edge}{bg=probeEdge}\n" ++
  "\\setlength{\\parskip}{2pt}\n" ++
  "\\makeatletter\n" ++
  "\\newbox\\probe@box\n" ++
  "\\setbeamertemplate{block begin}{%\n" ++
  "  \\par\\vspace{4pt}%\n" ++
  "  \\setbox\\probe@box\\vbox{\\hsize\\linewidth\\advance\\hsize by -6pt\n" ++
  "    \\usebeamerfont*{block title}\\usebeamercolor[fg]{block title}%\n" ++
  "    \\strut\\insertblocktitle\\strut\\par}%\n" ++
  "  \\noindent{\\color{probeEdgeTwo}\\vrule width 1.5pt height \\ht\\probe@box depth \\dp\\probe@box}%\n" ++
  "  \\hskip 1.5pt\\copy\\probe@box\\hskip 1pt{\\usebeamercolor[bg]{probe edge}%\n" ++
  "    \\vrule width 2pt height \\ht\\probe@box depth \\dp\\probe@box}%\n" ++
  "  \\par\\nobreak\\vskip 3pt plus 1pt\n" ++
  "  \\usebeamerfont{block body}\\usebeamercolor[fg]{block body}}\n" ++
  "\\setbeamertemplate{block end}{\\par\\vskip 5pt}\n" ++
  "\\setbeamertemplate{block alerted begin}{%\n" ++
  "  \\par\\vspace{4pt}%\n" ++
  "  \\setbox\\probe@box\\vbox{\\hsize\\linewidth\\advance\\hsize by -3pt\n" ++
  "    \\usebeamerfont*{block title alerted}\\usebeamercolor[fg]{block title alerted}%\n" ++
  "    \\insertblocktitle\\par}%\n" ++
  "  \\noindent\\copy\\probe@box\\hskip 1pt{\\usebeamercolor[bg]{probe edge}%\n" ++
  "    \\vrule width 2pt height \\ht\\probe@box depth \\dp\\probe@box}%\n" ++
  "  \\par\\nobreak\\vskip 3pt\n" ++
  "  \\usebeamerfont{block body alerted}\\usebeamercolor[fg]{block body alerted}}\n" ++
  "\\setbeamertemplate{block alerted end}{\\par\\vskip 5pt}\n" ++
  "\\makeatother\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[t]{Boxed}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Gamma title words}\n" ++
  "Body words here.\n" ++
  "\\end{block}\n" ++
  "\\begin{block}{}\n" ++
  "Untitled boxed words.\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Boxed bare}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{alertblock}{Delta title words}\n" ++
  "Third body words.\n" ++
  "\\end{alertblock}\n" ++
  "\\begin{alertblock}{}\n" ++
  "Untitled bare words.\n" ++
  "\\end{alertblock}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\end{document}\n"

/-- The title's box in a declared title size: `\large` for the plain block —
moloch's own alerted title font keeps the alerted one's — and `\small` for
the example; one-line and two-line titles. -/
def sizedSource : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n" ++
  "\\usetheme{moloch}\n" ++
  "\\definecolor{probeInk}{HTML}{1F2A44}\n" ++
  "\\definecolor{probeEdge}{HTML}{2E8B57}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setbeamercolor{probe edge}{bg=probeEdge}\n" ++
  "\\setbeamerfont{block title}{size=\\large}\n" ++
  "\\setbeamerfont{block title example}{size=\\small}\n" ++
  "\\makeatletter\n" ++
  "\\newbox\\probe@box\n" ++
  "\\newcommand{\\probe@open}[1]{%\n" ++
  "  \\par\\vskip\\medskipamount\n" ++
  "  \\ifx\\insertblocktitle\\@empty\\else\n" ++
  "    \\setbox\\probe@box\\vbox{\\hsize\\linewidth\n" ++
  "      \\usebeamerfont*{block title#1}\\usebeamercolor[fg]{block title#1}%\n" ++
  "      \\strut\\insertblocktitle\\strut\\par}%\n" ++
  "    \\noindent\\llap{{\\usebeamercolor[bg]{probe edge}%\n" ++
  "        \\vrule width 1.2pt height \\ht\\probe@box depth \\dp\\probe@box}\\hskip 2pt}%\n" ++
  "    \\box\\probe@box\\par\\nobreak\n" ++
  "  \\fi\n" ++
  "  \\usebeamerfont{block body#1}\\usebeamercolor[fg]{block body#1}}\n" ++
  "\\newcommand{\\probe@close}{\\par\\vskip\\smallskipamount}\n" ++
  "\\defbeamertemplate*{block begin}{probe}{\\probe@open{}}\n" ++
  "\\defbeamertemplate*{block end}{probe}{\\probe@close}\n" ++
  "\\defbeamertemplate*{block alerted begin}{probe}{\\probe@open{ alerted}}\n" ++
  "\\defbeamertemplate*{block alerted end}{probe}{\\probe@close}\n" ++
  "\\defbeamertemplate*{block example begin}{probe}{\\probe@open{ example}}\n" ++
  "\\defbeamertemplate*{block example end}{probe}{\\probe@close}\n" ++
  "\\makeatother\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[t]{Sized}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Alpha title words}\n" ++
  "Body words here.\n" ++
  "\\end{block}\n" ++
  "\\begin{alertblock}{Beta title words}\n" ++
  "Third body words.\n" ++
  "\\end{alertblock}\n" ++
  "\\begin{exampleblock}{Gamma title words}\n" ++
  "Fourth body words.\n" ++
  "\\end{exampleblock}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Sized wrap}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{First title line\\\\Second title line}\n" ++
  "Fifth body words.\n" ++
  "\\end{block}\n" ++
  "\\begin{exampleblock}{Third title line\\\\Fourth title line}\n" ++
  "Sixth body words.\n" ++
  "\\end{exampleblock}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\end{document}\n"

/-- beamer's default blocks with a declared title size and no template of the
document's own. -/
def plainSizedSource : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n" ++
  "\\usetheme{moloch}\n" ++
  "\\definecolor{probeInk}{HTML}{1F2A44}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setbeamerfont{block title}{size=\\large}\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[t]{Plain sized}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Alpha heading words}\n" ++
  "Body words here.\n" ++
  "\\end{block}\n" ++
  "\\begin{alertblock}{Beta heading words}\n" ++
  "Third body words.\n" ++
  "\\end{alertblock}\n" ++
  "\\begin{exampleblock}{Gamma heading words}\n" ++
  "Fourth body words.\n" ++
  "\\end{exampleblock}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Plain sized wrap}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{First heading line\\\\Second heading line}\n" ++
  "Fifth body words.\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\end{document}\n"

/-- A rule painted by `\usebeamercolor{element}\color{bg}`, in the epoch
each frame stands in. -/
def channelsSource : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n" ++
  "\\usetheme{moloch}\n" ++
  "\\definecolor{probeInk}{HTML}{1F2A44}\n" ++
  "\\definecolor{probeEdge}{HTML}{2E8B57}\n" ++
  "\\definecolor{probeRed}{HTML}{B22222}\n" ++
  "\\definecolor{probeBlue}{HTML}{1E40AF}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setbeamercolor{probe edge}{fg=probeInk,bg=probeEdge}\n" ++
  "\\makeatletter\n" ++
  "\\newbox\\probe@box\n" ++
  "\\setbeamertemplate{block begin}{%\n" ++
  "  \\par\\vskip\\medskipamount\n" ++
  "  \\ifx\\insertblocktitle\\@empty\\else\n" ++
  "    \\setbox\\probe@box\\vbox{\\hsize\\linewidth\n" ++
  "      \\usebeamerfont*{block title}\\usebeamercolor[fg]{block title}%\n" ++
  "      \\strut\\insertblocktitle\\strut\\par}%\n" ++
  "    \\noindent\\llap{{\\usebeamercolor{probe edge}\\color{bg}%\n" ++
  "        \\vrule width 1.2pt height \\ht\\probe@box depth \\dp\\probe@box}\\hskip 2pt}%\n" ++
  "    \\box\\probe@box\\par\\nobreak\n" ++
  "  \\fi\n" ++
  "  \\usebeamerfont{block body}\\usebeamercolor[fg]{block body}}\n" ++
  "\\setbeamertemplate{block end}{\\par\\vskip\\smallskipamount}\n" ++
  "\\makeatother\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[t]{Channels}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Alpha title words}\n" ++
  "Body words here.\n" ++
  "\\end{block}\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Channels red}\n" ++
  "\\setbeamercolor{probe edge}{bg=probeRed}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Beta title words}\n" ++
  "Third body words.\n" ++
  "\\end{block}\n" ++
  "\\end{frame}\n" ++
  "\\setbeamercolor{probe edge}{bg=probeBlue}\n" ++
  "\\begin{frame}[t]{Channels blue}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Gamma title words}\n" ++
  "Fourth body words.\n" ++
  "\\end{block}\n" ++
  "\\end{frame}\n" ++
  "\\end{document}\n"

/-- The title's box kept empty under declared title sizes: strutted at
`\large`, two rules inside the line beside it; the alerted kind unstrutted,
so its empty box holds no paragraph; the example strutted at `\small`. -/
def emptyBoxSource : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n" ++
  "\\usetheme{moloch}\n" ++
  "\\definecolor{probeInk}{HTML}{1F2A44}\n" ++
  "\\definecolor{probeEdge}{HTML}{2E8B57}\n" ++
  "\\definecolor{probeEdgeTwo}{HTML}{8B2E57}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setbeamercolor{probe edge}{bg=probeEdge}\n" ++
  "\\setbeamerfont{block title}{size=\\large}\n" ++
  "\\setbeamerfont{block title example}{size=\\small}\n" ++
  "\\setlength{\\parskip}{2pt}\n" ++
  "\\makeatletter\n" ++
  "\\newbox\\probe@box\n" ++
  "\\setbeamertemplate{block begin}{%\n" ++
  "  \\par\\vspace{4pt}%\n" ++
  "  \\setbox\\probe@box\\vbox{\\hsize\\linewidth\\advance\\hsize by -6pt\n" ++
  "    \\usebeamerfont*{block title}\\usebeamercolor[fg]{block title}%\n" ++
  "    \\strut\\insertblocktitle\\strut\\par}%\n" ++
  "  \\noindent{\\color{probeEdgeTwo}\\vrule width 1.5pt height \\ht\\probe@box depth \\dp\\probe@box}%\n" ++
  "  \\hskip 1.5pt\\copy\\probe@box\\hskip 1pt{\\usebeamercolor[bg]{probe edge}%\n" ++
  "    \\vrule width 2pt height \\ht\\probe@box depth \\dp\\probe@box}%\n" ++
  "  \\par\\nobreak\\vskip 3pt\n" ++
  "  \\usebeamerfont{block body}\\usebeamercolor[fg]{block body}}\n" ++
  "\\setbeamertemplate{block end}{\\par\\vskip 5pt}\n" ++
  "\\setbeamertemplate{block alerted begin}{%\n" ++
  "  \\par\\vspace{4pt}%\n" ++
  "  \\setbox\\probe@box\\vbox{\\hsize\\linewidth\\advance\\hsize by -3pt\n" ++
  "    \\usebeamerfont*{block title alerted}\\usebeamercolor[fg]{block title alerted}%\n" ++
  "    \\insertblocktitle\\par}%\n" ++
  "  \\noindent\\copy\\probe@box\\hskip 1pt{\\usebeamercolor[bg]{probe edge}%\n" ++
  "    \\vrule width 2pt height \\ht\\probe@box depth \\dp\\probe@box}%\n" ++
  "  \\par\\nobreak\\vskip 3pt\n" ++
  "  \\usebeamerfont{block body alerted}\\usebeamercolor[fg]{block body alerted}}\n" ++
  "\\setbeamertemplate{block alerted end}{\\par\\vskip 5pt}\n" ++
  "\\setbeamertemplate{block example begin}{%\n" ++
  "  \\par\\vspace{4pt}%\n" ++
  "  \\setbox\\probe@box\\vbox{\\hsize\\linewidth\\advance\\hsize by -3pt\n" ++
  "    \\usebeamerfont*{block title example}\\usebeamercolor[fg]{block title example}%\n" ++
  "    \\strut\\insertblocktitle\\strut\\par}%\n" ++
  "  \\noindent\\copy\\probe@box\\hskip 1pt{\\usebeamercolor[bg]{probe edge}%\n" ++
  "    \\vrule width 2pt height \\ht\\probe@box depth \\dp\\probe@box}%\n" ++
  "  \\par\\nobreak\\vskip 3pt\n" ++
  "  \\usebeamerfont{block body example}\\usebeamercolor[fg]{block body example}}\n" ++
  "\\setbeamertemplate{block example end}{\\par\\vskip 5pt}\n" ++
  "\\makeatother\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[t]{Empty large}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Gamma title words}\n" ++
  "Body words here.\n" ++
  "\\end{block}\n" ++
  "\\begin{block}{}\n" ++
  "Untitled boxed words.\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Empty bare}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{alertblock}{Delta title words}\n" ++
  "Third body words.\n" ++
  "\\end{alertblock}\n" ++
  "\\begin{alertblock}{}\n" ++
  "Untitled bare words.\n" ++
  "\\end{alertblock}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Empty small}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{exampleblock}{Epsilon title words}\n" ++
  "Fifth body words.\n" ++
  "\\end{exampleblock}\n" ++
  "\\begin{exampleblock}{}\n" ++
  "Untitled small words.\n" ++
  "\\end{exampleblock}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\end{document}\n"

/-- Rules painted through two `\usebeamercolor`s, the later element setting
only the other channel: `\color{bg}` after a foreground-only element,
`\color{fg}` after a background-only one, and `\usebeamercolor[bg]` of the
foreground-only one; then a frame that gives it a background. -/
def chainSource : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n" ++
  "\\usetheme{moloch}\n" ++
  "\\definecolor{probeInk}{HTML}{1F2A44}\n" ++
  "\\definecolor{probeEdge}{HTML}{2E8B57}\n" ++
  "\\definecolor{probeEdgeTwo}{HTML}{8B2E57}\n" ++
  "\\definecolor{probeRed}{HTML}{B22222}\n" ++
  "\\definecolor{probeBlue}{HTML}{1E40AF}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setbeamercolor{probe edge}{fg=probeEdgeTwo,bg=probeEdge}\n" ++
  "\\setbeamercolor{probe fgonly}{fg=probeRed}\n" ++
  "\\setbeamercolor{probe bgonly}{bg=probeBlue}\n" ++
  "\\makeatletter\n" ++
  "\\newbox\\probe@box\n" ++
  "\\setbeamertemplate{block begin}{%\n" ++
  "  \\par\\vskip\\medskipamount\n" ++
  "  \\ifx\\insertblocktitle\\@empty\\else\n" ++
  "    \\setbox\\probe@box\\vbox{\\hsize\\linewidth\n" ++
  "      \\usebeamerfont*{block title}\\usebeamercolor[fg]{block title}%\n" ++
  "      \\strut\\insertblocktitle\\strut\\par}%\n" ++
  "    \\noindent\\llap{{\\usebeamercolor{probe edge}\\usebeamercolor{probe fgonly}\\color{bg}%\n" ++
  "        \\vrule width 1.2pt height \\ht\\probe@box depth \\dp\\probe@box}\\hskip 2pt}%\n" ++
  "    \\box\\probe@box\\par\\nobreak\n" ++
  "  \\fi\n" ++
  "  \\usebeamerfont{block body}\\usebeamercolor[fg]{block body}}\n" ++
  "\\setbeamertemplate{block end}{\\par\\vskip\\smallskipamount}\n" ++
  "\\setbeamertemplate{block alerted begin}{%\n" ++
  "  \\par\\vskip\\medskipamount\n" ++
  "  \\ifx\\insertblocktitle\\@empty\\else\n" ++
  "    \\setbox\\probe@box\\vbox{\\hsize\\linewidth\n" ++
  "      \\usebeamerfont*{block title alerted}\\usebeamercolor[fg]{block title alerted}%\n" ++
  "      \\strut\\insertblocktitle\\strut\\par}%\n" ++
  "    \\noindent\\llap{{\\usebeamercolor{probe edge}\\usebeamercolor{probe bgonly}\\color{fg}%\n" ++
  "        \\vrule width 1.4pt height \\ht\\probe@box depth \\dp\\probe@box}\\hskip 2pt}%\n" ++
  "    \\box\\probe@box\\par\\nobreak\n" ++
  "  \\fi\n" ++
  "  \\usebeamerfont{block body alerted}\\usebeamercolor[fg]{block body alerted}}\n" ++
  "\\setbeamertemplate{block alerted end}{\\par\\vskip\\smallskipamount}\n" ++
  "\\setbeamertemplate{block example begin}{%\n" ++
  "  \\par\\vskip\\medskipamount\n" ++
  "  \\ifx\\insertblocktitle\\@empty\\else\n" ++
  "    \\setbox\\probe@box\\vbox{\\hsize\\linewidth\n" ++
  "      \\usebeamerfont*{block title example}\\usebeamercolor[fg]{block title example}%\n" ++
  "      \\strut\\insertblocktitle\\strut\\par}%\n" ++
  "    \\noindent\\llap{{\\usebeamercolor{probe edge}\\usebeamercolor[bg]{probe fgonly}%\n" ++
  "        \\vrule width 1.6pt height \\ht\\probe@box depth \\dp\\probe@box}\\hskip 2pt}%\n" ++
  "    \\box\\probe@box\\par\\nobreak\n" ++
  "  \\fi\n" ++
  "  \\usebeamerfont{block body example}\\usebeamercolor[fg]{block body example}}\n" ++
  "\\setbeamertemplate{block example end}{\\par\\vskip\\smallskipamount}\n" ++
  "\\makeatother\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[t]{Chain}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Alpha title words}\n" ++
  "Body words here.\n" ++
  "\\end{block}\n" ++
  "\\begin{alertblock}{Beta title words}\n" ++
  "Third body words.\n" ++
  "\\end{alertblock}\n" ++
  "\\begin{exampleblock}{Gamma title words}\n" ++
  "Fourth body words.\n" ++
  "\\end{exampleblock}\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Chain set}\n" ++
  "\\setbeamercolor{probe fgonly}{bg=probeBlue}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Delta title words}\n" ++
  "Fifth body words.\n" ++
  "\\end{block}\n" ++
  "\\begin{exampleblock}{Epsilon title words}\n" ++
  "Sixth body words.\n" ++
  "\\end{exampleblock}\n" ++
  "\\end{frame}\n" ++
  "\\end{document}\n"

/-- Title fonts declared with `size*`, each its own `\baselineskip`: the
alerted title 13 pt on 17, the example 9 pt on 15; one-line and two-line
titles. -/
def starSizedSource : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n" ++
  "\\usetheme{moloch}\n" ++
  "\\definecolor{probeInk}{HTML}{1F2A44}\n" ++
  "\\definecolor{probeEdge}{HTML}{2E8B57}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setbeamercolor{probe edge}{bg=probeEdge}\n" ++
  "\\setbeamerfont{block title alerted}{size*={13}{17}}\n" ++
  "\\setbeamerfont{block title example}{size*={9}{15}}\n" ++
  "\\makeatletter\n" ++
  "\\newbox\\probe@box\n" ++
  "\\newcommand{\\probe@open}[1]{%\n" ++
  "  \\par\\vskip\\medskipamount\n" ++
  "  \\ifx\\insertblocktitle\\@empty\\else\n" ++
  "    \\setbox\\probe@box\\vbox{\\hsize\\linewidth\n" ++
  "      \\usebeamerfont*{block title#1}\\usebeamercolor[fg]{block title#1}%\n" ++
  "      \\strut\\insertblocktitle\\strut\\par}%\n" ++
  "    \\noindent\\llap{{\\usebeamercolor[bg]{probe edge}%\n" ++
  "        \\vrule width 1.2pt height \\ht\\probe@box depth \\dp\\probe@box}\\hskip 2pt}%\n" ++
  "    \\box\\probe@box\\par\\nobreak\n" ++
  "  \\fi\n" ++
  "  \\usebeamerfont{block body#1}\\usebeamercolor[fg]{block body#1}}\n" ++
  "\\newcommand{\\probe@close}{\\par\\vskip\\smallskipamount}\n" ++
  "\\defbeamertemplate*{block begin}{probe}{\\probe@open{}}\n" ++
  "\\defbeamertemplate*{block end}{probe}{\\probe@close}\n" ++
  "\\defbeamertemplate*{block alerted begin}{probe}{\\probe@open{ alerted}}\n" ++
  "\\defbeamertemplate*{block alerted end}{probe}{\\probe@close}\n" ++
  "\\defbeamertemplate*{block example begin}{probe}{\\probe@open{ example}}\n" ++
  "\\defbeamertemplate*{block example end}{probe}{\\probe@close}\n" ++
  "\\makeatother\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[t]{Star sized}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Alpha title words}\n" ++
  "Body words here.\n" ++
  "\\end{block}\n" ++
  "\\begin{alertblock}{Beta title words}\n" ++
  "Third body words.\n" ++
  "\\end{alertblock}\n" ++
  "\\begin{exampleblock}{Gamma title words}\n" ++
  "Fourth body words.\n" ++
  "\\end{exampleblock}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Star sized wrap}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{alertblock}{First title line\\\\Second title line}\n" ++
  "Fifth body words.\n" ++
  "\\end{alertblock}\n" ++
  "\\begin{exampleblock}{Third title line\\\\Fourth title line}\n" ++
  "Sixth body words.\n" ++
  "\\end{exampleblock}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\end{document}\n"

/-- beamer's default blocks under a `size*` title font, 13 pt on 17. -/
def plainStarSource : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n" ++
  "\\usetheme{moloch}\n" ++
  "\\definecolor{probeInk}{HTML}{1F2A44}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setbeamerfont{block title}{size*={13}{17}}\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[t]{Plain star}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Alpha heading words}\n" ++
  "Body words here.\n" ++
  "\\end{block}\n" ++
  "\\begin{exampleblock}{Gamma heading words}\n" ++
  "Fourth body words.\n" ++
  "\\end{exampleblock}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Plain star wrap}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{First heading line\\\\Second heading line}\n" ++
  "Fifth body words.\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\end{document}\n"

/-- Titles set without a box of their own, each in a group so the body keeps
its own font: unstrutted, so an untitled block sets no title paragraph at
all; strutted at `\large`, so an untitled one sets the struts' line. -/
def plainEmptySource : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n" ++
  "\\usetheme{moloch}\n" ++
  "\\definecolor{probeInk}{HTML}{1F2A44}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setbeamerfont{block title alerted}{size=\\large}\n" ++
  "\\setlength{\\parskip}{2pt}\n" ++
  "\\setbeamertemplate{block begin}{%\n" ++
  "  \\par\\vskip 4pt\n" ++
  "  {\\usebeamerfont*{block title}\\usebeamercolor[fg]{block title}%\n" ++
  "    \\insertblocktitle\\par}%\n" ++
  "  \\vskip 3pt\n" ++
  "  \\usebeamerfont{block body}\\usebeamercolor[fg]{block body}}\n" ++
  "\\setbeamertemplate{block end}{\\par\\vskip 5pt}\n" ++
  "\\setbeamertemplate{block alerted begin}{%\n" ++
  "  \\par\\vskip 4pt\n" ++
  "  {\\usebeamerfont*{block title alerted}\\usebeamercolor[fg]{block title alerted}%\n" ++
  "    \\strut\\insertblocktitle\\strut\\par}%\n" ++
  "  \\vskip 3pt\n" ++
  "  \\usebeamerfont{block body alerted}\\usebeamercolor[fg]{block body alerted}}\n" ++
  "\\setbeamertemplate{block alerted end}{\\par\\vskip 5pt}\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[t]{Plain empty}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Gamma title words}\n" ++
  "Body words here.\n" ++
  "\\end{block}\n" ++
  "\\begin{block}{}\n" ++
  "Untitled plain words.\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Plain strut}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{alertblock}{Delta title words}\n" ++
  "Third body words.\n" ++
  "\\end{alertblock}\n" ++
  "\\begin{alertblock}{}\n" ++
  "Untitled strut words.\n" ++
  "\\end{alertblock}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\end{document}\n"

/-- Rules reaching by their titles' lines, read in the title's font from the
title's box: the plain kind's its box's height and depth less the
`\parskip` its list opens on, less half the leading the capitals leave
(`\baselineskip` less `\fontcharht\font`H`), standing that far below the
last baseline; the example kind's the same at `\large`, its box opening on
its strut, so its rule reaches past the box's top; the alerted kind's on the
right, half a leading deep and a point over the lines above, deeper than the
box. The two-line titles break with `\\`, which beamer sets as a paragraph
per line. The fourth frame's titles stand their lines apart from their
struts: an accented capital's ink above the strut, at the body's size and at
`\large`, and two lines a `\\[3pt]` further apart; the fifth's last lines
stand deeper than their struts, which the rule's reach past the box's top
reads. -/
def capitalsSource : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n" ++
  "\\usetheme{moloch}\n" ++
  "\\definecolor{probeInk}{HTML}{1F2A44}\n" ++
  "\\definecolor{probeEdge}{HTML}{2E8B57}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setbeamercolor{probe edge}{bg=probeEdge}\n" ++
  "\\setbeamerfont{block title example}{size=\\large}\n" ++
  "\\setlength{\\parskip}{4pt}\n" ++
  "\\makeatletter\n" ++
  "\\newbox\\probe@box\n" ++
  "\\newdimen\\probe@down\n" ++
  "\\newcommand{\\probe@open}[1]{%\n" ++
  "  \\par\\vskip\\medskipamount\n" ++
  "  \\ifx\\insertblocktitle\\@empty\\else\n" ++
  "    \\setbox\\probe@box\\vbox{\\hsize\\linewidth\n" ++
  "      \\usebeamerfont*{block title#1}\\usebeamercolor[fg]{block title#1}%\n" ++
  "      \\strut\\insertblocktitle\\strut\\par\n" ++
  "      \\global\\probe@down\\dimexpr(\\baselineskip-\\fontcharht\\font`H)/2\\relax}%\n" ++
  "    \\noindent\\llap{{\\usebeamercolor[bg]{probe edge}%\n" ++
  "        \\vrule width .3em\n" ++
  "          height \\dimexpr\\ht\\probe@box+\\dp\\probe@box-\\parskip-\\probe@down\\relax\n" ++
  "          depth \\probe@down}%\n" ++
  "      \\hskip .6em}%\n" ++
  "    \\box\\probe@box\\par\\nobreak\n" ++
  "  \\fi\n" ++
  "  \\usebeamerfont{block body#1}\\usebeamercolor[fg]{block body#1}}\n" ++
  "\\newcommand{\\probe@close}{\\par\\vskip\\smallskipamount}\n" ++
  "\\defbeamertemplate*{block begin}{probe}{\\probe@open{}}\n" ++
  "\\defbeamertemplate*{block end}{probe}{\\probe@close}\n" ++
  "\\defbeamertemplate*{block example begin}{probe}{%\n" ++
  "  \\par\\vskip\\medskipamount\n" ++
  "  \\ifx\\insertblocktitle\\@empty\\else\n" ++
  "    \\setbox\\probe@box\\vbox{\\hsize\\linewidth\n" ++
  "      \\usebeamerfont*{block title example}\\strut\\usebeamercolor[fg]{block title example}%\n" ++
  "      \\insertblocktitle\\strut\\par\n" ++
  "      \\global\\probe@down\\dimexpr(\\baselineskip-\\fontcharht\\font`H)/2\\relax}%\n" ++
  "    \\noindent\\llap{{\\usebeamercolor[bg]{probe edge}%\n" ++
  "        \\vrule width .3em height \\dimexpr\\ht\\probe@box+\\dp\\probe@box-\\probe@down\\relax\n" ++
  "          depth \\probe@down}%\n" ++
  "      \\hskip .6em}%\n" ++
  "    \\box\\probe@box\\par\\nobreak\n" ++
  "  \\fi\n" ++
  "  \\usebeamerfont{block body example}\\usebeamercolor[fg]{block body example}}\n" ++
  "\\defbeamertemplate*{block example end}{probe}{\\probe@close}\n" ++
  "\\defbeamertemplate*{block alerted begin}{probe}{%\n" ++
  "  \\par\\vskip\\medskipamount\n" ++
  "  \\ifx\\insertblocktitle\\@empty\\else\n" ++
  "    \\setbox\\probe@box\\vbox{\\hsize\\linewidth\n" ++
  "      \\usebeamerfont*{block title alerted}\\usebeamercolor[fg]{block title alerted}%\n" ++
  "      \\strut\\insertblocktitle\\strut\\par\n" ++
  "      \\global\\probe@down\\dimexpr\\baselineskip/2\\relax}%\n" ++
  "    \\noindent\\copy\\probe@box\n" ++
  "    \\rlap{\\hskip 4pt{\\usebeamercolor[fg]{alerted text}%\n" ++
  "        \\vrule width 3pt\n" ++
  "          height \\dimexpr\\dp\\probe@box+\\ht\\probe@box-\\parskip-\\probe@down+1pt\\relax\n" ++
  "          depth \\probe@down}}%\n" ++
  "    \\par\\nobreak\n" ++
  "  \\fi\n" ++
  "  \\usebeamerfont{block body alerted}\\usebeamercolor[fg]{block body alerted}}\n" ++
  "\\defbeamertemplate*{block alerted end}{probe}{\\probe@close}\n" ++
  "\\makeatother\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[t]{Capitals}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Alpha title words}\n" ++
  "Body words here.\n" ++
  "\\end{block}\n" ++
  "\\begin{block}{Delta first title line\\\\Delta second title line}\n" ++
  "Second body words.\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Sizes}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{exampleblock}{Gamma title words}\n" ++
  "Third body words.\n" ++
  "\\end{exampleblock}\n" ++
  "\\begin{exampleblock}{Epsilon first title line\\\\Epsilon second title line}\n" ++
  "Fourth body words.\n" ++
  "\\end{exampleblock}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Right}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{alertblock}{Beta title words}\n" ++
  "Fifth body words.\n" ++
  "\\end{alertblock}\n" ++
  "\\begin{block}{}\n" ++
  "Untitled body words.\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Accents}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Élan Über words}\n" ++
  "Sixth body words.\n" ++
  "\\end{block}\n" ++
  "\\begin{block}{Zeta first title line\\\\[3pt]Zeta second title line}\n" ++
  "Seventh body words.\n" ++
  "\\end{block}\n" ++
  "\\begin{exampleblock}{Écart title words}\n" ++
  "Eighth body words.\n" ++
  "\\end{exampleblock}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Depths}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Kappa title words\\rule[-6pt]{0pt}{7pt}}\n" ++
  "Ninth body words.\n" ++
  "\\end{block}\n" ++
  "\\begin{exampleblock}{Lambda title words\\rule[-6pt]{0pt}{7pt}}\n" ++
  "Tenth body words.\n" ++
  "\\end{exampleblock}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\end{document}\n"

private def edgeColor : Ir.Color := { r := 0x2E, g := 0x8B, b := 0x57 }

private def edgeTwoColor : Ir.Color := { r := 0x8B, g := 0x2E, b := 0x57 }

/-- The moloch bundle's alerted ink, the right-hand rule's colour. -/
private def alertColor : Ir.Color :=
  (((Theme.find? "moloch").map (·.realize .decks)).bind (·.find? "alert")).getD Ir.Color.black

/-- A mark on a shipped page: a line's baseline or left edge, by its letters;
the `n`th rule of a colour down the page, its top, bottom, left or right; the
text block's left and right edges. -/
private inductive Mark where
  | base (text : String)
  | lineX (text : String)
  | top (c : Ir.Color) (n : Nat)
  | bottom (c : Ir.Color) (n : Nat)
  | left (c : Ir.Color) (n : Nat)
  | right (c : Ir.Color) (n : Nat)
  | edge
  | rightEdge

/-- lualatex's distances from the first mark to the second, in thousandths
of a TeX point, per probe and page. -/
private def measured : Array (String × Nat × Mark × Mark × Int) := #[
  -- The title's box: medskip, the line's `\parskip`, `\lineskip`, then the
  -- box's own `\parskip` and the strut above the baseline.
  ("hanging", 0, .base "Lead paragraph above.", .base "Alpha title words", 25802),
  ("hanging", 0, .top edgeColor 0, .base "Alpha title words", 12400),
  ("hanging", 0, .top edgeColor 0, .bottom edgeColor 0, 16000),
  ("hanging", 0, .base "Alpha title words", .base "Body words here.", 19000),
  ("hanging", 0, .base "Body words here.", .base "Second body paragraph.", 16000),
  ("hanging", 0, .base "Second body paragraph.", .base "Trailing paragraph below.", 19000),
  ("hanging", 1, .base "Lead paragraph above.", .base "Beta title words", 25802),
  ("hanging", 1, .top alertColor 0, .base "Beta title words", 12400),
  ("hanging", 1, .top alertColor 0, .bottom alertColor 0, 16000),
  ("hanging", 1, .base "Beta title words", .base "Third body words.", 16000),
  -- The untitled block sets no title box, its addition still standing.
  ("hanging", 1, .base "Third body words.", .base "Untitled body words.", 28000),
  ("hanging", 1, .base "Untitled body words.", .base "Trailing paragraph below.", 19000),
  ("hanging", 2, .top edgeColor 0, .base "Gamma title words", 12400),
  ("hanging", 2, .base "Gamma title words", .base "Fourth body words.", 16000),
  ("hanging", 2, .base "Fourth body words.",
    .base "A very long block title that certainly wraps onto a second line", 28802),
  ("hanging", 2, .top edgeColor 1,
    .base "A very long block title that certainly wraps onto a second line", 12400),
  ("hanging", 2, .top edgeColor 1, .bottom edgeColor 1, 28000),
  ("hanging", 2, .base "of text because it keeps going and going", .base "Fifth body words.", 19000),
  -- The box holding title and body: its top the title's, its bottom the
  -- body's last line's depth; untitled, the body's colour change stands first.
  ("whole", 0, .base "Lead paragraph above.", .base "Alpha title words", 25802),
  ("whole", 0, .top edgeColor 0, .base "Alpha title words", 12400),
  ("whole", 0, .top edgeColor 0, .bottom edgeColor 0, 46802),
  ("whole", 0, .base "Second body paragraph.", .base "Trailing paragraph below.", 19000),
  ("whole", 1, .base "Lead paragraph above.", .base "Untitled body words.", 25000),
  ("whole", 1, .top edgeColor 0, .base "Untitled body words.", 11598),
  ("whole", 1, .top edgeColor 0, .bottom edgeColor 0, 14000),
  ("whole", 1, .base "Untitled body words.", .base "One untitled line.", 28000),
  ("whole", 1, .top edgeColor 1, .base "One untitled line.", 11598),
  ("whole", 1, .top edgeColor 1, .bottom edgeColor 1, 30000),
  ("whole", 1, .base "One untitled line.", .base "And another paragraph.", 16000),
  ("whole", 1, .base "And another paragraph.", .base "Trailing paragraph below.", 19000),
  -- Inside the line, no `\parskip`: a one-line title box takes the baseline
  -- skip, a two-line one `\lineskip`; the earlier addition is gone.
  ("inside", 0, .base "Lead paragraph above.", .base "Alpha title words", 18000),
  ("inside", 0, .top edgeColor 0, .base "Alpha title words", 8400),
  ("inside", 0, .top edgeColor 0, .bottom edgeColor 0, 12000),
  ("inside", 0, .base "Alpha title words", .base "Body words here.", 12000),
  ("inside", 0, .base "Second body paragraph.", .base "Trailing paragraph below.", 15000),
  ("inside", 1, .base "Lead paragraph above.",
    .base "A very long block title that certainly wraps onto a second line", 17802),
  ("inside", 1, .top edgeColor 0,
    .base "A very long block title that certainly wraps onto a second line", 8400),
  ("inside", 1, .top edgeColor 0, .bottom edgeColor 0, 24000),
  ("inside", 1, .base "of text because it keeps going and going", .base "Fourth body words.", 12000),
  -- Each arm's own skips: the title's `4pt` only after the title's box, the
  -- untitled arm's `5pt` only where the title is empty; inside the box
  -- holding title and body, the untitled arm's `3pt` stands in the box,
  -- whose height the interline rule reads.
  ("armed", 0, .base "Lead paragraph above.", .base "Alpha title words", 23802),
  ("armed", 0, .top edgeColor 0, .base "Alpha title words", 11400),
  ("armed", 0, .top edgeColor 0, .bottom edgeColor 0, 15000),
  ("armed", 0, .base "Alpha title words", .base "Body words here.", 19000),
  ("armed", 0, .base "Body words here.", .base "Middle paragraph here.", 18000),
  ("armed", 0, .base "Middle paragraph here.", .base "Untitled body words.", 26000),
  ("armed", 0, .base "Untitled body words.", .base "Trailing paragraph below.", 18000),
  ("armed", 1, .base "Lead paragraph above.", .base "Beta title words", 29802),
  ("armed", 1, .top edgeColor 0, .base "Beta title words", 11400),
  ("armed", 1, .top edgeColor 0, .bottom edgeColor 0, 45802),
  ("armed", 1, .base "Beta title words", .base "Third body words.", 17000),
  ("armed", 1, .base "Third body words.", .base "Second body paragraph.", 15000),
  ("armed", 1, .base "Second body paragraph.", .base "Middle paragraph here.", 18000),
  ("armed", 1, .base "Middle paragraph here.", .base "Untitled whole words.", 32000),
  ("armed", 1, .top edgeColor 1, .base "Untitled whole words.", 13598),
  ("armed", 1, .top edgeColor 1, .bottom edgeColor 1, 13739),
  ("armed", 1, .base "Untitled whole words.", .base "Trailing paragraph below.", 18000),
  -- The title's box kept empty: the struts' line, and both rules beside it
  -- as tall as the box; unstrutted, the empty box is a line of no height
  -- that draws no rule.
  ("boxed", 0, .base "Lead paragraph above.", .base "Gamma title words", 19802),
  ("boxed", 0, .top edgeTwoColor 0, .base "Gamma title words", 10400),
  ("boxed", 0, .top edgeTwoColor 0, .bottom edgeTwoColor 0, 14000),
  ("boxed", 0, .top edgeColor 0, .bottom edgeColor 0, 14000),
  ("boxed", 0, .base "Gamma title words", .base "Body words here.", 17000),
  ("boxed", 0, .base "Body words here.", .base "Untitled boxed words.", 41802),
  ("boxed", 0, .top edgeTwoColor 1, .base "Untitled boxed words.", 27400),
  ("boxed", 0, .top edgeTwoColor 1, .bottom edgeTwoColor 1, 14000),
  ("boxed", 0, .top edgeColor 1, .bottom edgeColor 1, 14000),
  ("boxed", 0, .base "Untitled boxed words.", .base "Trailing paragraph below.", 19000),
  ("boxed", 1, .base "Lead paragraph above.", .base "Delta title words", 18000),
  ("boxed", 1, .top edgeColor 0, .base "Delta title words", 9598),
  ("boxed", 1, .top edgeColor 0, .bottom edgeColor 0, 9695),
  ("boxed", 1, .base "Delta title words", .base "Third body words.", 17000),
  ("boxed", 1, .base "Third body words.", .base "Untitled bare words.", 40000),
  ("boxed", 1, .base "Untitled bare words.", .base "Trailing paragraph below.", 19000),
  -- The title's `\strut` reads its own font's `\baselineskip` (14, 10 and
  -- 11 pt), and its lines stand that far apart.
  ("sized", 0, .base "Lead paragraph above.", .base "Alpha title words", 19202),
  ("sized", 0, .top edgeColor 0, .base "Alpha title words", 9800),
  ("sized", 0, .top edgeColor 0, .bottom edgeColor 0, 14000),
  ("sized", 0, .base "Alpha title words", .base "Body words here.", 12000),
  ("sized", 0, .base "Body words here.", .base "Beta title words", 21000),
  ("sized", 0, .top edgeColor 1, .base "Beta title words", 8400),
  ("sized", 0, .top edgeColor 1, .bottom edgeColor 1, 12000),
  ("sized", 0, .base "Beta title words", .base "Third body words.", 12000),
  ("sized", 0, .base "Third body words.", .base "Gamma title words", 21000),
  ("sized", 0, .top edgeColor 2, .base "Gamma title words", 7700),
  ("sized", 0, .top edgeColor 2, .bottom edgeColor 2, 11000),
  ("sized", 0, .base "Gamma title words", .base "Fourth body words.", 12000),
  ("sized", 0, .base "Fourth body words.", .base "Trailing paragraph below.", 15000),
  ("sized", 1, .base "Lead paragraph above.", .base "First title line", 19202),
  ("sized", 1, .top edgeColor 0, .base "First title line", 9800),
  ("sized", 1, .top edgeColor 0, .bottom edgeColor 0, 28000),
  ("sized", 1, .base "First title line", .base "Second title line", 14000),
  ("sized", 1, .base "Second title line", .base "Fifth body words.", 12000),
  ("sized", 1, .base "Fifth body words.", .base "Third title line", 20102),
  ("sized", 1, .top edgeColor 1, .base "Third title line", 7700),
  ("sized", 1, .top edgeColor 1, .bottom edgeColor 1, 22000),
  ("sized", 1, .base "Third title line", .base "Fourth title line", 11000),
  ("sized", 1, .base "Fourth title line", .base "Sixth body words.", 12000),
  ("sized", 1, .base "Sixth body words.", .base "Trailing paragraph below.", 15000),
  -- beamer's default title box under a declared size: placed by the page's
  -- interline rule from its height, its lines its font's `\baselineskip`
  -- apart; the alerted title keeps moloch's own size.
  ("plainsized", 0, .base "Lead paragraph above.", .base "Alpha heading words", 18000),
  ("plainsized", 0, .base "Alpha heading words", .base "Body words here.", 14545),
  ("plainsized", 0, .base "Body words here.", .base "Beta heading words", 21000),
  ("plainsized", 0, .base "Beta heading words", .base "Third body words.", 14064),
  ("plainsized", 0, .base "Third body words.", .base "Gamma heading words", 21000),
  ("plainsized", 0, .base "Gamma heading words", .base "Fourth body words.", 14545),
  ("plainsized", 0, .base "Fourth body words.", .base "Trailing paragraph below.", 15000),
  ("plainsized", 1, .base "Lead paragraph above.", .base "First heading line", 18520),
  ("plainsized", 1, .base "First heading line", .base "Second heading line", 14000),
  ("plainsized", 1, .base "Second heading line", .base "Fifth body words.", 14545),
  ("plainsized", 1, .base "Fifth body words.", .base "Trailing paragraph below.", 15000),
  -- An empty title box under a declared size: the struts' line at its own
  -- font's `\baselineskip` and the box's `\parskip`, the rules as tall; an
  -- unstrutted box holds no paragraph and draws no rule.
  ("emptybox", 0, .base "Lead paragraph above.", .base "Gamma title words", 21202),
  ("emptybox", 0, .top edgeTwoColor 0, .base "Gamma title words", 11800),
  ("emptybox", 0, .top edgeTwoColor 0, .bottom edgeTwoColor 0, 16000),
  ("emptybox", 0, .top edgeColor 0, .bottom edgeColor 0, 16000),
  ("emptybox", 0, .base "Gamma title words", .base "Body words here.", 17000),
  ("emptybox", 0, .base "Body words here.", .base "Untitled boxed words.", 43202),
  ("emptybox", 0, .top edgeTwoColor 1, .base "Untitled boxed words.", 28800),
  ("emptybox", 0, .top edgeTwoColor 1, .bottom edgeTwoColor 1, 16000),
  ("emptybox", 0, .top edgeColor 1, .bottom edgeColor 1, 16000),
  ("emptybox", 0, .base "Untitled boxed words.", .base "Trailing paragraph below.", 19000),
  ("emptybox", 1, .base "Lead paragraph above.", .base "Delta title words", 18000),
  ("emptybox", 1, .top edgeColor 0, .base "Delta title words", 9598),
  ("emptybox", 1, .top edgeColor 0, .bottom edgeColor 0, 9695),
  ("emptybox", 1, .base "Delta title words", .base "Third body words.", 17000),
  ("emptybox", 1, .base "Third body words.", .base "Untitled bare words.", 40000),
  ("emptybox", 1, .base "Untitled bare words.", .base "Trailing paragraph below.", 19000),
  ("emptybox", 2, .base "Lead paragraph above.", .base "Epsilon title words", 19102),
  ("emptybox", 2, .top edgeColor 0, .base "Epsilon title words", 9700),
  ("emptybox", 2, .top edgeColor 0, .bottom edgeColor 0, 13000),
  ("emptybox", 2, .base "Epsilon title words", .base "Fifth body words.", 17000),
  ("emptybox", 2, .base "Fifth body words.", .base "Untitled small words.", 41102),
  ("emptybox", 2, .top edgeColor 1, .base "Untitled small words.", 26700),
  ("emptybox", 2, .top edgeColor 1, .bottom edgeColor 1, 13000),
  ("emptybox", 2, .base "Untitled small words.", .base "Trailing paragraph below.", 19000),
  -- `size*` titles stand their declared `\baselineskip`: the strut, the
  -- lines of a two-line title, and the depth what follows is spaced from.
  ("starsized", 0, .base "Lead paragraph above.", .base "Alpha title words", 18000),
  ("starsized", 0, .top edgeColor 0, .base "Alpha title words", 8400),
  ("starsized", 0, .top edgeColor 0, .bottom edgeColor 0, 12000),
  ("starsized", 0, .base "Alpha title words", .base "Body words here.", 12000),
  ("starsized", 0, .base "Body words here.", .base "Beta title words", 24302),
  ("starsized", 0, .top edgeColor 1, .base "Beta title words", 11900),
  ("starsized", 0, .top edgeColor 1, .bottom edgeColor 1, 17000),
  ("starsized", 0, .base "Beta title words", .base "Third body words.", 13698),
  ("starsized", 0, .base "Third body words.", .base "Gamma title words", 22902),
  ("starsized", 0, .top edgeColor 2, .base "Gamma title words", 10500),
  ("starsized", 0, .top edgeColor 2, .bottom edgeColor 2, 15000),
  ("starsized", 0, .base "Gamma title words", .base "Fourth body words.", 13098),
  ("starsized", 0, .base "Fourth body words.", .base "Trailing paragraph below.", 15000),
  ("starsized", 1, .base "Lead paragraph above.", .base "First title line", 21302),
  ("starsized", 1, .top edgeColor 0, .base "First title line", 11900),
  ("starsized", 1, .top edgeColor 0, .bottom edgeColor 0, 34000),
  ("starsized", 1, .base "First title line", .base "Second title line", 17000),
  ("starsized", 1, .base "Second title line", .base "Fifth body words.", 13751),
  ("starsized", 1, .base "Fifth body words.", .base "Third title line", 22902),
  ("starsized", 1, .top edgeColor 1, .base "Third title line", 10500),
  ("starsized", 1, .top edgeColor 1, .bottom edgeColor 1, 30000),
  ("starsized", 1, .base "Third title line", .base "Fourth title line", 15000),
  ("starsized", 1, .base "Fourth title line", .base "Sixth body words.", 13098),
  ("starsized", 1, .base "Sixth body words.", .base "Trailing paragraph below.", 15000),
  -- A title with no box is a paragraph of the block's list, placed by the
  -- interline rule under its font's `\baselineskip`; empty and unstrutted
  -- it is no paragraph at all.
  ("plainempty", 0, .base "Lead paragraph above.", .base "Gamma title words", 18000),
  ("plainempty", 0, .base "Gamma title words", .base "Body words here.", 17000),
  ("plainempty", 0, .base "Body words here.", .base "Untitled plain words.", 26000),
  ("plainempty", 0, .base "Untitled plain words.", .base "Trailing paragraph below.", 19000),
  ("plainempty", 1, .base "Lead paragraph above.", .base "Delta title words", 20000),
  ("plainempty", 1, .base "Delta title words", .base "Third body words.", 17000),
  ("plainempty", 1, .base "Third body words.", .base "Untitled strut words.", 42000),
  ("plainempty", 1, .base "Untitled strut words.", .base "Trailing paragraph below.", 19000),
  ("plainstar", 0, .base "Lead paragraph above.", .base "Alpha heading words", 19279),
  ("plainstar", 0, .base "Alpha heading words", .base "Body words here.", 14785),
  ("plainstar", 0, .base "Body words here.", .base "Gamma heading words", 22279),
  ("plainstar", 0, .base "Gamma heading words", .base "Fourth body words.", 14785),
  ("plainstar", 0, .base "Fourth body words.", .base "Trailing paragraph below.", 15000),
  ("plainstar", 1, .base "Lead paragraph above.", .base "First heading line", 19279),
  ("plainstar", 1, .base "First heading line", .base "Second heading line", 17000),
  ("plainstar", 1, .base "Second heading line", .base "Fifth body words.", 14785),
  ("plainstar", 1, .base "Fifth body words.", .base "Trailing paragraph below.", 15000),
  -- A rule reaching by the title's lines: half a leading and half a cap
  -- height past the capitals' span, one leading per line; the large title's
  -- rule reaches past its box, which its line then stands below; the
  -- alerted rule half a leading deep, which the body is then spaced from.
  ("capitals", 0, .base "Lead paragraph above.", .base "Alpha title words", 25802),
  ("capitals", 0, .top edgeColor 0, .base "Alpha title words", 9569),
  ("capitals", 0, .top edgeColor 0, .bottom edgeColor 0, 12000),
  ("capitals", 0, .base "Alpha title words", .base "Body words here.", 16000),
  ("capitals", 0, .base "Body words here.",
    .base "Delta first title line", 28802),
  ("capitals", 0, .top edgeColor 1,
    .base "Delta first title line", 9569),
  ("capitals", 0, .top edgeColor 1, .bottom edgeColor 1, 24000),
  ("capitals", 0, .base "Delta first title line",
    .base "Delta second title line", 12000),
  ("capitals", 0, .base "Delta second title line", .base "Second body words.", 16000),
  ("capitals", 0, .base "Second body words.", .base "Trailing paragraph below.", 19000),
  ("capitals", 1, .base "Lead paragraph above.", .base "Gamma title words", 24686),
  ("capitals", 1, .top edgeColor 0, .base "Gamma title words", 11283),
  ("capitals", 1, .top edgeColor 0, .bottom edgeColor 0, 14000),
  ("capitals", 1, .base "Gamma title words", .base "Third body words.", 16000),
  ("capitals", 1, .base "Third body words.",
    .base "Epsilon first title line", 27686),
  ("capitals", 1, .top edgeColor 1,
    .base "Epsilon first title line", 11283),
  ("capitals", 1, .top edgeColor 1, .bottom edgeColor 1, 28000),
  ("capitals", 1, .base "Epsilon first title line",
    .base "Epsilon second title line", 14000),
  ("capitals", 1, .base "Epsilon second title line", .base "Fourth body words.", 16000),
  ("capitals", 1, .base "Fourth body words.", .base "Trailing paragraph below.", 19000),
  ("capitals", 2, .base "Lead paragraph above.", .base "Beta title words", 25802),
  ("capitals", 2, .top alertColor 0, .base "Beta title words", 7000),
  ("capitals", 2, .top alertColor 0, .bottom alertColor 0, 13000),
  ("capitals", 2, .base "Beta title words", .base "Fifth body words.", 18651),
  ("capitals", 2, .base "Fifth body words.", .base "Untitled body words.", 25000),
  ("capitals", 2, .base "Untitled body words.", .base "Trailing paragraph below.", 19000),
  -- Lines standing apart from their struts: an accent's ink above the strut
  -- makes the box and its rule that much taller above, the large title's
  -- box so much taller that its line stands lower again; a skip between two
  -- lines lengthens the rule by itself.
  ("capitals", 3, .base "Lead paragraph above.", .base "Élan Über words", 26714),
  ("capitals", 3, .top edgeColor 0, .base "Élan Über words", 10481),
  ("capitals", 3, .top edgeColor 0, .bottom edgeColor 0, 12912),
  ("capitals", 3, .base "Élan Über words", .base "Sixth body words.", 16000),
  ("capitals", 3, .base "Sixth body words.", .base "Zeta first title line", 28802),
  ("capitals", 3, .top edgeColor 1, .base "Zeta first title line", 9569),
  ("capitals", 3, .top edgeColor 1, .bottom edgeColor 1, 27000),
  ("capitals", 3, .base "Zeta first title line", .base "Zeta second title line", 15000),
  ("capitals", 3, .base "Zeta second title line", .base "Seventh body words.", 16000),
  ("capitals", 3, .base "Seventh body words.", .base "Écart title words", 29059),
  ("capitals", 3, .top edgeColor 2, .base "Écart title words", 12657),
  ("capitals", 3, .top edgeColor 2, .bottom edgeColor 2, 15374),
  ("capitals", 3, .base "Écart title words", .base "Eighth body words.", 16000),
  ("capitals", 3, .base "Eighth body words.", .base "Trailing paragraph below.", 19000),
  ("capitals", 4, .base "Lead paragraph above.", .base "Kappa title words", 25802),
  ("capitals", 4, .top edgeColor 0, .base "Kappa title words", 11969),
  ("capitals", 4, .top edgeColor 0, .bottom edgeColor 0, 14400),
  ("capitals", 4, .base "Kappa title words", .base "Ninth body words.", 18598),
  ("capitals", 4, .base "Ninth body words.", .base "Lambda title words", 29486),
  ("capitals", 4, .top edgeColor 1, .base "Lambda title words", 13083),
  ("capitals", 4, .top edgeColor 1, .bottom edgeColor 1, 15800),
  ("capitals", 4, .base "Lambda title words", .base "Tenth body words.", 18598),
  ("capitals", 4, .base "Tenth body words.", .base "Trailing paragraph below.", 19000)]

/-- lualatex's horizontal distances, the same way. -/
private def measuredX : Array (String × Nat × Mark × Mark × Int) := #[
  ("hanging", 0, .left edgeColor 0, .edge, 9000),
  ("hanging", 0, .left edgeColor 0, .right edgeColor 0, 3000),
  ("hanging", 0, .edge, .lineX "Alpha title words", 0),
  ("hanging", 1, .rightEdge, .left alertColor 0, 4000),
  ("hanging", 1, .left alertColor 0, .right alertColor 0, 3000),
  ("whole", 0, .left edgeColor 0, .edge, 7500),
  ("whole", 0, .left edgeColor 0, .right edgeColor 0, 2500),
  ("whole", 0, .edge, .lineX "Body words here.", 0),
  ("inside", 0, .edge, .left edgeColor 0, 0),
  ("inside", 0, .left edgeColor 0, .right edgeColor 0, 2000),
  ("inside", 0, .edge, .lineX "Alpha title words", 7000),
  ("inside", 0, .edge, .lineX "Body words here.", 0),
  ("armed", 1, .rightEdge, .left edgeColor 0, 4000),
  ("armed", 1, .left edgeColor 0, .right edgeColor 0, 1000),
  ("armed", 0, .left edgeColor 0, .edge, 3200),
  ("armed", 0, .left edgeColor 0, .right edgeColor 0, 1200),
  ("boxed", 0, .edge, .left edgeTwoColor 0, 0),
  ("boxed", 0, .left edgeTwoColor 0, .right edgeTwoColor 0, 1500),
  ("boxed", 0, .edge, .lineX "Gamma title words", 3000),
  ("boxed", 0, .rightEdge, .right edgeColor 0, 0),
  ("boxed", 0, .left edgeColor 0, .right edgeColor 0, 2000),
  ("boxed", 1, .rightEdge, .right edgeColor 0, 0),
  ("boxed", 1, .edge, .lineX "Delta title words", 0),
  ("capitals", 0, .left edgeColor 0, .edge, 9000),
  ("capitals", 0, .left edgeColor 0, .right edgeColor 0, 3000),
  ("capitals", 2, .rightEdge, .left alertColor 0, 4000),
  ("capitals", 2, .left alertColor 0, .right alertColor 0, 3000)]

/-- Word spaces ship as gaps, not glyphs: a line is found by its letters. -/
private def letters (text : String) : String := text.replace " " ""

private def ruleOf (page : Layout.PageOut) (c : Ir.Color) (n : Nat) : Option Layout.Fill :=
  ((page.fills.filter (·.color == c)).qsort (·.y < ·.y))[n]?

private def lineOf (page : Layout.PageOut) (text : String) : Option Layout.LineOut :=
  page.lines.find? fun l => !l.furniture && lineText l false == letters text

private def markAt (geom : Layout.Geom) (page : Layout.PageOut) : Mark → Option Dim.Sp
  | .base t => (lineOf page t).map (·.y)
  | .lineX t => (lineOf page t).map (·.x)
  | .top c n => (ruleOf page c n).map (·.y)
  | .bottom c n => (ruleOf page c n).map fun f => f.y + f.h
  | .left c n => (ruleOf page c n).map (·.x)
  | .right c n => (ruleOf page c n).map fun f => f.x + f.w
  | .edge => some geom.hmargin
  | .rightEdge => some (geom.hmargin + geom.textWidth)

private def milliOf (d : Dim.Sp) : Int := (d * 1000 + 32768) / 65536

/-- 2 thousandths of a point: the walk's four-decimal TeX points, rounded
here to thousandths. -/
private def tolerance : Int := 2

private def sources : List (String × String) :=
  [("hanging", hanging), ("whole", whole), ("inside", inside), ("armed", armedSource),
   ("boxed", boxedSource), ("sized", sizedSource), ("plainsized", plainSizedSource),
   ("emptybox", emptyBoxSource), ("starsized", starSizedSource), ("plainstar", plainStarSource),
   ("plainempty", plainEmptySource), ("capitals", capitalsSource)]

private def layout (fonts : Font.FontSet) (name src : String) : Layout.Geom × Layout.Out × Array Diag :=
  let (doc, diags) := Elab.run s!"block-template-{name}.tex" src
  let geom := Layout.Geom.ofPage doc.page
  (geom, Layout.run geom fonts none doc, diags)

/-- The shipped pages hold each rule where lualatex draws it, the template's
lists spaced as TeX spaces them, and nothing else painted: no colour box. -/
private def pageChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  for (name, src) in sources do
    let (geom, out, diags) := layout fonts name src
    check ref s!"block template {name}: the probe reads without loss"
      ((diags ++ out.diags).all (·.severity == .note))
    let rows := measured ++ measuredX
    for (probe, page, a, b, want) in rows do
      unless probe == name do continue
      match out.pages[page]?.bind fun p => (markAt geom p a).bind fun ya => (markAt geom p b).map (· - ya) with
      | some d =>
        check ref s!"block template {name} page {page}: {want} (lualatex) got {milliOf d}"
          ((milliOf d - want).natAbs ≤ tolerance.toNat)
      | none => check ref s!"block template {name} page {page}: the marks for {want} ship" false
    -- Paint is the rules alone: a page's ground, the frame title's bar,
    -- and one fill per rule beside a box.
    let edge (f : Layout.Fill) : Bool :=
      f.color == edgeColor || f.color == alertColor || f.color == edgeTwoColor
    let rules := out.pages.map fun p => (p.fills.filter edge).size
    let want : Array Nat := match name with
      | "hanging" => #[1, 1, 2]
      | "whole" => #[1, 2]
      | "armed" => #[1, 2]
      | "boxed" => #[4, 1]
      | "sized" => #[3, 2]
      | "plainsized" => #[0, 0]
      | "emptybox" => #[4, 1, 2]
      | "starsized" => #[3, 2]
      | "plainstar" => #[0, 0]
      | "plainempty" => #[0, 0]
      | "capitals" => #[2, 2, 1, 3, 2]
      | _ => #[1, 1]
    check ref s!"block template {name}: one rule per box that has one ({rules})" (rules == want)
    check ref s!"block template {name}: no colour box is painted"
      (out.pages.all fun p => p.fills.all fun f => edge f || f.x == 0)

/-- A rule after `\box` reads the box's emptied register: TeX draws it with
no height, so nothing ships; after `\copy` the box is still there. -/
private def voidedChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let voided := hanging.replace "\\noindent\\copy\\probe@box" "\\noindent\\box\\probe@box"
  check ref "block template: the voided probe differs from the probe" (voided != hanging)
  let (_, out, _) := layout fonts "voided" voided
  check ref "block template: a rule reading an emptied box ships nothing"
    ((out.pages[1]?.map fun p => (p.fills.filter (·.color == alertColor)).size) == some 0)

/-- The children of every shaped block section, in tree order. -/
private def shapedSections (body : Array Html.Node) : Array (Array Html.Node) :=
  (elemNodesList (· == "section") #[] body.toList).filterMap fun n => match n with
    | .elem _ attrs kids =>
      if attrs.any (fun (k, v) => k == "class" && hasStr v "block-shaped") then some kids else none
    | .text _ | .style _ | .script .. => none

/-- The typed HTML tree sets each templated block as its section with no
colour box, an untitled block whose template tests the title with no
header, and the stylesheet draws each rule beside its box from the declared
values: the hanging title rule `.3em` wide and `.6em` out, in the palette
entry the template's colour element paints. -/
private def htmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let (doc, _) := Elab.run "block-template-hanging.tex" hanging
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let sheet := treeCssList "" (head.toList ++ body.toList)
  let sections := (elemAttrsList (· == "section") #[] body.toList).filter fun (_, attrs) =>
    attrs.any fun (k, v) => k == "class" && hasStr v "block"
  check ref "block template HTML: every templated block is a shaped section"
    (sections.size == 5 && sections.all fun (_, attrs) =>
      attrs.any fun (k, v) => k == "class" && hasStr v "block-shaped")
  check ref "block template HTML: no block carries a colour box"
    ((elemAttrsList (fun _ => true) #[] body.toList).all fun (_, attrs) =>
      !attrs.any fun (k, v) => k == "class" && v == "block-body")
  let headers := (shapedSections body).map fun kids =>
    (kids.filter fun k => k matches .elem "header" _ _).size
  check ref s!"block template HTML: the untitled block sets no header ({headers})"
    (headers == #[1, 1, 0, 1, 1])
  let titleRule := cssRuleOf sheet "section.block-shaped.block-block > header::before"
  check ref s!"block template HTML: the title's rule is .3em wide in its colour ({titleRule})"
    (titleRule.any fun r => hasStr r "width: 0.3em" && hasStr r "#2e8b57" &&
      hasStr r "left: calc(0rem - 0.6em - 0.3em)")
  let rightRule := cssRuleOf sheet "section.block-shaped.block-alert > header::after"
  check ref s!"block template HTML: the alerted title's rule stands on the right ({rightRule})"
    (rightRule.any fun r => hasStr r "right: calc(" && hasStr r "position: absolute")
  check ref "block template HTML: a shaped block's body keeps the page's paragraph skip"
    (hasStr sheet ":where(section.block-shaped > *) { --parskip: inherit; }")

/-- **The stylesheet projects the record the page reads**: every rule of every
shaped kind is its box's pseudo-element declaring the rule's own width and
the lookup of its palette entry, `Ir.BlockEdge.ink`'s spelling. -/
private def projectionChecks (ref : IO.Ref (List String)) : IO Unit := do
  for (name, src) in sources do
    let (doc, _) := Elab.run s!"block-template-{name}.tex" src
    let css := HtmlDoc.blockShapeCss doc
    for kind in [Ir.TitledKind.block, .alert, .example] do
      let some shape := Ir.blockShapeOf doc.styles kind | continue
      for e in shape.edges do
        let box := s!"section.block-shaped.block-{kind.name}" ++
          (if e.span == .title then " > header" else "")
        let pseudo := if e.side == .left then "::before" else "::after"
        let paint := match e.name with
          | some n => s!"var({n.property}, {HtmlDoc.cssColor e.color})"
          | none => HtmlDoc.cssColor e.color
        check ref s!"block template {name} {kind.name}: the stylesheet draws the page's rule"
          ((cssRuleOf css (box ++ pseudo)).any fun r =>
            hasStr r s!"width: {HtmlDoc.blockShapeLength doc e.width};" &&
              hasStr r s!"background: {paint};")
        check ref s!"block template {name} {kind.name}: the page reads the rule's palette entry"
          (e.ink doc.palette == e.color)

/-- The reading names what it does not read: a template outside the
vocabulary is not applied, beamer's default pair stands, and the loss is
one warning; the native spelling the reading lands as reads back as the
record, its emptiest form included. -/
private def readingChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  for (name, src) in sources do
    let (_, diags) := Elab.run s!"block-template-{name}.tex" src
    check ref s!"block template {name}: the template and its registers are read, not skipped"
      (diags.all fun d => d.code != "W0301" && d.code != "W0110" &&
        !(d.code == "W0104" && hasStr d.message "probe edge"))
  let boxed := hanging.replace "\\defbeamertemplate*{block begin}{probe}{\\probe@open{}}"
    "\\defbeamertemplate*{block begin}{probe}{\\begin{beamercolorbox}{block title}\\insertblocktitle\\end{beamercolorbox}}"
  check ref "block template: the unread probe differs from the probe" (boxed != hanging)
  let (_, out, diags) := layout fonts "unread" boxed
  check ref "block template: an unread template is named once"
    ((diags.filter fun d => d.code == "W0110" && d.subject == some "beamer:template:block begin").size == 1)
  check ref "block template: an unread template's blocks keep the default pair"
    ((out.pages[0]?.map fun p => (p.fills.filter (·.color == edgeColor)).size) == some 0 &&
      ((Elab.run "block-template-unread.tex" boxed).1.styles.find? "block").bind (·.shape) == none)
  -- The native spelling round-trips, every field down to its emptiest form.
  let reads : List (String × Ir.BlockShape) :=
    [("{ title = plain, untitled = {} }", { title := {}, bare := some {} }),
     ("{ title = plain, untitled = { before = medskipamount + 5pt, between = 3pt } }",
      { title := {}, bare := some { before := #[.register "medskipamount", .glue { width := .ofSp (Dim.pt 5) }]
                                    between := #[.glue { width := .ofSp (Dim.pt 3) }] } }),
     ("{ title = box strut parskip, untitled = box, before = medskipamount + 2pt, " ++
       "between = smallskipamount, after = bigskipamount, whole = parskip, " ++
       "edge = { span = whole, side = right, width = 0.25em, sep = 3pt, hang = false, color = accent } }",
      { title := { boxed := true, strut := true, parskip := true }, bare := none
        before := #[.register "medskipamount", .glue { width := .ofSp (Dim.pt 2) }]
        between := #[.register "smallskipamount"], after := #[.register "bigskipamount"]
        whole := some true
        edges := #[{ span := .whole, side := .right, width := { width := { em := 250 } }
                     sep := { width := .ofSp (Dim.pt 3) }, hang := false
                     color := { r := 0x12, g := 0x34, b := 0x56 }, name := some (.role .accent) }] }),
     ("{ title = box strut parskip, untitled = {}, edge = { span = title, side = left, " ++
       "width = 0.3em, sep = 0.6em, hang = true, color = accent, height = -0.5lh + 0.5cap, " ++
       "depth = 0.5lh - 0.5cap - 1pt } }",
      { title := { boxed := true, strut := true, parskip := true }, bare := some {}
        edges := #[{ span := .title, side := .left, width := { width := { em := 300 } }
                     sep := { width := { em := 600 } }, hang := true
                     color := { r := 0x12, g := 0x34, b := 0x56 }, name := some (.role .accent)
                     reach := .lines { lead := -500, cap := 500 }
                       { lead := 500, cap := -500, sp := -Dim.pt 1 } }] }),
     ("{ title = box strut parskip, untitled = { before = medskipamount }, before = medskipamount, " ++
       "after = smallskipamount, edge = { span = whole, side = left, width = 0.3em, sep = 0.6em, " ++
       "hang = true, color = accent, height = -0.5lh + 0.5cap, depth = 0.5lh - 0.5cap } }",
      { title := { boxed := true, strut := true, parskip := true }
        bare := some { before := #[.register "medskipamount"] }
        before := #[.register "medskipamount"], after := #[.register "smallskipamount"]
        edges := #[{ span := .whole, side := .left, width := { width := { em := 300 } }
                     sep := { width := { em := 600 } }, hang := true
                     color := { r := 0x12, g := 0x34, b := 0x56 }, name := some (.role .accent)
                     reach := .lines { lead := -500, cap := 500 } { lead := 500, cap := -500 } }] })]
  for (src, want) in reads do
    let doc := (Elab.run "block-shape.tex"
      ("\\documentclass{slides}\n\\palette{ accent = #123456 }\n\\style{block}{ shape = " ++ src ++
        " }\n\\begin{document}\n\\end{document}\n")).1
    -- The colour is the palette's own reading of its entry.
    let accent := (doc.palette.find? "accent").getD Ir.Color.black
    let want := { want with edges := want.edges.map fun e => { e with color := accent } }
    check ref s!"block template: the native shape {src} reads back"
      (((doc.styles.find? "block").bind (·.shape)) == some want)

/-- The reading names a rule it does not hold beside the title's lines: one
reading its box's height alone, one taking off a paragraph skip its box's
list does not open on, one reading the height of a character other than
`H`, one beside a title box no strut bounds, whose lines stand as tall and
as deep as their ink, and one beside a box whose first strut is set before
the title's font. Each pair is named once, for its reading, and its blocks
keep beamer's default pair; the native spelling refuses a rule reaching by
lines beside a title box without struts the same way. The plain kind reads
half the capitals' leading past its lines. -/
private def capitalReadingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let height := capitalsSource.replace
    "height \\dimexpr\\ht\\probe@box+\\dp\\probe@box-\\parskip-\\probe@down\\relax"
    "height \\dimexpr\\ht\\probe@box-\\parskip-\\probe@down\\relax"
  let skip := capitalsSource.replace
    "height \\dimexpr\\ht\\probe@box+\\dp\\probe@box-\\probe@down\\relax"
    "height \\dimexpr\\ht\\probe@box+\\dp\\probe@box-\\parskip-\\probe@down\\relax"
  let other := capitalsSource.replace "\\fontcharht\\font`H" "\\fontcharht\\font`x"
  let unstrutted := capitalsSource.replace
    "\\usebeamerfont*{block title#1}\\usebeamercolor[fg]{block title#1}%\n      \\strut\\insertblocktitle\\strut\\par"
    "\\usebeamerfont*{block title#1}\\usebeamercolor[fg]{block title#1}%\n      \\insertblocktitle\\par"
  let early := capitalsSource.replace
    "\\usebeamerfont*{block title example}\\strut\\usebeamercolor[fg]{block title example}%"
    "\\strut\\usebeamerfont*{block title example}\\usebeamercolor[fg]{block title example}%"
  let cases : List (String × String × String × String × String) :=
    [("height", height, "block begin", "block", "reading other than its height and depth"),
     ("skip", skip, "block example begin", "exampleblock",
       "another skip than the one its list opens on"),
     ("other", other, "block begin", "block", "\\probe@down set to a length it cannot read"),
     ("unstrutted", unstrutted, "block begin", "block", "reaching by lines no strut bounds"),
     ("early", early, "block example begin", "exampleblock", "struts of another font bound")]
  for (name, src, element, style, why) in cases do
    check ref s!"capitals {name}: the refused probe differs from the probe" (src != capitalsSource)
    let (doc, diags) := Elab.run s!"block-template-capitals-{name}.tex" src
    let named := diags.filter fun d =>
      d.code == "W0110" && d.subject == some s!"beamer:template:{element}"
    check ref s!"capitals {name}: the template is named once, for its reading ({named.map (·.message)})"
      (named.size == 1 && named.all (hasStr ·.message why))
    check ref s!"capitals {name}: its blocks keep the default pair"
      (((doc.styles.find? style).bind (·.shape)).isNone)
  -- The plain kind reads half the capitals' leading past its lines, the
  -- pair `Ir.BlockMetric.halfLeading_centred_exact` speaks of.
  let (doc, _) := Elab.run "block-template-capitals.tex" capitalsSource
  let reaches := ((Ir.blockShapeOf doc.styles .block).map (·.edges.map (·.reach))).getD #[]
  check ref "capitals: the plain kind's rule reads half the capitals' leading past its lines"
    (reaches == #[.lines Ir.BlockMetric.halfLeading.neg Ir.BlockMetric.halfLeading])
  let (_, nd) := Elab.run "block-shape-unstrutted.tex"
    ("\\documentclass{slides}\n\\palette{ accent = #123456 }\n\\style{block}{ shape = " ++
      "{ title = box parskip, untitled = {}, edge = { span = title, side = left, width = 0.3em, " ++
      "sep = 0.6em, hang = true, color = accent, height = -0.5lh + 0.5cap, depth = 0.5lh - 0.5cap } } }\n" ++
      "\\begin{document}\n\\end{document}\n")
  check ref s!"capitals: the native spelling refuses lines beside a title no strut bounds ({nd.map (·.message)})"
    (nd.any fun d => d.code == "E0323" && hasStr d.message "a title that is not a box its struts bound")

/-- **A register a template assigns is no length of the document's**
(the premise beside `Compat.flushBeamerBlocks`' register gate): the probe's
`\probe@down`, which the templates assign and read as TeX runs them, read by
the document's own text — a gap in a paragraph — is refused by name, where
TeX would set the value its last run left there and a length token would
set none; set with `\setlength` first, it is refused the same way. -/
private def capitalRegisterChecks (ref : IO.Ref (List String)) : IO Unit := do
  let used := capitalsSource
    |>.replace "\\makeatother\n" "\\newcommand{\\probegap}{\\hspace*{\\probe@down}}\n\\makeatother\n"
    |>.replace "Body words here.\n" "Body\\probegap{} words here.\n"
  check ref "capitals register: the probe using its register differs from the probe" (used != capitalsSource)
  let (_, diags) := Elab.run "block-template-capitals-register.tex" used
  check ref s!"capitals register: the document's read of the template's register is refused by name ({diags.filter (·.severity == .error) |>.map (·.message)})"
    (diags.any fun d => d.severity == .error && hasStr d.message "probe@down")
  -- Set as a length first, it still holds no value the document reads.
  let set := used.replace "\\makeatother\n" "\\setlength{\\probe@down}{3pt}\n\\makeatother\n"
  check ref "capitals register: the probe setting its register differs from the probe" (set != used)
  let (_, sd) := Elab.run "block-template-capitals-register-set.tex" set
  check ref s!"capitals register: a register set as a length is still refused where the document reads it ({sd.filter (·.severity == .error) |>.map (·.message)})"
    (sd.any fun d => d.severity == .error && hasStr d.message "probe@down")
  let (_, clean) := Elab.run "block-template-capitals.tex" capitalsSource
  check ref "capitals register: the probe alone raises nothing"
    (clean.all (·.severity == .note))

/-- fontspec's `\newfontfamily\cmd{Family}` declares a family beside the
three slots and the command that selects it, and beamer's
`\setbeamerfont{block title}{series=\mdseries,family=\cmd}` sets the block
title in it, through the title's font site (`\style{block}{ font = … }`),
which the alerted title inherits by beamer's parent chain. A family named
by one face — "Source Serif Pro Bold", which fontspec finds as that face —
sets the title in that face at the medium series, where the title's own
default is the sans bold, in both artifacts: the PDF's title runs in that
face, the HTML's title span in the family's own stack, whose faces are that
face's. The command switches the family in text too. -/
private def familySource : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n\\usetheme{moloch}\n" ++
  "\\usepackage{fontspec}\n\\setsansfont{Open Sans}\n" ++
  "\\newfontfamily\\probetitle{Source Serif Pro Bold}\n" ++
  "\\setbeamerfont{block title}{series=\\mdseries,family=\\probetitle}\n" ++
  "\\begin{document}\n\\begin{frame}[t]{Family}\n" ++
  "\\begin{block}{Alpha title words}Body words here.\\end{block}\n" ++
  "\\begin{alertblock}{Beta title words}Third body words.\\end{alertblock}\n" ++
  "{\\probetitle Gamma} plain words.\n" ++
  "\\end{frame}\n\\end{document}\n"

private def familyChecks (ref : IO.Ref (List String)) : IO Unit := do
  let (doc, diags) := Elab.run "block-template-family.tex" familySource
  check ref "block title family: the family and its command are read, not skipped"
    (diags.all fun d => d.code != "W0301" &&
      !(d.code == "W0104" && hasStr d.message "block title"))
  check ref "block title family: the family is declared beside the three slots"
    (doc.fonts.families == #[("probetitle", "Source Serif Pro Bold")])
  let scanned ← FontDiscovery.scanRootsIn none [testFonts]
  let scan : FontAssembly.FaceScan := { faces := scanned, docDirs := [], dirs := #[], diags := #[] }
  let cache ← FontEnv.Cache.mk'
  let .ok (fs, doc, fdiags, _) ← FontAssembly.buildFontSet doc scan cache .settled |
    check ref "block title family: the fixture fonts assemble" false
  check ref "block title family: the named face is its own regular, no substitution"
    (fdiags.all (·.code != "W0006"))
  let out := Layout.run (Layout.Geom.ofPage doc.page) fs none doc
  let page := out.pages[0]?.getD {}
  let titleFace := "SourceSerifPro-Bold"
  let faces (t : String) : Array String :=
    ((page.lines.find? fun l => !l.furniture && (lineText l false).startsWith (letters t)).map
      fun l => (lineRuns l).map fun (idx, _, _, _) => (fs.get idx).psName).getD #[]
  check ref s!"block title family: the block title sets in the family's face ({faces "Alpha title words"})"
    (!(faces "Alpha title words").isEmpty && (faces "Alpha title words").all (· == titleFace))
  check ref s!"block title family: the alerted title follows the plain one ({faces "Beta title words"})"
    (!(faces "Beta title words").isEmpty && (faces "Beta title words").all (· == titleFace))
  check ref s!"block title family: the body keeps the sans face ({faces "Body words here."})"
    ((faces "Body words here.").all (· == "OpenSans-Regular") && !(faces "Body words here.").isEmpty)
  let switched := faces "Gamma"
  check ref s!"block title family: the command switches the family for its group ({switched})"
    (switched[0]? == some titleFace && switched.back? == some "OpenSans-Regular")
  let (head, body, _) := HtmlDoc.emitTree { fonts := some fs } doc
  let sheet := treeCssList "" (head.toList ++ body.toList)
  let slot := Ir.familySlotBase
  check ref "block title family HTML: the title span is the family's stack"
    ((body.flatMap (attrValuesOf (· == "span") "style")).contains s!"font-family: var(--font-{slot})")
  check ref "block title family HTML: the family's stack opens on its own synthetic family"
    (hasStr sheet s!"--font-{slot}: \"ltx-{slot}\"")
  check ref "block title family HTML: the family ships the face the PDF sets"
    ((HtmlDoc.shipFaces fs).any fun ff => ff.family == s!"ltx-{slot}" &&
      (fs.get ff.index).psName == titleFace)


/-- A rule painted by `\usebeamercolor{element}\color{bg}` is the element's
background, which `\usebeamercolor` binds to `bg` (beamerbasecolor.sty), in
the epoch each frame stands in — lualatex paints the three frames' rules
green, red and blue. -/
private def channelChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let (_, out, diags) := layout fonts "channels" channelsSource
  check ref "block template channels: the probe reads without loss"
    ((diags ++ out.diags).all (·.severity == .note))
  let red : Ir.Color := { r := 0xB2, g := 0x22, b := 0x22 }
  let blue : Ir.Color := { r := 0x1E, g := 0x40, b := 0xAF }
  for (page, c) in [(0, edgeColor), (1, red), (2, blue)] do
    let rules := ((out.pages[page]?.map (·.fills)).getD #[]).filter fun f => f.w < Dim.pt 2
    check ref s!"block template channels page {page}: the rule paints the element's background"
      (rules.size == 1 && rules.all (·.color == c))

/-- **`\usebeamercolor` binds a channel only where its element sets one**
(beamerbasecolor.sty: `fg` and `bg` become the element's where it has them
and keep the colour in force otherwise): `\color{bg}` after an element with
no background paints the earlier element's background, `\color{fg}` after
one with no foreground the earlier one's foreground, and
`\usebeamercolor[bg]` of an element with no background keeps the earlier
one's — lualatex paints the three rules green, rose and green — in each
frame's epoch, so a frame that gives the foreground-only element a
background paints its rules blue. The earlier element is read, so nothing
calls its colours unused. -/
private def chainChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let (_, out, diags) := layout fonts "chain" chainSource
  check ref "block template chain: the probe reads without loss"
    ((diags ++ out.diags).all (·.severity == .note))
  let blue : Ir.Color := { r := 0x1E, g := 0x40, b := 0xAF }
  for (page, want) in [(0, #[edgeColor, edgeTwoColor, edgeColor]), (1, #[blue, blue])] do
    let rules := ((((out.pages[page]?.map (·.fills)).getD #[]).filter fun f => f.w < Dim.pt 2).qsort
      (·.y < ·.y)).map (·.color)
    check ref s!"block template chain page {page}: each rule paints the channel its chain binds"
      (rules == want)

/-- A shipped line's first glyph run: the face and size it sets in. -/
private def firstRun (fs : Font.FontSet) (l : Layout.LineOut) : Option (Font.Font × Dim.Sp) :=
  l.segs.findSome? fun s => match s with
    | .run idx _ _ _ gs size _ _ _ _ _ =>
      if gs.isEmpty then none else some (fs.get idx, if size == 0 then l.size else size)
    | _ => none

/-- How far a shipped line's ink stands above its baseline: its tallest
glyph's, in the face and at the size its run sets in. -/
private def inkTop (fs : Font.FontSet) (l : Layout.LineOut) : Dim.Sp :=
  l.segs.foldl (init := 0) fun acc s => match s with
    | .run idx _ _ _ gs size _ _ raise _ _ =>
      let face := fs.get idx
      let size := if size == 0 then l.size else size
      gs.foldl (init := acc) fun acc (g, _, _) => match face.bounds g with
        | some b => max acc (((b.top.toNat * size.toNat / face.unitsPerEm : Nat) : Int) + raise)
        | none => acc
    | _ => acc

/-- The non-furniture lines a fill spans, top to bottom. -/
private def linesBeside (p : Layout.PageOut) (bar : Layout.Fill) : Array Layout.LineOut :=
  (p.lines.filter fun l => !l.furniture && bar.y ≤ l.y && l.y ≤ bar.y + bar.h).qsort (·.y < ·.y)

/-- **A rule reaching by its title's lines stands centred on the capitals**
over the shipped pages, as `Layout.edgeLinesSpan_centred_exact` states it of
the fill beside lines struts bound, given the half-leading pair the template
reads (`Ir.BlockMetric.halfLeading_centred_exact`): every
rule beside the probe's plain and example titles — one line and two, at the
body's size and at `\large`, two lines a skip further apart — has its
midpoint at the midpoint of the span from its title's first line's cap
height, the height of `H` in the face and at the size the line's first run
sets in, to its last line's baseline, and reaches its lines' span and one
`\baselineskip` more, to two scaled points. Where the first line's ink
stands above its strut — an accented capital — TeX's box of that line is as
much taller, and so is the rule above it. -/
private def capitalChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let (_, out, _) := layout fonts "capitals" capitalsSource
  for (page, leads) in [(0, [12, 12]), (1, [14, 14]), (3, [12, 12, 14])] do
    let p : Layout.PageOut := out.pages[page]?.getD {}
    let bars := (p.fills.filter (·.color == edgeColor)).qsort (·.y < ·.y)
    check ref s!"capitals page {page}: a rule beside each title ({bars.size})" (bars.size == leads.length)
    for (bar, lead) in bars.toList.zip leads do
      let lead := Dim.pt lead
      let title := linesBeside p bar
      match title[0]?, title.back?, title[0]?.bind (firstRun fonts) with
      | some first, some last, some (face, size) =>
        let cap : Dim.Sp := (((face.charHeight 'H').toNat * size.toNat / face.unitsPerEm : Nat) : Int)
        let excess := max 0 (inkTop fonts first - lead * 7 / 10)
        check ref (s!"capitals page {page}: the {title.size}-line title's rule is centred on its capitals " ++
          s!"less its ink past the strut ({2 * bar.y + bar.h} against {first.y - cap + last.y - excess})")
          ((2 * bar.y + bar.h - (first.y - cap + last.y - excess)).natAbs ≤ 2)
        check ref s!"capitals page {page}: the {title.size}-line title's rule reaches its lines and a leading ({bar.h})"
          ((bar.h - (last.y - first.y + lead + excess)).natAbs ≤ 2)
      | _, _, _ => check ref s!"capitals page {page}: the title beside a rule ships" false

/-- The term a stylesheet length adds last, `calc(… + <term>)`, as a length
on a stage `height` tall: thousandths of `vh`, or a zero. -/
private def lastStageTerm (rule key : String) (height : Dim.Sp) : Option Dim.Sp := do
  let decl ← (rule.splitOn ";").find? fun d => (d.splitOn ":")[0]?.map (·.trimAscii.toString) == some key
  let value := ((decl.splitOn ":").drop 1 |> String.intercalate ":").trimAscii.toString
  let term := ((value.splitOn " + ").getLast?.getD value).trimAscii.toString
  let term := String.ofList (term.toList.reverse.dropWhile (· == ')')).reverse
  if term == "0rem" then return 0
  if !term.endsWith "vh" then none
  let (m, sc) ← Decl.parseDecimal (term.dropEnd 2).toString
  return m * 1000 / (sc : Int) * height / 100000

/-- The rules beside a page's titles in one colour, each with its title's
first and last lines and the face and size its first run sets in. -/
private def titleBars (fonts : Font.FontSet) (p : Layout.PageOut) (c : Ir.Color) :
    Array (Layout.Fill × Layout.LineOut × Layout.LineOut × Font.Font × Dim.Sp) :=
  ((p.fills.filter (·.color == c)).qsort (·.y < ·.y)).filterMap fun bar =>
    let title := linesBeside p bar
    match title[0]?, title.back?, title[0]?.bind (firstRun fonts) with
    | some first, some last, some (face, size) => some (bar, first, last, face, size)
    | _, _, _ => none

/-- The capitals probe with every rule reaching by its box alone. -/
private def boxedRules (src : String) : String :=
  src
    |>.replace ("height \\dimexpr\\ht\\probe@box+\\dp\\probe@box-\\parskip-\\probe@down\\relax\n" ++
        "          depth \\probe@down}") "height \\ht\\probe@box depth \\dp\\probe@box}"
    |>.replace ("height \\dimexpr\\ht\\probe@box+\\dp\\probe@box-\\probe@down\\relax\n" ++
        "          depth \\probe@down}") "height \\ht\\probe@box depth \\dp\\probe@box}"
    |>.replace ("height \\dimexpr\\dp\\probe@box+\\ht\\probe@box-\\parskip-\\probe@down+1pt\\relax\n" ++
        "          depth \\probe@down}") "height \\ht\\probe@box depth \\dp\\probe@box}"

/-- One build's HTML against its PDF, kind by kind: each rule's place about
its title's baselines, and the rise and room the header keeps against the
same template with every rule reaching by its box alone, for a title of one
line and one broken by `\\`. -/
private def titleRuleHtmlChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (name src : String) (kinds : List (Ir.TitledKind × String × Nat × Ir.Color × String × String × String))
    (broken : List (Ir.TitledKind × Nat × String × String)) : IO Unit := do
  let (doc, _) := Elab.run s!"block-template-{name}.tex" src
  let geom := Layout.Geom.ofPage doc.page
  let cfg : HtmlDoc.Config := { blockTitleRule := Layout.blockTitleRule geom fonts doc.styles }
  let (head, body, _) := HtmlDoc.emitTree cfg doc
  let sheet := treeCssList "" (head.toList ++ body.toList)
  let (_, out, _) := layout fonts name src
  let (_, plain, _) := layout fonts s!"{name}-boxed" (boxedRules src)
  let tol : Nat := (2 * doc.page.height / 100000 + 2).toNat
  let strut := fonts.get (fonts.lookup 0 700 false)
  let leaded (f : Font.Font) (size : Dim.Sp) : Dim.Sp × Dim.Sp :=
    let sc (u : Int) : Dim.Sp := ((u.toNat * size.toNat / f.unitsPerEm : Nat) : Int)
    Layout.leadedBox (sc f.ascent) (sc (-f.descent)) (Ir.leadingFor size doc.page.leading)
  let distance (out : Layout.Out) (page : Nat) (a b : String) : Option Dim.Sp :=
    out.pages[page]?.bind fun p => (lineOf p a).bind fun x => (lineOf p b).map (·.y - x.y)
  -- The rise a header's padding adds past its skips: the term it ends on.
  let riseOf (rule : String) : Dim.Sp := (lastStageTerm rule "padding-top" doc.page.height).getD 0
  for (kind, pseudo, page, color, lead, title, next) in kinds do
    let sel := s!"section.block-shaped.block-{kind.name} > header"
    let rule := (cssRuleOf sheet s!"{sel}::{pseudo}").getD ""
    let p : Layout.PageOut := out.pages[page]?.getD {}
    let bars := titleBars fonts p color
    check ref s!"{name} HTML {kind.name}: the page's rules ship ({bars.size})" (!bars.isEmpty)
    for (bar, first, last, face, size) in bars do
      let s := leaded strut doc.page.fontSize
      let r := leaded face size
      let b := max s.1 r.1
      let box := b + max s.2 r.2
      match lastStageTerm rule "top" doc.page.height, lastStageTerm rule "bottom" doc.page.height with
      | some top, some bottom =>
        check ref (s!"{name} HTML {kind.name}: the rule's top stands above the first baseline as the page's " ++
          s!"({b - top} against {first.y - bar.y})") (((b - top) - (first.y - bar.y)).natAbs ≤ tol)
        check ref (s!"{name} HTML {kind.name}: the rule's bottom stands below the last baseline as the page's " ++
          s!"({box - b - bottom} against {bar.y + bar.h - last.y})")
          (((box - b - bottom) - (bar.y + bar.h - last.y)).natAbs ≤ tol)
      | _, _ => check ref s!"{name} HTML {kind.name}: the rule's offsets read ({rule})" false
    let pad := ((cssRulesOf sheet sel).find? (hasStr · "padding-top")).getD ""
    let room := (lastStageTerm pad "padding-bottom" doc.page.height).getD 0
    match distance out page lead title, distance plain page lead title,
        distance out page title next, distance plain page title next with
    | some a, some a', some d, some d' =>
      check ref s!"{name} HTML {kind.name}: the header rises as the page's title ({riseOf pad} against {a - a'})"
        ((riseOf pad - (a - a')).natAbs ≤ tol)
      check ref s!"{name} HTML {kind.name}: the header keeps the page's room below ({room} against {d - d'})"
        ((room - (d - d')).natAbs ≤ tol)
    | _, _, _, _ => check ref s!"{name} HTML {kind.name}: the boxed probe's lines ship" false
  -- A title the author breaks stands as low as the page's broken title.
  for (kind, page, prev, title) in broken do
    let sel := s!"section.block-shaped.block-{kind.name} > header"
    let pad := ((cssRulesOf sheet s!"{sel}:has(br)").find? (hasStr · "padding-top")).getD
      (((cssRulesOf sheet sel).find? (hasStr · "padding-top")).getD "")
    match distance out page prev title, distance plain page prev title with
    | some a, some a' =>
      check ref s!"{name} HTML {kind.name}: a broken title's header rises as the page's ({riseOf pad} against {a - a'})"
        ((riseOf pad - (a - a')).natAbs ≤ tol)
    | _, _ => check ref s!"{name} HTML {kind.name}: the broken titles ship" false

/-- **The web page stands each rule reaching by its title's lines where the
page stands it** (`HtmlDoc.blockShapeCss`, `Layout.blockTitleRule`): each
kind's rule is its header's pseudo-element, its top the header's first line
box's top and its bottom its last line box's bottom, each moved by the offset
the driver measures over the page's faces. Under CSS 2.1 §10.8.1's model of
the header's lines — the header's strut, its bold body face at the body's
size, and the title's run in its face at its size, each leaded at its size's
share of the page's leading over its ascent and descent, the line box their
union — every rule stands as far above its title's first baseline and below
its last as the PDF's rule beside the same title, for one line and two, to
the stylesheet's precision: the plain and `\large` rules centred on their
capitals, and the alerted rule on the right a point above its centre. The
header keeps what TeX's line holding box and rule adds beside the lines: the
room below the alerted rule, deeper than its box, and the rise past the box's
top — all of it for a title the author breaks, and for one line what the
interline rule leaves of it, nothing where the `\baselineskip` absorbs it —
each the distance the PDF's title and body move against the same template
with every rule reaching by its box alone; at the body's size, with no
`\parskip`, and at `\large`. A rule reaching by its box beside one that
rises stands from the box's top, the rise above it. -/
private def capitalHtmlChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let kinds : List (Ir.TitledKind × String × Nat × Ir.Color × String × String × String) :=
    [(.block, "before", 0, edgeColor, "Lead paragraph above.", "Alpha title words", "Body words here."),
     (.example, "before", 1, edgeColor, "Lead paragraph above.", "Gamma title words", "Third body words."),
     (.alert, "after", 2, alertColor, "Lead paragraph above.", "Beta title words", "Fifth body words.")]
  let broken : List (Ir.TitledKind × Nat × String × String) :=
    [(.block, 0, "Body words here.", "Delta first title line"),
     (.example, 1, "Third body words.", "Epsilon first title line")]
  titleRuleHtmlChecks ref fonts "capitals" capitalsSource kinds broken
  let unsized := capitalsSource.replace "\\setbeamerfont{block title example}{size=\\large}\n" ""
  check ref "capitals HTML: the unsized probe differs from the probe" (unsized != capitalsSource)
  titleRuleHtmlChecks ref fonts "capitals-unsized" unsized kinds broken
  let flush := capitalsSource.replace "\\setlength{\\parskip}{4pt}\n" "\\setlength{\\parskip}{0pt}\n"
  check ref "capitals HTML: the probe with no paragraph skip differs from the probe" (flush != capitalsSource)
  titleRuleHtmlChecks ref fonts "capitals-flush" flush kinds broken
  -- A rule reaching by its box beside the large title's rising rule.
  let beside := capitalsSource.replace
    "    \\box\\probe@box\\par\\nobreak\n  \\fi\n  \\usebeamerfont{block body example}"
    ("    \\copy\\probe@box\\rlap{\\hskip 4pt\\vrule width 3pt height \\ht\\probe@box depth \\dp\\probe@box}" ++
      "\\par\\nobreak\n  \\fi\n  \\usebeamerfont{block body example}")
  check ref "capitals HTML: the probe with a box rule beside the large title differs" (beside != capitalsSource)
  let (doc, _) := Elab.run "block-template-capitals-beside.tex" beside
  let geom := Layout.Geom.ofPage doc.page
  let cfg : HtmlDoc.Config := { blockTitleRule := Layout.blockTitleRule geom fonts doc.styles }
  let (head, body, _) := HtmlDoc.emitTree cfg doc
  let sheet := treeCssList "" (head.toList ++ body.toList)
  let sel := "section.block-shaped.block-example > header"
  let pad := ((cssRulesOf sheet sel).find? (hasStr · "padding-top")).getD ""
  let boxRule := (cssRuleOf sheet s!"{sel}::after").getD ""
  match lastStageTerm pad "padding-top" doc.page.height, lastStageTerm boxRule "top" doc.page.height with
  | some rise, some top =>
    check ref s!"capitals HTML: the box's rule stands from the box's top, the rise above it ({top} against {rise})"
      (rise > 0 && (top - rise).natAbs ≤ (2 * doc.page.height / 100000 + 2).toNat)
  | _, _ => check ref s!"capitals HTML: the box rule's place reads ({pad} / {boxRule})" false

/-- A page's ink, as a comparison reads it: every line's place and letters,
every fill's rectangle and colour. -/
private def pageInk (out : Layout.Out) : Array String :=
  out.pages.flatMap fun p =>
    (p.lines.map fun l => s!"line {l.x} {l.y} {lineText l false}") ++
      p.fills.map fun f => s!"fill {f.x} {f.y} {f.w} {f.h} {f.color.r} {f.color.g} {f.color.b}"

/-- Every `\style` key no beamer block reads, with a value its own element
would take. -/
private def blockUnreadEntries : List (String × String) :=
  [("before", "30pt"), ("after", "30pt"), ("rule", "blue"), ("rule-position", "baseline"),
   ("rule-thickness", "2pt"), ("marker", "{x}"), ("indent", "2em"), ("gap", "4pt"),
   ("align", "center"), ("separator", "blue"), ("rule-above", "1pt"), ("rule-above-skip", "2pt"),
   ("rule-above-gap", "3pt"), ("rule-below", "1pt"), ("rule-below-gap", "2pt"),
   ("rule-below-skip", "3pt"), ("author-font", "{\\itshape}"), ("author-strut", "4pt"),
   ("body-size", "small"), ("hover", "red"), ("focus", "blue"), ("motion", "150ms"),
   ("color", "red")]

/-- An article with no palette, so its stylesheet carries a dark scheme. -/
private def paletteFree : String :=
  "\\documentclass{article}\n\\begin{document}\nPlain words here.\n\\end{document}\n"

/-- The style keys a beamer block reads are its title's `font` and its
template's `shape`. Every other key `\style` knows is named once (W0104)
where it is declared and kept out of the document's styles, so both
artifacts ship exactly what they ship without it: on the three kinds,
templated or in beamer's default blocks, and on a page with no palette,
whose stylesheet keeps the dark scheme a stored colour once took away. A
key `\style` does not know, or one another element owns, is its own one
refusal and nothing more. -/
private def blockStyleKeyChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let spec := String.intercalate ", " (blockUnreadEntries.map fun (k, v) => s!"{k} = {v}")
  for (probe, src) in [("hanging", hanging), ("plainsized", plainSizedSource),
      ("palettefree", paletteFree)] do
    for el in Ir.blockStyleElements do
      let line := s!"\\style\{{el}}\{ {spec} }\n"
      let styled := src.replace "\\begin{document}" (line ++ "\\begin{document}")
      check ref s!"block style {probe} {el}: the styled probe differs from the probe" (styled != src)
      let (_, outA, diagsA) := layout fonts probe src
      let (_, outB, diagsB) := layout fonts probe styled
      for (key, _) in blockUnreadEntries do
        check ref s!"block style {probe} {el}: '{key}' is named once"
          ((diagsB.filter fun d => d.code == "W0104" &&
            d.subject == some s!"style:{el}:{key}").size == 1)
      check ref s!"block style {probe} {el}: nothing else is raised"
        ((diagsB.filter (·.severity != .note)).size == blockUnreadEntries.length &&
          (diagsA.filter (·.severity != .note)).isEmpty)
      check ref s!"block style {probe} {el}: the page ships as without the keys"
        (pageInk outA == pageInk outB)
      let html (s : String) : String := (HtmlDoc.emit {} (Elab.run s!"block-style-{probe}.tex" s).1).1
      check ref s!"block style {probe} {el}: the HTML ships as without the keys"
        (html src == html styled)
  for (el, entry, code) in [("alertblock", "foo = 1", "E0322"),
      ("block", "slot = { set = title, anchor = west, at = west }", "E0323")] do
    let src := paletteFree.replace "\\begin{document}" s!"\\style\{{el}}\{ {entry} }\n\\begin\{document}"
    let (_, diags) := Elab.run "block-style-owned.tex" src
    let raised := diags.filter (·.severity != .note)
    check ref s!"block style {el}: '{entry}' is its one refusal, {code} ({raised.map (·.code)})"
      (raised.size == 1 && raised.all (·.code == code))

/-- The HTML stands a template's skips where the page does (`blockShapeCss`,
`blockRules`): the section's padding above the title in the arm the block
takes and below the body, the header's below the title — each the declared
skip's own length on the deck's stage — and no block margin of the default
pair's around it. A template that differs only in the skip above the title
differs in exactly that padding. -/
private def htmlSkipChecks (ref : IO.Ref (List String)) : IO Unit := do
  let (doc, _) := Elab.run "block-template-armed.tex" armedSource
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let sheet := treeCssList "" (head.toList ++ body.toList)
  let len (pt : Nat) : String := HtmlDoc.blockShapeLength doc { width := .ofSp (Dim.pt pt) }
  let peer := "var(--parskip, 0.725rem)"
  let plain := cssRuleOf sheet "section.block-shaped.block-block"
  check ref s!"block skips HTML: the section stands the template's skips above and below ({plain})"
    (plain.any fun r => hasStr r s!"padding-top: {len 6};" && hasStr r s!"padding-bottom: {len 3};")
  let header := cssRuleOf sheet "section.block-shaped.block-block > header"
  check ref s!"block skips HTML: the header stands the skip below the title ({header})"
    (header.any fun r => hasStr r s!"padding-bottom: {len 4};")
  let bare := cssRuleOf sheet "section.block-shaped.block-block:not(:has(> header))"
  check ref s!"block skips HTML: an untitled block stands its own arm's skips ({bare})"
    (bare.any fun r => hasStr r s!"padding-top: calc({len 11} + {peer});")
  let whole := cssRuleOf sheet "section.block-shaped.block-alert:not(:has(> header))"
  check ref s!"block skips HTML: an untitled body opening its box stands the arm's skip inside it ({whole})"
    (whole.any fun r => hasStr r s!"padding-top: calc({len 12} + {peer} + {len 3} + {peer});")
  check ref "block skips HTML: no default block margin stands around a templated block"
    (hasStr sheet ":where(* + section.block-shaped) { margin-top: 0rem; }")
  let bigger := armedSource.replace "  \\par\\vskip\\medskipamount\n" "  \\par\\vskip\\bigskipamount\n"
  check ref "block skips HTML: the bigger probe differs from the probe" (bigger != armedSource)
  let (doc2, _) := Elab.run "block-template-armed-big.tex" bigger
  let (head2, body2, _) := HtmlDoc.emitTree {} doc2
  let sheet2 := treeCssList "" (head2.toList ++ body2.toList)
  check ref "block skips HTML: a bigger skip above the title is a bigger padding"
    ((cssRuleOf sheet2 "section.block-shaped.block-block").any fun r =>
      hasStr r s!"padding-top: {len 12};")

/-- **The HTML sets an empty title box as TeX does** (`blockShapeCss`): the
box a template keeps for an untitled block stands its title font's strut
tall where the template struts it — lualatex's two empty boxes are the 2pt
`\parskip` inside them on a `\large` and a `\small` strut, 14 and 11 pt, on
the deck's stage — beside its rules; where it does not, the box holds no
paragraph, so it has no height and no rule beside it, and its line is one
line of the page. The empty header carries none of it inline: the stylesheet
owns each kind's box. A title with no box of its own spends its line's
`\parskip` once, and empty is its struts' line or no line at all. -/
private def emptyBoxHtmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let (doc, _) := Elab.run "block-template-emptybox.tex" emptyBoxSource
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let sheet := treeCssList "" (head.toList ++ body.toList)
  for (kind, strut) in [("block", Dim.pt 14), ("example", Dim.pt 11)] do
    let box := (cssRuleOf sheet s!"section.block-shaped.block-{kind} > header:empty").getD ""
    check ref s!"empty title box HTML {kind}: the box is its title font's strut tall ({box})"
      (hasStr box "box-sizing: content-box;" && cssStageLength box "min-height" strut doc.page.height)
  let bare := (cssRuleOf sheet "section.block-shaped.block-alert > header:empty").getD ""
  check ref s!"empty title box HTML alert: an unstrutted box holds no paragraph ({bare})"
    (hasStr bare "box-sizing: content-box;" && hasStr bare "min-height: 1lh;" &&
      hasStr bare "padding-top: var(--parskip, 0.725rem);")
  let rule := (cssRuleOf sheet "section.block-shaped.block-alert > header:empty::after").getD ""
  check ref s!"empty title box HTML alert: a box of no height has no rule beside it ({rule})"
    (hasStr rule "content: none;")
  let empties := (shapedSections body).flatMap fun kids => kids.filterMap fun k => match k with
    | .elem "header" attrs #[] => some attrs
    | _ => none
  check ref s!"empty title box HTML: every kind's empty box is the stylesheet's ({empties.size})"
    (empties.size == 3 && empties.all fun attrs => !attrs.any (·.1 == "style"))
  -- A title with no box of its own spends its line's `\parskip` alone; empty,
  -- it is the struts' line, or no line at all.
  let (plain, _) := Elab.run "block-template-plainempty.tex" plainEmptySource
  let (phead, pbody, _) := HtmlDoc.emitTree {} plain
  let psheet := treeCssList "" (phead.toList ++ pbody.toList)
  let titled := (cssRuleOf psheet "section.block-shaped.block-block > header").getD ""
  check ref s!"unboxed title HTML: the title spends its line's paragraph skip once ({titled})"
    (hasStr titled "padding-top: calc(var(--parskip, 0.725rem) + 0rem);")
  let none := (cssRuleOf psheet "section.block-shaped.block-block > header:empty").getD ""
  check ref s!"unboxed title HTML: an empty unstrutted title is no line ({none})"
    (hasStr none "min-height: 0rem;" && hasStr none "padding-top: 0rem;")
  let struts := (cssRuleOf psheet "section.block-shaped.block-alert > header:empty").getD ""
  check ref s!"unboxed title HTML: an empty strutted title is its struts' line ({struts})"
    (cssStageLength struts "min-height" (Dim.pt 14) plain.page.height &&
      hasStr struts "padding-top: var(--parskip, 0.725rem);")

/-- A shipped line's runs as the faces and sizes they set in. -/
private def lineFaces (fs : Font.FontSet) (l : Layout.LineOut) : Array (String × Dim.Sp) :=
  l.segs.filterMap fun s => match s with
    | .run idx _ _ _ gs size _ _ _ _ _ => if gs.isEmpty then none else some ((fs.get idx).psName, size)
    | _ => none

/-- The fixture fonts assembled for a document, as the CLI assembles them. -/
private def assemble (doc : Ir.Doc) : IO (Option (Font.FontSet × Ir.Doc)) := do
  let scanned ← FontDiscovery.scanRootsIn none [testFonts]
  let scan : FontAssembly.FaceScan := { faces := scanned, docDirs := [], dirs := #[], diags := #[] }
  let cache ← FontEnv.Cache.mk'
  match ← FontAssembly.buildFontSet doc scan cache .settled with
  | .ok (fs, doc, _, _) => return some (fs, doc)
  | .error _ => return none

/-- beamer's font parent chain, axis by axis (`Ir.blockTitleFont_axes_exact`):
the alerted and example titles keep the plain title's family where they
declare none and their own size where they declare one, and moloch's own
alerted title font keeps its size under a declared plain title size —
lualatex sets the plain, alerted and example titles in Source Serif Pro Bold
at 10, 9 and 10 pt in the first probe, and Open Sans Bold at 12, 10 and 12 pt
in the second. -/
private def parentChecks (ref : IO.Ref (List String)) : IO Unit := do
  let head := "\\documentclass[10pt,aspectratio=169]{beamer}\n\\usetheme{moloch}\n" ++
    "\\usepackage{fontspec}\n\\setsansfont{Open Sans}\n"
  let blocks := "\\begin{document}\n\\begin{frame}[t]{Parents}\nLead paragraph above.\n" ++
    "\\begin{block}{Alpha title words}Body words here.\\end{block}\n" ++
    "\\begin{alertblock}{Beta title words}Third body words.\\end{alertblock}\n" ++
    "\\begin{exampleblock}{Gamma title words}Fourth body words.\\end{exampleblock}\n" ++
    "\\end{frame}\n\\end{document}\n"
  let probes : List (String × String × List (String × String × Dim.Sp)) :=
    [("family", head ++ "\\newfontfamily\\probeserif{Source Serif Pro}\n" ++
        "\\setbeamerfont{block title}{family=\\probeserif}\n" ++
        "\\setbeamerfont{block title alerted}{size=\\small}\n" ++ blocks,
      [("Alpha title words", "SourceSerifPro-Bold", Dim.pt 10),
       ("Beta title words", "SourceSerifPro-Bold", Dim.pt 9),
       ("Gamma title words", "SourceSerifPro-Bold", Dim.pt 10)]),
     ("size", head ++ "\\setbeamerfont{block title}{size=\\large}\n" ++ blocks,
      [("Alpha title words", "OpenSans-Bold", Dim.pt 12),
       ("Beta title words", "OpenSans-Bold", Dim.pt 10),
       ("Gamma title words", "OpenSans-Bold", Dim.pt 12)]),
     -- Declared before the theme: loading moloch's font theme merges its own
     -- size and series over the plain and alerted titles' fields, keeping
     -- the declared family; the example title, which moloch leaves alone,
     -- keeps its declared size.
     ("pretheme", "\\documentclass[10pt,aspectratio=169]{beamer}\n\\usepackage{fontspec}\n" ++
        "\\setsansfont{Open Sans}\n\\newfontfamily\\probeserif{Source Serif Pro}\n" ++
        "\\setbeamerfont{block title}{size=\\large,family=\\probeserif}\n" ++
        "\\setbeamerfont{block title alerted}{size=\\small}\n" ++
        "\\setbeamerfont{block title example}{size=\\Large}\n\\usetheme{moloch}\n" ++ blocks,
      [("Alpha title words", "SourceSerifPro-Bold", Dim.pt 10),
       ("Beta title words", "SourceSerifPro-Bold", Dim.pt 10),
       ("Gamma title words", "SourceSerifPro-Bold", Dim.pt 144 / 10)]),
     -- The starred form clears the plain title's fields, moloch's series
     -- with them: the plain title and the example under it set in the
     -- regular weight, the alerted one in its own bold.
     ("starred", head ++ "\\setbeamerfont*{block title}{size=\\small}\n" ++ blocks,
      [("Alpha title words", "OpenSans-Regular", Dim.pt 9),
       ("Beta title words", "OpenSans-Bold", Dim.pt 10),
       ("Gamma title words", "OpenSans-Regular", Dim.pt 9)])]
  for (name, src, want) in probes do
    let (doc, _) := Elab.run s!"block-title-{name}.tex" src
    let some (fs, doc) ← assemble doc | check ref s!"block title {name}: the fixture fonts assemble" false
    let out := Layout.run (Layout.Geom.ofPage doc.page) fs none doc
    let page := out.pages[0]?.getD {}
    for (title, face, size) in want do
      let faces := ((page.lines.find? fun l => !l.furniture &&
        (lineText l false).startsWith (letters title)).map (lineFaces fs)).getD #[]
      check ref s!"block title {name}: '{title}' sets in {face} at {milliOf size} ({faces})"
        (!faces.isEmpty && faces.all (· == (face, size)))
  let (_, diags) := Elab.run "block-title-starred.tex"
    (head ++ "\\setbeamerfont*{block title}{size=\\small}\n" ++ blocks)
  check ref "block title starred: the note names the declaration with its star"
    (diags.any fun d => d.code == "N0100" && hasStr d.message "'\\setbeamerfont*{block title}'")

/-- fontspec's provide forms define the command only where it is undefined
(`\ProvideDocumentCommand`): a family command already declared keeps its
family, as lualatex keeps it, and a new one is declared. -/
private def provideChecks (ref : IO.Ref (List String)) : IO Unit := do
  let src := "\\documentclass[10pt,aspectratio=169]{beamer}\n\\usetheme{moloch}\n" ++
    "\\usepackage{fontspec}\n\\setsansfont{Open Sans}\n" ++
    "\\newfontfamily\\probeA{Source Serif Pro}\n" ++
    "\\providefontfamily\\probeA{Source Code Pro}\n" ++
    "\\providefontface\\probeC{Source Code Pro}\n" ++
    "\\begin{document}\n\\begin{frame}[t]{Provide}\n" ++
    "{\\probeA Serif words} plain words {\\probeC Code words}.\n" ++
    "\\end{frame}\n\\end{document}\n"
  let (doc, diags) := Elab.run "block-title-provide.tex" src
  check ref s!"provide forms: a defined command keeps its family ({doc.fonts.families})"
    (doc.fonts.families == #[("probeA", "Source Serif Pro"), ("probeC", "Source Code Pro")])
  check ref "provide forms: the kept command's provide is accounted as nothing"
    (diags.any fun d => d.subject == some "ctrl:nothing:providefontfamily:probeA")
  let some (fs, doc) ← assemble doc | check ref "provide forms: the fixture fonts assemble" false
  let out := Layout.run (Layout.Geom.ofPage doc.page) fs none doc
  let page : Layout.PageOut := out.pages[0]?.getD {}
  let faces := match page.lines.find? fun l => hasStr (lineText l false) "Serif" with
    | some line => lineFaces fs line
    | none => #[]
  check ref s!"provide forms: the kept family sets its own face ({faces})"
    (faces[0]?.map (·.1) == some "SourceSerifPro-Regular" &&
      faces.any (·.1 == "SourceCodePro-Regular"))

/-- The IR dump, the golden witness, carries every declared family under
the key that declares it, and each of its faces under that family's key. -/
private def dumpChecks (ref : IO.Ref (List String)) : IO Unit := do
  let src := "\\documentclass{article}\n\\usepackage{fontspec}\n" ++
    "\\newfontfamily\\probeA{Source Serif Pro}[BoldFont=Source Serif Pro Bold]\n" ++
    "\\newfontface\\probeB{FiraSans-Regular.otf}\n" ++
    "\\begin{document}\nWords.\n\\end{document}\n"
  let (doc, diags) := Elab.run "block-title-dump.tex" src
  let dump := Ir.dump doc diags -- ir tier: the claim is the dump's own, the golden witness's record of the fonts
  for line in ["font family.probeA \"Source Serif Pro\"", "font family.probeB \"FiraSans-Regular.otf\"",
      "font family.probeA.bold \"Source Serif Pro Bold\"",
      "font family.probeB.bold \"FiraSans-Regular.otf\"",
      "font family.probeB.italic \"FiraSans-Regular.otf\"",
      "font family.probeB.bolditalic \"FiraSans-Regular.otf\""] do
    check ref s!"font dump: {line}" (hasStr dump (line ++ "\n"))
  check ref "font dump: no declared family's face dumps as a mono face" (!hasStr dump "font mono.")

/-- `\setbeamertemplate{block begin}[default]` installs beamer's own pair
afresh, so an earlier `\addtobeamertemplate` goes with the template it
modified: lualatex sets the block as with no addition at all. -/
private def defaultOptionChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let head := "\\documentclass[10pt,aspectratio=169]{beamer}\n\\usetheme{moloch}\n"
  let body := "\\begin{document}\n\\begin{frame}[t]{Added}\nLead paragraph above.\n" ++
    "\\begin{block}{Alpha title words}\nBody words here.\n\\end{block}\n\\end{frame}\n\\end{document}\n"
  let added := head ++ "\\addtobeamertemplate{block begin}{}{\\bigskip}\n" ++
    "\\setbeamertemplate{block begin}[default]\n" ++ body
  let (_, outA, _) := layout fonts "added" added
  let (_, outP, _) := layout fonts "plain" (head ++ body)
  check ref "block template: a default reinstall drops the addition made before it"
    (pageInk outA == pageInk outP)

/-- A family declared in the body is skipped as the declaration it is, named
by the command the author wrote, and its command selects no family in
either artifact: the IR declares none, the HTML selects none, and the PDF
sets the words in the page's own face. -/
private def bodyFamilyChecks (ref : IO.Ref (List String)) : IO Unit := do
  let src := "\\documentclass[10pt,aspectratio=169]{beamer}\n\\usepackage{fontspec}\n" ++
    "\\begin{document}\n\\begin{frame}[t]{Body}\n\\newfontfamily\\probeA{Source Serif Pro}\n" ++
    "{\\probeA Serif words} plain words.\n\\end{frame}\n\\end{document}\n"
  let (doc, diags) := Elab.run "block-title-body-family.tex" src
  let w0340 := diags.filter (·.code == "W0340")
  check ref s!"body family: the declaration is named as the author's command ({w0340.map (·.message)})"
    (w0340.size == 1 && w0340.all fun d => d.subject == some "ctrl:newfontfamily" &&
      hasStr d.message "\\newfontfamily" && !hasStr d.message "\\fonts")
  check ref "body family: no family is declared" doc.fonts.families.isEmpty
  check ref "body family: the HTML selects no undeclared family"
    (!hasStr (HtmlDoc.emit {} doc).1 s!"var(--font-{Ir.familySlotBase})")
  let some (fs, doc) ← assemble doc | check ref "body family: the fixture fonts assemble" false
  let out := Layout.run (Layout.Geom.ofPage doc.page) fs none doc
  let page : Layout.PageOut := out.pages[0]?.getD {}
  let faces := match page.lines.find? fun l => hasStr (lineText l false) "Serif" with
    | some line => lineFaces fs line
    | none => #[]
  check ref s!"body family: the PDF sets the words in the page's own face ({faces})"
    (!faces.isEmpty && faces.all fun (face, _) => !face.startsWith "SourceSerifPro")

/-! ### A rule beside the whole block

lualatex, as above, ships `wholebar`: the capitals probe's rule beside the
title, from a template whose `block begin` also opens a box the body is set
in (`\setbox\B\vbox\bgroup`, on the depth of the line above,
`\prevdepth`, after a penalty), and whose `block end` closes the box, takes
the glue, kerns and penalties after its last line into a box of their own
(a macro calling itself, `\lastnodetype`, `\unskip`), sets the body back
unboxed, then a box of no size holding the body's part of the rule
(`\nointerlineskip`, `\moveleft`, `\vbox to\z@`, `\raisebox`) — a title's
rule's depth below the last baseline, as tall as the title's line's depth
and the box's height — and sets back the items and the last line's depth.
Over paragraphs, a list, a display alignment, a large title, a picture, an
untitled block, a title alone and a listing, every line stands where the
title's rule alone leaves it, and the rule runs from the title's capitals to
its depth below the block's last baseline (`Layout.edgeLinesFrom_abuts_exact`).
-/

def wholeBarSource : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n" ++
  "\\usetheme{moloch}\n" ++
  "\\definecolor{probeInk}{HTML}{1F2A44}\n" ++
  "\\definecolor{probeEdge}{HTML}{2E8B57}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setbeamercolor{probe edge}{bg=probeEdge}\n" ++
  "\\setbeamerfont{block title example}{size=\\large}\n" ++
  "\\setlength{\\parskip}{4pt}\n" ++
  "\\makeatletter\n" ++
  "\\newbox\\probe@title\n" ++
  "\\newbox\\probe@body\n" ++
  "\\newbox\\probe@trail\n" ++
  "\\newdimen\\probe@inset\n" ++
  "\\newdimen\\probe@wd\n" ++
  "\\newdimen\\probe@sep\n" ++
  "\\newdimen\\probe@titleinset\n" ++
  "\\newdimen\\probe@above\n" ++
  "\\newdimen\\probe@raise\n" ++
  "\\newdimen\\probe@last\n" ++
  "\\newcommand{\\probe@open}[1]{%\n" ++
  "  \\par\\vskip\\medskipamount\n" ++
  "  \\ifx\\insertblocktitle\\@empty\\else\n" ++
  "    \\setbox\\probe@title\\vbox{\\hsize\\linewidth\n" ++
  "      \\usebeamerfont*{block title#1}\\usebeamercolor[fg]{block title#1}%\n" ++
  "      \\strut\\insertblocktitle\\strut\\par\n" ++
  "      \\global\\probe@inset\\dimexpr(\\baselineskip-\\fontcharht\\font`H)/2\\relax}%\n" ++
  "    \\probe@titleinset\\probe@inset\n" ++
  "    \\probe@wd .3em\n" ++
  "    \\probe@sep .6em\n" ++
  "    \\noindent\\llap{{\\usebeamercolor[bg]{probe edge}%\n" ++
  "        \\vrule width \\probe@wd\n" ++
  "          height \\dimexpr\\ht\\probe@title+\\dp\\probe@title-\\parskip-\\probe@inset\\relax\n" ++
  "          depth \\probe@inset}%\n" ++
  "      \\hskip \\probe@sep}%\n" ++
  "    \\box\\probe@title\\par\\nobreak\n" ++
  "  \\fi\n" ++
  "  \\usebeamerfont{block body#1}\\usebeamercolor[fg]{block body#1}%\n" ++
  "  \\probe@above\\prevdepth\n" ++
  "  \\setbox\\probe@body\\vbox\\bgroup\\prevdepth\\probe@above\\nobreak}\n" ++
  "\\newcommand{\\probe@peel}{%\n" ++
  "  \\ifnum\\lastnodetype=11\n" ++
  "    \\skip@\\lastskip\\unskip\n" ++
  "    \\global\\setbox\\probe@trail\\vbox{\\vskip\\skip@\\unvbox\\probe@trail}\\probe@peel\n" ++
  "  \\else\\ifnum\\lastnodetype=12\n" ++
  "    \\dimen@\\lastkern\\unkern\n" ++
  "    \\global\\setbox\\probe@trail\\vbox{\\kern\\dimen@\\unvbox\\probe@trail}\\probe@peel\n" ++
  "  \\else\\ifnum\\lastnodetype=13\n" ++
  "    \\count@\\lastpenalty\\unpenalty\n" ++
  "    \\global\\setbox\\probe@trail\\vbox{\\penalty\\count@\\unvbox\\probe@trail}\\probe@peel\n" ++
  "  \\fi\\fi\\fi}\n" ++
  "\\newcommand{\\probe@close}{%\n" ++
  "  \\par\n" ++
  "  \\global\\probe@last\\prevdepth\n" ++
  "  \\global\\setbox\\probe@trail\\box\\voidb@x\n" ++
  "  \\probe@peel\n" ++
  "  \\egroup\n" ++
  "  \\ifx\\insertblocktitle\\@empty\n" ++
  "    \\unvbox\\probe@body\n" ++
  "  \\else\n" ++
  "    \\advance\\probe@above\\ht\\probe@body\n" ++
  "    \\probe@raise\\probe@last\n" ++
  "    \\ifdim\\probe@raise<\\z@ \\probe@raise\\z@ \\fi\n" ++
  "    \\advance\\probe@raise-\\probe@titleinset\n" ++
  "    \\unvbox\\probe@body\n" ++
  "    \\nointerlineskip\n" ++
  "    \\moveleft\\dimexpr\\probe@wd+\\probe@sep\\relax\\vbox to\\z@{\\vss\\hbox{{\\usebeamercolor[bg]{probe edge}%\n" ++
  "      \\raisebox{\\probe@raise}[\\z@][\\z@]{\\vrule width \\probe@wd height \\probe@above depth \\z@}}}}%\n" ++
  "  \\fi\n" ++
  "  \\unvbox\\probe@trail\n" ++
  "  \\prevdepth\\probe@last\n" ++
  "  \\vskip\\smallskipamount}\n" ++
  "\\defbeamertemplate*{block begin}{probe}{\\probe@open{}}\n" ++
  "\\defbeamertemplate*{block end}{probe}{\\probe@close}\n" ++
  "\\defbeamertemplate*{block example begin}{probe}{\\probe@open{ example}}\n" ++
  "\\defbeamertemplate*{block example end}{probe}{\\probe@close}\n" ++
  "\\makeatother\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[t]{Paragraphs}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Alpha title words}\n" ++
  "Body words here.\n" ++
  "\\end{block}\n" ++
  "\\begin{block}{Delta first title line\\\\Delta second title line}\n" ++
  "First body paragraph.\n" ++
  "\n" ++
  "Second body paragraph.\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Lists and displays}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Gamma list title}\n" ++
  "\\begin{itemize}\n" ++
  "\\item First listed item.\n" ++
  "\\item Second listed item.\n" ++
  "\\end{itemize}\n" ++
  "\\end{block}\n" ++
  "\\begin{block}{Omega display title}\n" ++
  "\\begin{align*}\n" ++
  "  a &= b + c\\\\\n" ++
  "  d &= e\n" ++
  "\\end{align*}\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t]{Sizes and pictures}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{exampleblock}{Epsilon large title}\n" ++
  "Third body words.\n" ++
  "\\end{exampleblock}\n" ++
  "\\begin{block}{Eta picture title}\n" ++
  "\\begin{tikzpicture}\\draw[fill=gray] (0,0) rectangle (2,0.8);\\end{tikzpicture}\n" ++
  "\\end{block}\n" ++
  "\\begin{block}{}\n" ++
  "Untitled body words.\n" ++
  "\\end{block}\n" ++
  "\\begin{block}{Kappa title alone}\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\begin{frame}[t,fragile]{Listings}\n" ++
  "Lead paragraph above.\n" ++
  "\\begin{block}{Zeta listing title}\n" ++
  "\\begin{verbatim}\n" ++
  "plain listing line\n" ++
  "second listing line\n" ++
  "\\end{verbatim}\n" ++
  "\\end{block}\n" ++
  "Trailing paragraph below.\n" ++
  "\\end{frame}\n" ++
  "\\end{document}\n"

/-- lualatex's distances on the whole-bar probe, in thousandths of a point,
per page: the rule beside each block from its title's first baseline and to
the block's last — one rule, where TeX's two parts meet — and the lines
around it. -/
private def measuredWhole : Array (Nat × Mark × Mark × Int) := #[
  (0, .base "Lead paragraph above.", .base "Alpha title words", 25802),
  (0, .top edgeColor 0, .base "Alpha title words", 9569),
  (0, .base "Alpha title words", .base "Body words here.", 16000),
  (0, .base "Body words here.", .bottom edgeColor 0, 2431),
  (0, .top edgeColor 1, .base "Delta first title line", 9569),
  (0, .base "Delta first title line", .base "Delta second title line", 12000),
  (0, .base "Delta second title line", .base "First body paragraph.", 16000),
  (0, .base "First body paragraph.", .base "Second body paragraph.", 16000),
  (0, .base "Second body paragraph.", .bottom edgeColor 1, 2431),
  (0, .base "Second body paragraph.", .base "Trailing paragraph below.", 19000),
  (1, .top edgeColor 0, .base "Gamma list title", 9569),
  (1, .base "Gamma list title", .base "• First listed item.", 19000),
  (1, .base "• First listed item.", .base "• Second listed item.", 15000),
  (1, .base "• Second listed item.", .bottom edgeColor 0, 2431),
  (1, .top edgeColor 1, .base "Omega display title", 9569),
  (2, .top edgeColor 0, .base "Epsilon large title", 11283),
  (2, .base "Epsilon large title", .base "Third body words.", 16000),
  (2, .base "Third body words.", .bottom edgeColor 0, 2717),
  (2, .top edgeColor 1, .base "Eta picture title", 9569),
  (2, .top edgeColor 2, .base "Kappa title alone", 9569),
  (2, .base "Kappa title alone", .bottom edgeColor 2, 2431),
  (3, .top edgeColor 0, .base "Zeta listing title", 9569),
  (3, .base "Zeta listing title", .base "plain listing line", 24000),
  (3, .base "plain listing line", .base "second listing line", 12000),
  (3, .base "second listing line", .bottom edgeColor 0, 2431)]

/-- The whole-bar probe with its rule beside the title alone: no box around
the body, and a close of the skip below only. -/
private def titleBarOf (src : String) : String :=
  src
    |>.replace ("  \\probe@above\\prevdepth\n" ++
        "  \\setbox\\probe@body\\vbox\\bgroup\\prevdepth\\probe@above\\nobreak}\n") "}\n"
    |>.replace ("\\newcommand{\\probe@close}{%\n" ++
        "  \\par\n" ++
        "  \\global\\probe@last\\prevdepth\n" ++
        "  \\global\\setbox\\probe@trail\\box\\voidb@x\n" ++
        "  \\probe@peel\n" ++
        "  \\egroup\n" ++
        "  \\ifx\\insertblocktitle\\@empty\n" ++
        "    \\unvbox\\probe@body\n" ++
        "  \\else\n" ++
        "    \\advance\\probe@above\\ht\\probe@body\n" ++
        "    \\probe@raise\\probe@last\n" ++
        "    \\ifdim\\probe@raise<\\z@ \\probe@raise\\z@ \\fi\n" ++
        "    \\advance\\probe@raise-\\probe@titleinset\n" ++
        "    \\unvbox\\probe@body\n" ++
        "    \\nointerlineskip\n" ++
        "    \\moveleft\\dimexpr\\probe@wd+\\probe@sep\\relax\\vbox to\\z@{\\vss\\hbox{{\\usebeamercolor[bg]{probe edge}%\n" ++
        "      \\raisebox{\\probe@raise}[\\z@][\\z@]{\\vrule width \\probe@wd height \\probe@above depth \\z@}}}}%\n" ++
        "  \\fi\n" ++
        "  \\unvbox\\probe@trail\n" ++
        "  \\prevdepth\\probe@last\n" ++
        "  \\vskip\\smallskipamount}\n")
      "\\newcommand{\\probe@close}{\\par\\vskip\\smallskipamount}\n"

/-- A line's run whose letters are `text`: its baseline on the page, the
line's lifted by the run's own. -/
private def runBase (p : Layout.PageOut) (text : String) : Option Dim.Sp :=
  p.lines.findSome? fun l => l.segs.findSome? fun s => match s with
    | .run _ _ _ _ glyphs _ _ _ raise _ _ =>
      if String.ofList (glyphs.toList.map (·.2.1)) == text then some (l.y - raise) else none
    | _ => none

/-- **A rule beside the whole block stands where lualatex stands it**: read
off the whole-bar probe as one rule beside each titled block
(`Ir.BlockSpan.whole`), from its title's capitals — the title's rule's place
— to its depth below the block's last baseline: a paragraph's, a list
item's, a display alignment's last row's, a picture's, a listing's last
line's, the title's own where the body is empty; none beside the untitled
block; and every line where the title's rule alone leaves it. -/
private def wholeBarChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let fs ← mathSetOf fonts
  let (geom, out, diags) := layout fs "wholebar" wholeBarSource
  check ref s!"whole bar: the probe reads without loss ({(diags ++ out.diags).filter (·.severity != .note) |>.map (·.message)})"
    ((diags ++ out.diags).all (·.severity == .note))
  let (doc, _) := Elab.run "block-template-wholebar.tex" wholeBarSource
  let edges := ((Ir.blockShapeOf doc.styles .block).map (·.edges)).getD #[]
  check ref s!"whole bar: the plain kind's rule stands beside the whole block, by its lines ({edges.map (·.span == .whole)})"
    (edges.size == 1 && edges.all fun e => e.span == .whole && e.hang &&
      e.reach == .lines Ir.BlockMetric.halfLeading.neg Ir.BlockMetric.halfLeading)
  for (page, a, b, want) in measuredWhole do
    match out.pages[page]?.bind fun p => (markAt geom p a).bind fun ya => (markAt geom p b).map (· - ya) with
    | some d =>
      check ref s!"whole bar page {page}: {want} (lualatex) got {milliOf d}"
        ((milliOf d - want).natAbs ≤ tolerance.toNat)
    | none => check ref s!"whole bar page {page}: the marks for {want} ship" false
  let rules := out.pages.map fun p => (p.fills.filter (·.color == edgeColor)).size
  check ref s!"whole bar: one rule per titled block, none beside the untitled one ({rules})"
    (rules == #[2, 2, 3, 1])
  -- The display alignment's rule ends its depth below the last row, which
  -- TeX sets as a line of its own: here a row of the display's one line.
  let half : Dim.Sp := 2431
  match out.pages[1]?, out.pages[1]?.bind fun p => runBase p "𝑑" with
  | some p, some row =>
    match ruleOf p edgeColor 1 with
    | some bar =>
      let d := milliOf (bar.y + bar.h - row)
      check ref s!"whole bar: the display's rule ends below its last row ({d})"
        ((d - half).natAbs ≤ tolerance.toNat)
    | none => check ref "whole bar: the display's rule ships" false
  | _, _ => check ref "whole bar: the display's last row ships" false
  -- A grid inside the last row's cell is a box of that row's: the rule
  -- still ends below the row.
  let nested := wholeBarSource.replace "  d &= e\n" "  d &= \\begin{gathered} x \\\\ y \\end{gathered}\n"
  check ref "whole bar: the nested-grid probe differs from the probe" (nested != wholeBarSource)
  let (_, nout, _) := layout fs "wholebar-nested" nested
  match nout.pages[1]?, nout.pages[1]?.bind fun p => runBase p "𝑑" with
  | some p, some row =>
    match ruleOf p edgeColor 1 with
    | some bar =>
      let d := milliOf (bar.y + bar.h - row)
      check ref s!"whole bar: a display whose last row holds a grid ends its rule below that row ({d})"
        ((d - half).natAbs ≤ tolerance.toNat)
    | none => check ref "whole bar: the nested-grid display's rule ships" false
  | _, _ => check ref "whole bar: the nested-grid display's last row ships" false
  -- The picture stands on the baseline, its lower edge there.
  match out.pages[2]? with
  | some p =>
    match ruleOf p edgeColor 1, p.inks[0]? with
    | some bar, some k =>
      let bottom := k.claims.foldl (fun m b => max m b.2.2) k.place.dy
      let d := milliOf (bar.y + bar.h - bottom)
      check ref s!"whole bar: the picture's rule ends below the picture's baseline ({d})"
        ((d - half).natAbs ≤ 250)
    | _, _ => check ref "whole bar: the picture and its rule ship" false
  | none => check ref "whole bar: the picture's page ships" false
  -- Every line stands where the title's rule alone leaves it.
  let titled := titleBarOf wholeBarSource
  check ref "whole bar: the title-only probe differs from the probe" (titled != wholeBarSource)
  let (_, alone, _) := layout fs "wholebar-title" titled
  let ys (o : Layout.Out) := o.pages.map fun p => p.lines.map fun l => (l.y, lineText l false)
  check ref "whole bar: every line stands where the title's rule alone leaves it" (ys out == ys alone)
  check ref "whole bar: the title-only probe draws the title's rule alone"
    ((alone.pages.map fun p => (p.fills.filter (·.color == edgeColor)).size) == #[2, 2, 3, 1])

/-- **The web page draws the rule beside the whole block on the block's
section** (`HtmlDoc.blockShapeCss`): from its title's part's top, where the
title's rule stands below the header's first line box, to its depth below
the body's last line box's baseline — a body paragraph's unless the section
says how far its last line box reaches (a listing's, its mono face at its
size leaded at its line height); none for an untitled block. The depth is
the page's: the PDF's rule ends that far below the block's last baseline. -/
private def wholeBarHtmlChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let fs ← mathSetOf fonts
  let (doc, _) := Elab.run "block-template-wholebar.tex" wholeBarSource
  let geom := Layout.Geom.ofPage doc.page
  let cfg : HtmlDoc.Config := { blockTitleRule := Layout.blockTitleRule geom fs doc.styles
                                blockLastBelow := Layout.blockLastBelow geom fs }
  let (head, body, _) := HtmlDoc.emitTree cfg doc
  let sheet := treeCssList "" (head.toList ++ body.toList)
  let sel := "section.block-shaped.block-block"
  let rule := (cssRuleOf sheet s!"{sel}::before").getD ""
  check ref s!"whole bar HTML: the section draws the rule ({rule})"
    (hasStr rule "position: absolute" && hasStr rule "var(--block-last-below, " &&
      hasStr rule "width: 0.3em" && hasStr rule "left: calc(0rem - 0.6em - 0.3em)")
  check ref "whole bar HTML: the header draws no rule of its own"
    ((cssRuleOf sheet s!"{sel} > header::before").isNone)
  check ref "whole bar HTML: an untitled block draws none"
    ((cssRuleOf sheet s!"{sel}:not(:has(> header))::before").any (hasStr · "content: none"))
  let place := Layout.blockTitleRule geom fs doc.styles .block
    (.lines Ir.BlockMetric.halfLeading.neg Ir.BlockMetric.halfLeading)
  let (_, out, _) := layout fs "wholebar" wholeBarSource
  match place, out.pages[0]? with
  | some p, some page =>
    match ruleOf page edgeColor 0, lineOf page "Body words here." with
    | some bar, some last =>
      let pdf := bar.y + bar.h - last.y
      check ref s!"whole bar HTML: the section's rule ends the page's depth below the last baseline ({p.depth} against {pdf})"
        ((p.depth - pdf).natAbs ≤ 2 * Dim.spPerPt / 1000)
      let stage (v : Int) := HtmlDoc.blockShapeLength doc { width := .ofSp v }
      check ref s!"whole bar HTML: a paragraph's line box ends the rule by default ({rule})"
        (hasStr rule s!"var(--block-last-below, {stage p.bodyBelow}) - {stage p.depth})")
    | _, _ => check ref "whole bar HTML: the page's rule and its last line ship" false
  | _, _ => check ref "whole bar HTML: the driver places the rule" false
  -- The listing's section says how far its last line box reaches.
  let below := Layout.blockLastBelow geom fs
  let listings := Ir.foldBlocks (fun acc b => match b with
    | .titled _ _ kb => match kb.back? with
      | some (.verbatim ..) => acc.push kb.back?
      | _ => acc
    | _ => acc) (fun acc _ => acc) #[] doc.body
  check ref s!"whole bar HTML: one block ends on a listing ({listings.size})" (listings.size == 1)
  match listings[0]?.bind below with
  | some v =>
    let said := s!"--block-last-below: {HtmlDoc.blockShapeLength doc { width := .ofSp v }};"
    -- The section holding the listing.
    let holding := (elemNodesList (· == "section") #[] body.toList).filterMap fun n => match n with
      | .elem _ attrs kids =>
        if kids.any (fun k => k matches .elem "pre" _ _) then (attrs.find? (·.1 == "style")).map (·.2)
        else none
      | .text _ | .style _ | .script .. => none
    check ref s!"whole bar HTML: the listing's section says how far its last line box reaches ({said}, {holding})"
      (holding.size == 1 && holding.all (hasStr · said))
  | none => check ref "whole bar HTML: the driver measures the listing's last line" false
  -- Every such section says its own end, so a block inside another reads
  -- none of the enclosing one's; a body ending in a block ends past that
  -- block's skip below.
  let inner := wholeBarSource.replace "Body words here.\n"
    "Body words here.\n\\begin{block}{Inner title words}\nInner body words.\n\\end{block}\n"
  check ref "whole bar HTML: the nested-block probe differs from the probe" (inner != wholeBarSource)
  let (idoc, _) := Elab.run "block-template-wholebar-inner.tex" inner
  let (_, ibody, _) := HtmlDoc.emitTree cfg idoc
  let styles := (elemAttrsList (· == "section") #[] ibody.toList).filterMap fun (_, attrs) =>
    if attrs.any (fun (k, v) => k == "class" && hasStr v "block-shaped") then
      (attrs.find? (·.1 == "style")).map (·.2) else none
  check ref s!"whole bar HTML: every titled shaped section says its own end ({styles})"
    (styles.size ≥ 2 && styles.all (hasStr · "--block-last-below: "))
  check ref s!"whole bar HTML: a block ending in a block ends past that block's skip below ({styles})"
    (styles.any (hasStr · "--block-last-below: calc("))
  -- That skip as the section pads it, its font's part and all.
  let emInner := inner.replace "  \\vskip\\smallskipamount}\n" "  \\vskip 1em}\n"
  let (edoc, _) := Elab.run "block-template-wholebar-inner-em.tex" emInner
  let (_, ebody, _) := HtmlDoc.emitTree cfg edoc
  let estyles := (elemAttrsList (· == "section") #[] ebody.toList).filterMap fun (_, attrs) =>
    if attrs.any (fun (k, v) => k == "class" && hasStr v "block-shaped") then
      (attrs.find? (·.1 == "style")).map (·.2) else none
  check ref s!"whole bar HTML: a skip below in ems ends the enclosing block's rule an em past the inner block ({estyles})"
    (emInner != inner && estyles.any (hasStr · "--block-last-below: calc(1em + "))

/-- **The reading holds a template that sets the body back to what TeX sets**:
each probe below breaks one of the template's settings — the items the body
ends on left in its box, below the rule (no peel); the depth below its last
line not set back; the box opened on a fresh box's depth rather than the
line above's; its list opened on no penalty, so its first paragraph spends
no `\parskip`; the rule beside the body moved off the title's rule, or
reaching less than to it — and is named once, for its reading, its blocks
keeping beamer's default pair. The native spelling refuses a rule beside the
whole block by its lines beside a box holding title and body, or inside the
line. -/
private def wholeBarReadingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let src := wholeBarSource
  let cases : List (String × String × String) :=
    [("unpeeled", src.replace "  \\probe@peel\n  \\egroup\n" "  \\egroup\n",
       "a rule beside the body standing below the items the body ends on"),
     ("unrestored", src.replace "  \\prevdepth\\probe@last\n  \\vskip\\smallskipamount}" "  \\vskip\\smallskipamount}",
       "a body set back without the depth below its last line after it"),
     ("fresh", src.replace "\\vbox\\bgroup\\prevdepth\\probe@above\\nobreak}" "\\vbox\\bgroup\\nobreak}",
       "a body set back on another depth than the list it joins stood on"),
     ("unopened", src.replace "\\vbox\\bgroup\\prevdepth\\probe@above\\nobreak}" "\\vbox\\bgroup\\prevdepth\\probe@above}",
       "a body set back without the \\parskip its list spends"),
     ("moved", src.replace "\\moveleft\\dimexpr\\probe@wd+\\probe@sep\\relax" "\\moveleft\\dimexpr\\probe@wd\\relax",
       "a rule beside the body at another place, width or paint than its title's"),
     ("short", src.replace "    \\advance\\probe@above\\ht\\probe@body\n" "",
       "a rule beside the body reaching elsewhere than the title's rule"),
     -- Two rounds of one peel take two items off, not every one.
     ("unrolled", src.replace "\\probe@peel\n  \\else\\ifnum" "\n  \\else\\ifnum"
         |>.replace "\\probe@trail}\\probe@peel\n" "\\probe@trail}\n"
         |>.replace "  \\probe@peel\n  \\egroup\n" "  \\probe@peel\\probe@peel\n  \\egroup\n",
       "a rule beside the body standing below the items the body ends on"),
     -- A trail set in the body's group is lost where the group ends.
     ("local", src.replace "\\global\\setbox\\probe@trail\\vbox{" "\\setbox\\probe@trail\\vbox{",
       "the items the body ends on set back otherwise than in their order, every one"),
     -- A space before the rule moves it off the title's.
     ("spaced", src.replace "\\vbox to\\z@{\\vss\\hbox{{" "\\vbox to\\z@{\\vss\\hbox{ {",
       "a box beside the body other than a rule standing on its last line"),
     -- A close that takes the body's last item off moves what follows.
     ("unskipped", (titleBarOf src).replace "\\newcommand{\\probe@close}{\\par\\vskip\\smallskipamount}"
         "\\newcommand{\\probe@close}{\\par\\unskip\\vskip\\smallskipamount}",
       "the items the body ends on set back otherwise than in their order, every one"),
     -- A line end after a brace is TeX's space, before the rule.
     ("line end", src.replace "\\vbox to\\z@{\\vss\\hbox{{" "\\vbox to\\z@{\\vss\\hbox{\n{",
       "a box beside the body other than a rule standing on its last line"),
     -- So is a macro's text that is one.
     ("macro line end", src.replace "\\makeatother\n\\begin{document}"
         "\\newcommand{\\probe@lead}{\n}\n\\makeatother\n\\begin{document}"
         |>.replace "\\vbox to\\z@{\\vss\\hbox{{" "\\vbox to\\z@{\\vss\\hbox{\\probe@lead{",
       "a box beside the body other than a rule standing on its last line"),
     -- The starred colour use without a channel sets no colour last, and
     -- keeps the space after it.
     ("starred", src.replace "{\\usebeamercolor[bg]{probe edge}%\n      \\raisebox"
         "{\\usebeamercolor*{probe edge} \\usebeamercolor[bg]{probe edge}%\n      \\raisebox",
       "a box beside the body other than a rule standing on its last line"),
     -- A peel run twice through a macro the expansion leaves for the run
     -- takes two items off, not every one.
     ("forward", src.replace "\\newcommand{\\probe@peel}{%\n"
         "\\newcommand{\\probe@peel}{\\probe@peelone\\probe@peelone}\n\\newcommand{\\probe@peelone}{%\n"
         |>.replace "\\probe@trail}\\probe@peel\n" "\\probe@trail}\n",
       "a rule beside the body standing below the items the body ends on")]
  for (name, variant, why) in cases do
    check ref s!"whole bar {name}: the refused probe differs from the probe" (variant != src)
    let (doc, diags) := Elab.run s!"block-template-wholebar-{name}.tex" variant
    let named := diags.filter fun d => d.code == "W0110" && d.subject == some "beamer:template:block begin"
    check ref s!"whole bar {name}: the template is named once, for its reading ({named.map (·.message)})"
      (named.size == 1 && named.all (hasStr ·.message why))
    check ref s!"whole bar {name}: its blocks keep the default pair"
      (((doc.styles.find? "block").bind (·.shape)).isNone)
  -- A template runs as TeX runs it at each block, against the macros and
  -- flags in force where the body begins: a flag the preamble sets after
  -- the templates, a macro's optional argument's default, a comment's line
  -- end, glue after the rule.
  let (plain, _) := Elab.run "block-template-wholebar.tex" src
  let shape := (plain.styles.find? "block").bind (·.shape)
  let shapeOf (name variant : String) := ((Elab.run s!"block-template-wholebar-{name}.tex" variant).1.styles.find?
    "block").bind (·.shape)
  let gapped := src.replace "\\makeatletter\n" "\\makeatletter\n\\newif\\ifprobe@gap\\probe@gaptrue\n"
    |>.replace "  \\par\\vskip\\medskipamount\n  \\ifx\\insertblocktitle"
      "  \\par\\vskip\\medskipamount\\ifprobe@gap\\vskip\\bigskipamount\\fi\n  \\ifx\\insertblocktitle"
  let decided : List (String × String) :=
    [("flagged", src.replace "\\makeatletter\n" "\\makeatletter\n\\newif\\ifprobe@gap\\probe@gaptrue\n"
        |>.replace "  \\par\\vskip\\medskipamount\n  \\ifx\\insertblocktitle"
          "  \\par\\vskip\\medskipamount\\ifprobe@gap\\else\\vskip\\bigskipamount\\fi\n  \\ifx\\insertblocktitle"),
     ("late flag", gapped.replace "\\makeatother\n\\begin{document}"
        "\\probe@gapfalse\n\\makeatother\n\\begin{document}"),
     ("optional", src.replace "\\makeatletter\n"
          "\\makeatletter\n\\newcommand{\\probe@gap}[1][\\medskipamount]{\\vskip#1}\n"
        |>.replace "  \\par\\vskip\\medskipamount\n  \\ifx\\insertblocktitle"
          "  \\par\\probe@gap\n  \\ifx\\insertblocktitle"),
     ("commented", src.replace "\\vbox to\\z@{\\vss\\hbox{{" "\\vbox to\\z@{\\vss\\hbox{%\n{"),
     ("glue after", src.replace "depth \\z@}}}}%" "depth \\z@}} }}%")]
  for (name, variant) in decided do
    check ref s!"whole bar {name}: the decided probe differs from the probe" (variant != src)
    let (doc, diags) := Elab.run s!"block-template-wholebar-{name}.tex" variant
    check ref s!"whole bar {name}: the template reads as the probe's ({diags.filter (·.code == "W0110") |>.map (·.message)})"
      (shape.isSome && (doc.styles.find? "block").bind (·.shape) == shape)
  -- The flag decides: set where the body begins, its arm is taken.
  check ref "whole bar: a flag set where the body begins takes its arm"
    (shape.isSome && (shapeOf "gapped" gapped).isSome && shapeOf "gapped" gapped != shape)
  -- A template macro the preamble redefines after the templates runs as
  -- redefined, as TeX runs it at each block.
  let closeHead := "\\newcommand{\\probe@close}{%\n"
  let closeFoot := "  \\vskip\\smallskipamount}\n"
  let closeBody := (((src.splitOn closeHead)[1]?.getD "").splitOn closeFoot)[0]?.getD ""
  let renewed := src.replace "\\makeatother\n\\begin{document}"
    ("\\renewcommand{\\probe@close}{%\n" ++ closeBody ++ "  \\vskip\\bigskipamount}\n" ++
      "\\makeatother\n\\begin{document}")
  let written := src.replace closeFoot "  \\vskip\\bigskipamount}\n"
  check ref "whole bar: the redefined and the rewritten probes differ from the probe"
    (!closeBody.isEmpty && renewed != src && written != src)
  check ref "whole bar: a template macro redefined after the templates runs as redefined"
    ((shapeOf "renewed" renewed).isSome && shapeOf "renewed" renewed == shapeOf "written" written &&
      shapeOf "written" written != shape)
  -- A flag the body changes before a block runs the templates otherwise
  -- there than where the body began: named, the default pair standing.
  let drifted := gapped.replace "Lead paragraph above.\n" "\\probe@gapfalse\nLead paragraph above.\n"
  let (ddoc, dd) := Elab.run "block-template-wholebar-drift.tex" drifted
  let named := dd.filter fun d => d.code == "W0110" && d.subject == some "beamer:template:block begin"
  check ref s!"whole bar: a flag the body changes before a block is named ({named.map (·.message)})"
    (drifted != gapped && named.size == 1 && named.all (hasStr ·.message "changes \\ifprobe@gap"))
  check ref "whole bar: the blocks the body's flag changes keep the default pair"
    (((ddoc.styles.find? "block").bind (·.shape)).isNone)
  let native (edge : String) (whole : String) : String :=
    "\\documentclass{slides}\n\\palette{ accent = #123456 }\n\\style{block}{ shape = " ++
      "{ title = box strut parskip, untitled = {}" ++ whole ++ ", edge = { span = whole, side = left, " ++
      "width = 0.3em, sep = 0.6em, " ++ edge ++ ", color = accent, height = -0.5lh + 0.5cap, " ++
      "depth = 0.5lh - 0.5cap } } }\n\\begin{document}\n\\end{document}\n"
  for (name, src, why) in [("boxed", native "hang = true" ", whole = parskip",
        "beside a box holding title and body"),
      ("inside", native "hang = false" "", "inside its line")] do
    let (_, nd) := Elab.run s!"block-shape-whole-{name}.tex" src
    check ref s!"whole bar: the native spelling refuses lines beside the whole block {name} ({nd.map (·.message)})"
      (nd.any fun d => d.code == "E0323" && hasStr d.message why)

/-- **A block template's own macro names no loss of its own**
(`Compat.templateReach`, the premise beside the settled and translated
definitions): the whole-bar probe's macros, which only its templates call,
raise nothing; the probe whose text also uses one of them, where the
conditional pass expands the use, names its loss at that use. -/
private def templateCodeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let (_, clean) := Elab.run "block-template-wholebar.tex" wholeBarSource
  check ref s!"template code: the probe's own macros raise nothing ({clean.filter (·.severity != .note) |>.map (·.message)})"
    (clean.all (·.severity == .note))
  let used := wholeBarSource.replace "Body words here.\n" "Body words here.\\makeatletter\\probe@peel\\makeatother\n"
  check ref "template code: the probe using a template macro differs from the probe" (used != wholeBarSource)
  let (_, ud) := Elab.run "block-template-wholebar-used.tex" used
  check ref s!"template code: a template macro the text uses names its loss there ({ud.filter (·.severity != .note) |>.map (·.message)})"
    (ud.any fun d => d.code == "W0104" && hasStr d.message "probe@peel")
  -- Named elsewhere in the preamble, outside the templates and its own
  -- definition, it is no template's alone: its definition names its loss.
  let elsewhere := wholeBarSource.replace "\\makeatother\n"
    "\\newcommand{\\probe@other}{\\probe@peel}\n\\makeatother\n"
  check ref "template code: the probe naming a template macro elsewhere differs from the probe"
    (elsewhere != wholeBarSource)
  let (_, ed) := Elab.run "block-template-wholebar-elsewhere.tex" elsewhere
  -- The loss named at the macro's own definition, where its settled text
  -- reads its call of itself.
  let lines := (elsewhere.splitOn "\n").zipIdx
  let first := ((lines.find? fun (l, _) => l.startsWith "\\newcommand{\\probe@peel}").map (·.2 + 1)).getD 0
  let past := ((lines.find? fun (l, i) => i + 1 > first && l.startsWith "\\newcommand{\\probe@close}").map
    (·.2 + 1)).getD 0
  let atDefinition (d : Diag) : Bool := d.span.any fun sp => first ≤ sp.pos.line && sp.pos.line < past
  check ref s!"template code: a template macro the preamble names elsewhere names its definition's loss ({ed.filter (·.severity != .note) |>.map fun d => (d.message, d.span.map (·.pos.line))})"
    (ed.any fun d => d.code == "W0104" && hasStr d.message "probe@peel" && atDefinition d)
  -- And the probe's own definitions, every one of them, name nothing.
  let srcLines := (wholeBarSource.splitOn "\n").zipIdx
  let opens := ((srcLines.find? fun (l, _) => l.startsWith "\\newcommand{\\probe@open}").map (·.2 + 1)).getD 0
  let ends := ((srcLines.find? fun (l, _) => l.startsWith "\\defbeamertemplate").map (·.2 + 1)).getD 0
  check ref s!"template code: the probe's own definitions name nothing at their lines ({opens}..{ends})"
    (opens > 0 && ends > opens && clean.all fun d => d.severity == .note ||
      !(d.span.any fun sp => opens ≤ sp.pos.line && sp.pos.line < ends))

/-- **A line end the lexer leaves out beside a brace stays on the brace**
(`Pos.openEol`, `Pos.closeEol`), and the template reader sets back the
space TeX reads there (`BlockTemplate.flatten`): after an opening brace,
and before a closing one past anything but a control word; a comment's
line end is none, and the document's own raws keep none. -/
private def braceEolChecks (ref : IO.Ref (List String)) : IO Unit := do
  let raws (src : String) : Array Parse.Raw := (Parse.parse "eol.tex" (Lex.lex "eol.tex" src).1).1
  let flat (src : String) : Array LeanTex.Core.BlockTemplate.Tok :=
    LeanTex.Core.BlockTemplate.flatten (raws src)
  for (src, want) in [("{\n x}", #[LeanTex.Core.BlockTemplate.Tok.bg, .space, .word "x", .eg]),
      ("{x\n}", #[.bg, .word "x", .space, .eg]),
      ("{{x}\n}", #[.bg, .bg, .word "x", .eg, .space, .eg]),
      ("{\\relax\n}", #[.bg, .ctrl "relax", .eg]),
      ("{%\n x}", #[.bg, .word "x", .eg]),
      ("{x%\n}", #[.bg, .word "x", .eg])] do
    check ref s!"brace line ends: {repr src} reads as TeX's tokens ({repr (flat src)})" (flat src == want)
  check ref "brace line ends: the document's own raws keep no space there"
    ((raws "{\n x}").toList matches [.group #[.word "x" _] _] &&
      (raws "{x\n}").toList matches [.group #[.word "x" _] _])

def checks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  pageChecks ref fonts
  voidedChecks ref fonts
  channelChecks ref fonts
  htmlChecks ref
  htmlSkipChecks ref
  projectionChecks ref
  readingChecks ref fonts
  blockStyleKeyChecks ref fonts
  familyChecks ref
  parentChecks ref
  provideChecks ref
  dumpChecks ref
  defaultOptionChecks ref fonts
  bodyFamilyChecks ref
  chainChecks ref fonts
  emptyBoxHtmlChecks ref
  capitalChecks ref fonts
  capitalHtmlChecks ref fonts
  capitalReadingChecks ref
  capitalRegisterChecks ref
  wholeBarChecks ref fonts
  wholeBarHtmlChecks ref fonts
  wholeBarReadingChecks ref
  templateCodeChecks ref
  braceEolChecks ref

end Tests.BlockTemplate
