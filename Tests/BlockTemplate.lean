module

public import Tests.Support
public import LeanTex.Cli.FontAssembly

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

private def edgeColor : Ir.Color := { r := 0x2E, g := 0x8B, b := 0x57 }

private def edgeTwoColor : Ir.Color := { r := 0x8B, g := 0x2E, b := 0x57 }

/-- The moloch bundle's alerted ink, the right-hand rule's colour. -/
private def alertColor : Ir.Color :=
  (((Theme.find? "moloch").map (·.palette)).bind (·.find? "alert")).getD Ir.Color.black

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
  ("plainsized", 1, .base "Fifth body words.", .base "Trailing paragraph below.", 15000)]

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
  ("boxed", 1, .edge, .lineX "Delta title words", 0)]

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
   ("boxed", boxedSource), ("sized", sizedSource), ("plainsized", plainSizedSource)]

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
          | some n => s!"var(--{n}, {HtmlDoc.cssColor e.color})"
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
                     color := { r := 0x12, g := 0x34, b := 0x56 }, name := some "accent" }] })]
  for (src, want) in reads do
    let doc := (Elab.run "block-shape.tex"
      ("\\documentclass{slides}\n\\palette{ accent = #123456 }\n\\style{block}{ shape = " ++ src ++
        " }\n\\begin{document}\n\\end{document}\n")).1
    -- The colour is the palette's own reading of its entry.
    let accent := (doc.palette.find? "accent").getD Ir.Color.black
    let want := { want with edges := want.edges.map fun e => { e with color := accent } }
    check ref s!"block template: the native shape {src} reads back"
      (((doc.styles.find? "block").bind (·.shape)) == some want)

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

/-- A page's ink, as a comparison reads it: every line's place and letters,
every fill's rectangle and colour. -/
private def pageInk (out : Layout.Out) : Array String :=
  out.pages.flatMap fun p =>
    (p.lines.map fun l => s!"line {l.x} {l.y} {lineText l false}") ++
      p.fills.map fun f => s!"fill {f.x} {f.y} {f.w} {f.h} {f.color.r} {f.color.g} {f.color.b}"

/-- The style keys a beamer block reads are its title's `font` and its
template's `shape`; every other key it is given is named once (W0104) where
it is declared, and both artifacts ship exactly what they ship without it,
for each of the three kinds, templated or in beamer's default blocks. -/
private def blockStyleKeyChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let unread := ["before", "after", "color", "rule", "align", "indent"]
  for (probe, src) in [("hanging", hanging), ("plainsized", plainSizedSource)] do
    for el in Ir.blockStyleElements do
      let line := s!"\\style\{{el}}\{ before = 30pt, after = 30pt, color = red, rule = blue, \
align = center, indent = 2em }\n"
      let styled := src.replace "\\begin{document}" (line ++ "\\begin{document}")
      check ref s!"block style {probe} {el}: the styled probe differs from the probe" (styled != src)
      let (_, outA, diagsA) := layout fonts probe src
      let (_, outB, diagsB) := layout fonts probe styled
      for key in unread do
        check ref s!"block style {probe} {el}: '{key}' is named once"
          ((diagsB.filter fun d => d.code == "W0104" &&
            d.subject == some s!"style:{el}:{key}").size == 1)
      check ref s!"block style {probe} {el}: nothing else is raised"
        ((diagsB.filter (·.severity != .note)).size == unread.length &&
          (diagsA.filter (·.severity != .note)).isEmpty)
      check ref s!"block style {probe} {el}: the page ships as without the keys"
        (pageInk outA == pageInk outB)
      let html (s : String) : String := (HtmlDoc.emit {} (Elab.run s!"block-style-{probe}.tex" s).1).1
      check ref s!"block style {probe} {el}: the HTML ships as without the keys"
        (html src == html styled)

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
       ("Gamma title words", "OpenSans-Bold", Dim.pt 12)])]
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
either artifact. -/
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

end Tests.BlockTemplate
