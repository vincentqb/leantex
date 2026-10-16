module

public import Tests.Artifact

public section

open LeanTex.Core LeanTex.Cli

/-! Declared list, beamer and counter settings read as their packages read them, or named once
where they are set; positions are lualatex's, measured on the same documents. -/

namespace Tests.DeclSettings

/-- Four nested itemize and four nested enumerate levels, one word on each item. -/
def nestedLists : String :=
  "\\begin{itemize}\\item Ione\\begin{itemize}\\item Itwo\\begin{itemize}\\item Ithree" ++
  "\\begin{itemize}\\item Ifour\\end{itemize}\\end{itemize}\\end{itemize}\\end{itemize}\n" ++
  "\\begin{enumerate}\\item Eone\\begin{enumerate}\\item Etwo\\begin{enumerate}\\item Ethree" ++
  "\\begin{enumerate}\\item Efour\\end{enumerate}\\end{enumerate}\\end{enumerate}\\end{enumerate}\n"

/-- An article loading enumitem, with `pre` in its preamble and `body` before the nested lists. -/
def listDoc (pre : String) (body : String := "") : String :=
  s!"\\documentclass\{article}\n\\usepackage\{enumitem}\n{pre}\n\\begin\{document}\n{body}" ++
    nestedLists ++ "\\end{document}\n"

/-- enumitem's scopes as lualatex sets them: a first level alone or past four is named and styles
no other level, a narrower scope keeps its setting beside a later broader one, and one `\setlist`
is one accounting. -/
def setlistChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) (font : Font) :
    IO Unit := do
  let t := check ref
  let run (src : String) : Array Layout.LineOut × Array Diag × Array UInt8 :=
    let (d, ds) := elabStr src
    let out := layoutOf oneFace d
    (bodyLines out, ds ++ out.diags, (driverPdf oneFace (Layout.Geom.ofPage d.page) d out).data)
  let markerOf (l : Layout.LineOut) : String :=
    match l.segs[0]? with
    | some (Layout.Seg.run _ _ _ _ glyphs _ _ _ _ _ _) => String.ofList (glyphs.toList.map (·.2.1))
    | _ => ""
  let lvl3 := if (font.gid '∗').isSome then "∗" else "*"
  let defaults := #["•", "–", lvl3, "·", "1.", "(a)", "i.", "A."]
  -- An item's text stands past its marker run and the gaps after it.
  let textX (l : Layout.LineOut) : Int := Id.run do
    let mut x := l.x
    for h : i in [0:l.segs.size] do
      match l.segs[i] with
      | Layout.Seg.run _ _ _ w _ _ _ _ _ _ _ => if i == 0 then x := x + w else return x
      | Layout.Seg.gap w _ => x := x + w
      | _ => return x
    return x
  let steps (ls : Array Layout.LineOut) : Array Int :=
    (List.range 3).toArray.map fun i =>
      ((ls[i + 1]?.map textX).getD 0 - (ls[i]?.map textX).getD 0 : Int)
  let pt (n : Int) : Int := n * 65536
  let near (a b : Int) : Bool := (a - b).natAbs ≤ 65536 / 10
  let (base, baseDs, basePdf) := run (listDoc "")
  t "setlist: the nested lists draw the class markers" (base.map markerOf == defaults)
  t "setlist: the nested lists raise nothing" (baseDs.all (·.severity != .warning))
  -- lualatex: • – ∗ · at 21.9, 18.6 and 17.0 bp steps, whatever a first level alone declares.
  let (b1, b1Ds, _) := run (listDoc "\\setlist[itemize,1]{label=\\textbullet}")
  t "setlist: a first level alone styles no deeper level" (b1.map markerOf == defaults)
  t "setlist: a first level alone is named W0104"
    (b1Ds.any fun d => d.code == "W0104" && d.subject == some "param:\\setlist:label")
  let (a1, a1Ds, _) := run (listDoc "\\setlist[enumerate,1]{label=(\\alph*)}")
  t "setlist: a counting label numbers no level as (*)"
    (a1.map markerOf == defaults && !a1Ds.any (·.code == "W0301"))
  let (m1, _, _) := run (listDoc "\\setlist[enumerate,1]{leftmargin=3em}")
  t "setlist: a first level's margin moves no deeper level"
    (steps (m1.extract 4 8) == steps (base.extract 4 8))
  -- lualatex: level 2 at 9.9 bp from level 1, levels 3 and 4 at 29.9, in either order.
  for pre in ["\\setlist[itemize,2]{leftmargin=1em}\\setlist[itemize]{leftmargin=3em}",
      "\\setlist[itemize]{leftmargin=3em}\\setlist[itemize,2]{leftmargin=1em}"] do
    let (lv, _, _) := run (listDoc pre)
    let s := steps (lv.extract 0 4)
    t s!"setlist: a level keeps its own margin beside its kind's: {pre}"
      (s.size == 3 && near s[0]! (pt 10) && near s[1]! (pt 30) && near s[2]! (pt 30))
  -- lualatex: itemize keeps x, enumerate takes y, whatever the order.
  let (g1, _, _) := run (listDoc "\\setlist[itemize]{label=x}\\setlist{label=y}")
  t "setlist: a kind scope wins over a later global one"
    (g1.map markerOf == #["x", "x", "x", "x", "y", "y", "y", "y"])
  let (z1, _, _) := run (listDoc "\\setlist[itemize]{label=x}\\setlist[2]{label=z}")
  t "setlist: a kind scope wins over a later level one"
    ((z1.map markerOf).extract 0 2 == #["x", "x"] && (z1.map markerOf)[5]? == some "z")
  let (_, o1Ds, o1Pdf) := run (listDoc "\\setlist[itemize,0]{leftmargin=3em}")
  t "setlist: a level past the four ships, its setting named"
    (!o1Ds.any (·.severity == .error) && o1Ds.any (·.code == "W0104") && o1Pdf == basePdf)
  let (_, starDs, _) := run (listDoc "\\setlist{leftmargin=*}")
  t "setlist: a widest-label margin is named once" ((starDs.filter (·.severity != .note)).size == 1)
  let (_, romanDs, _) := run (listDoc "\\setlist[enumerate]{label=(\\roman*)}")
  t "setlist: a counting label is named once" ((romanDs.filter (·.severity != .note)).size == 1)
  -- premise: a body `\setlist` leaves no ink, so its one W0340 is its accounting.
  let (_, bodyDs, bodyPdf) := run (listDoc "" "{\\setlist[itemize]{label=x}}")
  t "setlist: a body setlist is one W0340 and leaves the page as it was"
    ((bodyDs.filter (·.severity != .note)).size == 1 && bodyDs.any (·.code == "W0340") &&
      bodyPdf == basePdf)

/-- A three-frame deck: a title page, a titled frame with lists and a block, and a second
titled frame; `pre` in its preamble and `mid` between the first two titled frames. -/
def deck (pre : String) (mid : String := "") : String :=
  s!"\\documentclass\{beamer}\n{pre}\n\\title\{Probe title}\\author\{Probe author}\n" ++
    "\\begin{document}\n\\begin{frame}\\titlepage\\end{frame}\n" ++
    "\\begin{frame}{Frame title}\\begin{itemize}\\item One item\\end{itemize}" ++
    "\\begin{block}{Block title}Block words.\\end{block}\\end{frame}\n" ++
    s!"{mid}\n\\begin\{frame}\{Second title}Second words.\\end\{frame}\n\\end\{document}\n"

/-- A frame title reads only its font, and only under a frame-title bar, in the frame model alone:
the other keys, a font with no bar and a frame title in a flow class change nothing. -/
def frameTitleKeyChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let ship (src : String) : Array UInt8 × String × Array Diag :=
    let (d, ds) := elabLocated "t.tex" src
    let out := layoutOf oneFace d
    ((driverPdf oneFace (Layout.Geom.ofPage d.page) d out).data, (HtmlDoc.emit {} d).1, ds)
  let bar := "\\setbeamercolor{frametitle}{bg=blue,fg=white}"
  for (pre, label) in [("", "a deck"), (bar, "a barred deck"), ("\\usetheme{moloch}", "moloch")] do
    let (pdf, html, _) := ship (deck pre)
    for key in ["align = center", "color = #8A2BE2"] do
      let (pdf', html', ds) := ship (deck (pre ++ s!"\\style\{frametitle}\{ {key} }"))
      t s!"frame title: '{key}' changes nothing in {label}" (pdf' == pdf && html' == html)
      t s!"frame title: '{key}' is named in {label}"
        (ds.any fun d => d.code == "W0104" && d.subject.any (·.startsWith "style:frametitle:"))
  let font := "\\setbeamerfont{frametitle}{size=\\tiny}"
  let (pdf, html, _) := ship (deck "")
  let (pdf', html', ds) := ship (deck font)
  t "frame title: a font with no bar changes nothing" (pdf' == pdf && html' == html)
  t "frame title: a font with no bar is named at its declaration"
    (ds.any fun d => d.subject == some "param:\\style:frametitle:font" &&
      d.span.any (·.pos.line == 2))
  for restated in ["size=\\Large", "series=\\bfseries", "size=\\Large,series=\\bfseries"] do
    let (pdfR, htmlR, dsR) := ship (deck s!"\\setbeamerfont\{frametitle}\{{restated}}")
    t s!"frame title: '{restated}' restates the plain title, changing nothing, noted"
      (pdfR == pdf && htmlR == html &&
        !dsR.any (fun d => d.severity == .warning && d.subject == some "param:\\style:frametitle:font") &&
        dsR.any fun d => d.code == "N0100" && d.subject == some "param:\\style:frametitle:font")
  let (pdfB, _, _) := ship (deck font "")
  let (pdfM, _, dsM) := ship (deck font bar)
  t "frame title: a bar declared between frames sets the declared font" (pdfM != pdfB)
  t "frame title: a font a later bar sets is not named"
    (!dsM.any fun d => d.subject == some "param:\\style:frametitle:font")
  let (_, _, dsS) := ship "\\documentclass{slides}\n\\style{frametitle}{ align = left }\n\\begin{document}\n\\begin{frame}{Title}Words.\\end{frame}\n\\end{document}\n"
  t "frame title: a key nobody's font declared names no font"
    (!dsS.any fun d => d.subject == some "param:\\style:frametitle:font")
  let art (pre : String) := s!"\\documentclass\{article}\n{pre}\n\\begin\{document}\nWords.\n\\end\{document}\n"
  let (pdfA, _, _) := ship (art "")
  let (pdfA', _, dsA) := ship (art "\\style{frametitle}{ font = {\\Huge} }")
  t "frame title: a flow class draws none, so its style changes nothing and is named"
    (pdfA' == pdfA && dsA.any (·.subject == some "style:frametitle"))

/-- beamer templates whose default draws nothing: an empty body asks for what the engine draws,
a deck with no links of its own carries none, and a predefined template takes no later line. -/
def emptyTemplateChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let ship (src : String) : Array UInt8 × String × Array Diag × Layout.Out :=
    let (d, ds) := elabStr src
    let out := layoutOf oneFace d
    ((driverPdf oneFace (Layout.Geom.ofPage d.page) d out).data, (HtmlDoc.emit {} d).1, ds, out)
  for theme in ["", "\\usetheme{moloch}"] do
    let (pdf, html, _, out) := ship (deck theme)
    t s!"templates: a deck carries no link of its own {theme}"
      (out.pages.all fun p => p.links.isEmpty && p.lines.all fun l => l.segs.all fun
        | Layout.Seg.run _ _ link _ _ _ _ _ _ _ _ => link.isNone
        | _ => true)
    for element in Compat.emptyTemplates do
      let (pdf', html', ds, _) := ship (deck (theme ++ s!"\\setbeamertemplate\{{element}}\{}"))
      t s!"templates: '{element}\{}' changes nothing {theme}" (pdf' == pdf && html' == html)
      t s!"templates: '{element}\{}' is a note, not a warning {theme}"
        (!ds.any (·.severity == .warning) &&
          ds.any (·.subject == some s!"param:\\setbeamertemplate:{element}"))
  for (tpl, next) in [("footline[frame number]", "\\author{Probe author}"),
      ("itemize items[circle]", "% a comment\n\\author{Probe author}"),
      ("enumerate items[default]", "\\author{Probe author}"), ("blocks[rounded]", "\\date{}"),
      ("section in toc[sections numbered]", "\\author{Probe author}"),
      ("title page[default]", "\\author{Probe author}")] do
    let e := String.ofList (tpl.toList.takeWhile (· != '['))
    let (_, _, ds, _) := ship (deck s!"\\setbeamertemplate\{{e}}{(tpl.drop e.length).toString}\n{next}")
    t s!"templates: '{tpl}' before another line ships, the template named"
      (!ds.any (·.severity == .error) &&
        ds.any fun d => d.subject == some s!"param:\\setbeamertemplate:{e}")

/-- The templates lualatex measured drawing nothing by default, beamer's headline and background
under its default, moloch, metropolis and Madrid themes. -/
def lualatexEmptyByDefault : List String := ["headline", "background"]

/-- Every empty template the reader notes is one lualatex measured empty by default, or the
navigation symbols, which the engine draws none of. -/
def emptyTemplateMeasuredChecks (ref : IO.Ref (List String)) : IO Unit :=
  check ref "templates: every empty template noted is measured empty, or one the engine never draws"
    (Compat.emptyTemplates.all fun e => e == "navigation symbols" || lualatexEmptyByDefault.contains e)

/-- The templates lualatex measured unchanged by their predefined `default` form in an unthemed
deck. -/
def lualatexDefaultUnchanged : List String :=
  ["itemize items", "enumerate items", "blocks", "footline", "title page"]

/-- A predefined `default` the reader notes is one lualatex measured unchanged, and the unthemed
deck ships the same pages with it; a themed deck's names it. -/
def defaultTemplateChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  t "templates: every noted default is one lualatex measured unchanged"
    (Compat.defaultTemplates.all lualatexDefaultUnchanged.contains)
  let ship (src : String) : Array UInt8 × String × Array Diag :=
    let (d, ds) := elabStr src
    ((driverPdf oneFace (Layout.Geom.ofPage d.page) d (layoutOf oneFace d)).data,
      (HtmlDoc.emit {} d).1, ds)
  let (pdf, html, _) := ship (deck "")
  for e in Compat.defaultTemplates do
    let (pdf', html', ds) := ship (deck s!"\\setbeamertemplate\{{e}}[default]")
    t s!"templates: '{e}[default]' ships an unthemed deck's pages, noted"
      (pdf' == pdf && html' == html && !ds.any (·.severity == .warning) &&
        ds.any (·.subject == some s!"param:\\setbeamertemplate:{e}"))
    let (_, _, dsM) := ship (deck s!"\\usetheme\{moloch}\\setbeamertemplate\{{e}}[default]")
    t s!"templates: '{e}[default]' under a theme is named"
      (dsM.any fun d => d.code == "W0104" && d.subject == some s!"param:\\setbeamertemplate:{e}")

/-- A counter a use reads is named at the use, and only one nothing reads at its allocation; a
listing's language help names the language written. -/
def counterReadChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (_, shared) := elabStr ("\\documentclass{article}\n\\usepackage{amsthm}\n" ++
    "\\newcounter{shared}\\newtheorem{theorem}[shared]{Theorem}\n\\begin{document}\n" ++
    "\\begin{theorem}Words.\\end{theorem}\n\\end{document}\n")
  t "counters: a counter a theorem shares is named at the theorem alone"
    (!shared.any (·.subject == some "param:\\newcounter:shared") && shared.any (·.code == "W0110"))
  let counted (pre body : String) : Array Diag :=
    (elabStr (s!"\\documentclass\{article}\n\\usepackage\{amsmath}\n\\newcounter\{probe}\n{pre}\n" ++
      s!"\\begin\{document}\n{body}\nWords.\n\\end\{document}\n")).2
  let allocNamed (ds : Array Diag) : Nat :=
    (ds.filter fun d => d.subject == some "param:\\newcounter:probe").size
  for (pre, body, what) in [("", "\\stepcounter{probe}Count \\theprobe.", "a step and its value"),
      ("\\numberwithin{equation}{probe}", "\\begin{equation}x\\end{equation}", "a numbering within it"),
      ("\\counterwithin{figure}{probe}", "", "a counter within it"),
      ("", "\\setcounter{probe}{3}", "a setting"), ("", "\\refstepcounter{probe}", "a reference step"),
      ("", "\\addtocounter{probe}{2}\\arabic{probe}", "an addition and its numeral"),
      ("", "{\\usecounter{probe}}", "a list's use"),
      ("", "\\setcounter{section}{\\value{probe}}", "its value")] do
    let ds := counted pre body
    t s!"counters: a counter read by {what} is not named at its allocation, its use naming its loss"
      (allocNamed ds == 0 && !ds.any (·.subject == some "ctrl:newcounter") &&
        ds.any (·.severity == .warning))
  let unused := counted "" ""
  t "counters: a counter nothing reads is named once, with help"
    (allocNamed unused == 1 && unused.any fun d =>
      d.subject == some "param:\\newcounter:probe" && d.help.isSome && d.span.any (·.pos.line == 3))
  t "counters: a counter whose name another's extends is still unread"
    (allocNamed (counted "\\newcounter{probeextra}" "\\stepcounter{probeextra}\\theprobeextra") == 1)
  t "counters: a counter reset by another is still unread"
    (allocNamed (counted "\\newcounter{probereset}[probe]" "") == 0 &&
      (counted "\\newcounter{probereset}[section]" "").any
        (·.subject == some "param:\\newcounter:probereset"))
  let (_, viaMacro) := elabStr ("\\documentclass{article}\n\\newcommand{\\mkcounter}[1]{\\newcounter{#1}}\n" ++
    "\\mkcounter{probe}\n\\begin{document}\nWords.\n\\end{document}\n")
  t "counters: an allocation a macro makes is named once, at its use"
    ((viaMacro.filter fun d => d.subject.any (·.startsWith "param:\\newcounter:")).size == 1 &&
      viaMacro.any fun d => d.subject == some "param:\\newcounter:probe" && d.span.any (·.pos.line == 3))
  let (_, minted) := elabStr ("\\documentclass{article}\n\\usepackage{minted}\n" ++
    "\\setminted{language=haskell}\n\\begin{document}\n\\begin{minted}{haskell}\nmain = 1\n" ++
    "\\end{minted}\n\\end{document}\n")
  t "listings: minted's language help names the language written"
    (minted.any fun d => d.help.any fun h => hasStr h "{haskell}")

/-- An article's titlepage names a loss only where LaTeX sets a page the engine does not: at
`\\maketitle`, whose title stands above the text here, and at the abstract. -/
def titlePageChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (cls opts body : String) : String :=
    s!"\\documentclass{opts}\{{cls}}\n\\title\{Probe title}\\author\{Probe author}\n" ++
      s!"\\begin\{document}\n{body}\nBody words.\n\\end\{document}\n"
  let losses (ds : Array Diag) : Array Diag :=
    ds.filter fun d => d.subject.any (·.startsWith "partial:\\documentclass:titlepage")
  let firstPage (d : Ir.Doc) : String :=
    String.join ((((layoutOf oneFace d).pages[0]?).map (·.lines.toList.map lineText)).getD [])
  t "titlepage: nothing is named where no title or abstract stands"
    (losses (elabStr (doc "article" "[titlepage]" "")).2).isEmpty
  t "titlepage: a page of the document's own names nothing"
    (losses (elabStr (doc "article" "[titlepage]" "\\begin{titlepage}Own page.\\end{titlepage}")).2).isEmpty
  for (body, what) in [("\\maketitle", "'\\maketitle'"),
      ("\\begin{abstract}Abstract words.\\end{abstract}", "the abstract")] do
    let (d, ds) := elabStr (doc "article" "[titlepage]" body)
    t s!"titlepage: {what} is named once, at its line"
      ((losses ds).size == 1 && (losses ds).all fun x => x.span.any (·.pos.line == 4))
    -- the premise the loss stands on: what LaTeX gives a page of its own shares the text's first page
    t s!"titlepage: {what} shares the first page with the text"
      (hasStr (firstPage d) "Body" && (hasStr (firstPage d) "Probe" || hasStr (firstPage d) "Abstract"))
  t "titlepage: report's own title page names nothing"
    (losses (elabStr (doc "report" "" "\\maketitle")).2).isEmpty
  t "titlepage: notitlepage names nothing"
    (losses (elabStr (doc "article" "[titlepage,notitlepage]" "\\maketitle")).2).isEmpty

/-- The display keys lualatex measured leaving fvextra's inline `\\Verb` where it stands, each
with a value against the same line without it. -/
def lualatexInlineUnchanged : List String :=
  ["linenos", "numbers", "firstnumber", "stepnumber", "numbersep", "numberblanklines",
   "numberfirstline", "frame", "framerule", "framesep", "rulecolor", "label", "labelposition",
   "xleftmargin", "xrightmargin", "resetmargins", "samepage", "vspace", "listparameters",
   "firstline", "lastline", "highlightlines", "highlightcolor"]

/-- Every key `\\setmintedinline` notes as a display's alone is one lualatex measured leaving
inline code unchanged. -/
def inlineDisplayChecks (ref : IO.Ref (List String)) : IO Unit := do
  check ref "listings: every display-only inline key has its lualatex measurement"
    (Compat.mintedDisplayKeys.all lualatexInlineUnchanged.contains)

end Tests.DeclSettings
