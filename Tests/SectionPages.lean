module

public import Tests.Support

public section

open LeanTex.Core

/-! A deck's section stands on a page of its own only where its theme or its own `\AtBeginSection`
declares one; any other names navigation alone, its anchor and label on what is set next. -/

namespace SectionPages

private def classes (attrs : Array (String × String)) : List String :=
  ((HtmlDoc.attrOf? attrs "class").getD "").splitOn " "

/-- The element children of the page's `main`, in order. -/
private def mainKids (body : Array Html.Node) : Array Html.Node :=
  match ((elemNodesList (· == "main") #[] body.toList)[0]? : Option Html.Node) with
  | some (.elem _ _ kids) => kids.filter (· matches .elem ..)
  | _ => #[]

/-- Whether a node is one stage of the deck's row: a frame, a section page or a stepped track. -/
private def isStage : Html.Node → Bool
  | .elem tag attrs _ =>
    (tag == "section" && ((classes attrs).contains "slide" || (classes attrs).contains "section-page")) ||
      (tag == "div" && (classes attrs).contains "slide-track")
  | _ => false

/-- Whether a node stands out of sight and out of flow. -/
private def outOfSight : Html.Node → Bool
  | .elem _ attrs _ =>
    let style := (HtmlDoc.attrOf? attrs "style").getD ""
    hasStr style "position: absolute" && hasStr style "clip-path: inset(50%)"
  | _ => false

/-- Whether a subtree carries an element of that `id`. -/
private def holdsId (id : String) (n : Html.Node) : Bool :=
  (elemNodesList (fun _ => true) #[] [n]).any fun k => match k with
    | .elem _ attrs _ => HtmlDoc.attrOf? attrs "id" == some id
    | _ => false

/-- Each stage's slide label, in order. -/
private def stageLabels (kids : Array Html.Node) : Array String :=
  (kids.filter isStage).map fun k => match k with
    | .elem _ attrs _ => (HtmlDoc.attrOf? attrs "data-slide-label").getD ""
    | _ => ""

/-- The out-of-sight headings under the nodes, their tag and words, in order. -/
private def navHeadings (kids : Array Html.Node) : Array (String × String) :=
  (elemNodesList (fun t => t == "h2" || t == "h3" || t == "h4") #[] kids.toList).filterMap fun k =>
    match k with
    | .elem tag _ _ => if outOfSight k then some (tag, (nodeTextOne "" k).trimAscii.toString) else none
    | _ => none

/-- The index of the first stage holding the `id`, among the row's stages. -/
private def stageWithId (kids : Array Html.Node) (id : String) : Option Nat :=
  (kids.filter isStage).findIdx? (holdsId id)

/-- The index of the first stage whose words hold the marker. -/
private def stageWith (kids : Array Html.Node) (marker : String) : Option Nat :=
  (kids.filter isStage).findIdx? fun k => hasStr (nodeTextOne "" k) marker

/-- The page whose ink holds the marker. -/
private def pageWith (c : Array CensusPage) (marker : String) : Option Nat :=
  (List.range c.size).find? (pageHas c · marker)

/-- What a page or stage is: a frame's, a section page, or content set outside every frame. -/
private inductive Kind where
  | frame | section | loose
  deriving BEq, Repr

/-- The kind a stage of the web deck is, by its class. -/
private def stageKind : Html.Node → Option Kind
  | .elem tag attrs _ =>
    if tag == "div" && (classes attrs).contains "slide-track" then some .frame
    else if tag != "section" then none
    else if (classes attrs).contains "section-page" then some .section
    else if (classes attrs).contains "loose" then some .loose
    else if (classes attrs).contains "slide" then some .frame
    else none
  | _ => none

/-- The kind a PDF page is: a frame's owns it, a section page or outside content owns none. -/
private def pageKind (p : Layout.PageOut) (sectionTitles : Array String) : Kind :=
  if p.frameOrigin.isSome then .frame
  else if p.lines.all fun l => l.furniture || sectionTitles.contains (lineText l).trimAscii.toString
  then .section
  else .loose

/-- What one invented deck ships: its pages by kind and marker, where its labels and section
anchors land, its footlines, its out-of-sight headings with a marker of the stage holding each, and
the codes it names. -/
private structure Expected where
  pages : Array (Kind × String)
  labels : Array (String × String)
  anchors : Array (String × String) := #[]
  foots : Array (String × String) := #[]
  headings : Array (String × String × String) := #[]
  warns : Array String := #[]

private def verify (ref : IO.Ref (List String)) (fonts : Font.FontSet) (name pre body : String)
    (e : Expected) : IO Unit := do
  let t := fun claim => check ref ("section pages / " ++ name ++ " / " ++ claim)
  let (doc, ds) := elabStr (deck169 pre body)
  let out := layoutOf fonts doc
  let census := censusOf (coveredColorsOf doc) out
  let (_, html, hds) := HtmlDoc.emitTree {} doc
  let kids := mainKids html
  let all := ds ++ hds ++ out.diags
  t s!"the deck builds clean, naming what it loses ({all.toList.map (·.code)})"
    (!all.any (fun d => d.severity == .error || d.code == "W0301") &&
      e.warns.all fun c => all.any (·.code == c))
  let titles := e.pages.filterMap fun (k, m) => if k == .section then some m else none
  t s!"the PDF ships the expected pages ({census.size} pages)"
    (census.size == e.pages.size &&
      e.pages.toList.zipIdx.all fun ((kind, marker), i) =>
        pageHas census i marker && out.pages[i]?.map (pageKind · titles) == some kind)
  t "every element of the web deck's row is a stage" (kids.all isStage)
  let stages := kids.filter isStage
  t s!"the web deck ships one stage per page, of its kind ({stageLabels kids})"
    (stages.size == e.pages.size &&
      e.pages.toList.zipIdx.all fun ((kind, marker), i) =>
        stageWith kids marker == some i && (stages[i]?.bind stageKind) == some kind)
  for (key, marker) in e.labels do
    let anchor := Ir.labelAnchor key
    t s!"the label {key} lands on the page set next, as beamer's"
      ((Layout.destination? out.pages anchor).map (·.1) == pageWith census marker)
    t s!"and on that stage in the web deck"
      (stageWithId kids anchor == stageWith kids marker)
  for (title, marker) in e.anchors do
    t s!"the section {title} anchors the page set next"
      ((Layout.destination? out.pages (Ir.slug #[.text title])).map (·.1) == pageWith census marker)
  unless e.foots.isEmpty do
    t s!"the footline names the section in force on every frame ({pdfFoots out})"
      (pdfFoots out == e.foots && slideFootsList #[] html.toList == e.foots)
  t s!"each page-less section names itself out of sight ({navHeadings kids})"
    (navHeadings kids == e.headings.map fun (tag, title, _) => (tag, title))
  for (tag, title, marker) in e.headings do
    t s!"the heading {title} stands in the stage set next, where the pager finds it"
      ((stageWith kids marker).any fun i =>
        (stages[i]?.map fun s => (navHeadings #[s]).contains (tag, title)) == some true)
  let pdf := Pdf.write (Layout.Geom.ofPage doc.page) fonts out.pages doc.info
    (tree := Struct.ofDoc (Layout.pdfView doc))
  let tagged := match PdfRead.objects pdf with
    | .ok es => some (es.val.filterMap fun en =>
      match en.val.get? "S", en.val.get? "K" with
      | some (.name s), none => if s.startsWith "H" then (en.val.get? "ActualText").map (s, ·) else none
      | _, _ => none)
    | .error _ => none
  t "and names itself in the tagged PDF by its words, as a heading holding no ink"
    (tagged == some (e.headings.map fun (tag, title, _) => (tag.toUpper, PdfRead.textString title)))

/-- Five frames under three sections, one starred, with a subsection, labels and references. -/
private def sectioned : String :=
  "\\begin{frame}{Opening}OpeningWords\\end{frame}\n" ++
  "\\section{Alpha Part}\\label{sec:alpha}\n" ++
  "\\begin{frame}{First}FirstWords, see \\ref{sec:beta}.\\end{frame}\n" ++
  "\\subsection{Alpha Detail}\\label{sub:detail}\n" ++
  "\\begin{frame}{Second}SecondWords, detail \\ref{sub:detail}.\\end{frame}\n" ++
  "\\section{Beta Part}\\label{sec:beta}\n" ++
  "\\begin{frame}{Third}ThirdWords, back to \\ref{sec:alpha}.\\end{frame}\n" ++
  "\\section*{Gamma Part}\n" ++
  "\\begin{frame}{Fourth}FourthWords\\end{frame}"

/-- What `sectioned` ships where no section stands on a page of its own. -/
private def pageless : Expected :=
  { pages := #[(.frame, "OpeningWords"), (.frame, "FirstWords"), (.frame, "SecondWords"),
      (.frame, "ThirdWords"), (.frame, "FourthWords")]
    labels := #[("sec:alpha", "FirstWords"), ("sub:detail", "SecondWords"), ("sec:beta", "ThirdWords")]
    anchors := #[("Alpha Part", "FirstWords"), ("Beta Part", "ThirdWords")]
    headings := #[("h2", "Alpha Part", "FirstWords"), ("h3", "Alpha Detail", "SecondWords"),
      ("h2", "Beta Part", "ThirdWords"), ("h2", "Gamma Part", "FourthWords")] }

/-- A hook setting a frame naming each section and, its optional argument empty, none for a starred
one. -/
private def outlineHook : String :=
  "\\AtBeginSection[]{\\begin{frame}{Outline}OutlineWords \\insertsection\\end{frame}}"

/-- What `sectioned` ships where the hook's frame follows each unstarred section, as beamer's. -/
private def hooked : Expected :=
  { pages := #[(.frame, "OpeningWords"), (.frame, "OutlineWords Alpha Part"), (.frame, "FirstWords"),
      (.frame, "SecondWords"), (.frame, "OutlineWords Beta Part"), (.frame, "ThirdWords"),
      (.frame, "FourthWords")]
    labels := #[("sec:alpha", "FirstWords"), ("sub:detail", "SecondWords"), ("sec:beta", "ThirdWords")]
    anchors := #[("Alpha Part", "OutlineWords Alpha Part"), ("Beta Part", "OutlineWords Beta Part")]
    headings := #[("h2", "Alpha Part", "OutlineWords Alpha Part"), ("h3", "Alpha Detail", "SecondWords"),
      ("h2", "Beta Part", "OutlineWords Beta Part"), ("h2", "Gamma Part", "FourthWords")] }

/-- Content outside every frame, then a section, then a frame. -/
private def looseThenSection : String :=
  "\\begin{frame}{One}OneWords\\end{frame}\n" ++
  "LooseOnly words.\n\n\\section{Late Part}\\label{sec:late}\n\n" ++
  "\\begin{frame}{Two}TwoWords\\end{frame}"

/-- Content outside every frame around a section, between two frames. -/
private def loose : String :=
  "\\begin{frame}{One}OneWords\\end{frame}\n" ++
  "LooseBefore words.\n\n\\section{Middle Part}\\label{sec:middle}\nLooseAfter words.\n\n" ++
  "\\begin{frame}{Two}TwoWords\\end{frame}"

/-- A section whose title holds its label. -/
private def titleLabel : String :=
  "\\begin{frame}{Opening}OpeningWords\\end{frame}\n\\section{Kettle Part\\label{sec:kettle}}\n" ++
  "\\begin{frame}{First}FirstWords\\end{frame}"

/-- A section, a label and a note after the last frame, and a note between frames. -/
private def trailing : String :=
  "\\begin{frame}{Opening}OpeningWords\\end{frame}\n\\note{EarlyNoteWords}\n" ++
  "\\begin{frame}{Last}LastWords\\end{frame}\n" ++
  "\\section{Last Part}\\label{sec:last}\n\\label{deck:end}\n\n\\note{LateNoteWords}"

/-- A hook declared after a section, which opens the later sections only. -/
private def lateHook : String :=
  "\\begin{frame}{Opening}OpeningWords\\end{frame}\n\\section{Alpha Part}\n" ++ outlineHook ++
  "\n\\begin{frame}{First}FirstWords\\end{frame}\n\\section{Beta Part}\n" ++
  "\\begin{frame}{Second}SecondWords\\end{frame}"

/-- Sections and labels under a language, a size group and a colour declared outside the frames. -/
private def scopedLabels : String :=
  "\\begin{frame}{One}OneWords\\end{frame}\n\\selectlanguage{french}\n" ++
  "\\section{Partie Alpha}\\label{sec:fr}\n\\begin{frame}{Deux}DeuxWords\\end{frame}\n" ++
  "{\\small\n\\section{Small Part}\\label{sec:small}\n\\begin{frame}{Four}FourWords\\end{frame}\n}\n" ++
  "\\color{red}\n\\section{Red Part}\\label{sec:red}\n\\begin{frame}{Five}FiveWords\\end{frame}"

/-- Blocks outside the frames that set nothing: an empty centre, an empty list, a label in a centre. -/
private def quiet : String :=
  "\\begin{frame}{One}OneWords\\end{frame}\n\\begin{center}\\end{center}\n" ++
  "\\begin{frame}{Two}TwoWords\\end{frame}\n\\begin{itemize}\\end{itemize}\n" ++
  "\\begin{frame}{Three}ThreeWords\\end{frame}\n\\begin{center}\\label{quiet:c}\\end{center}\n" ++
  "\\begin{frame}{Four}FourWords\\end{frame}"

/-- A section inside a block outside the frames, which inks as that block's heading. -/
private def nestedSection : String :=
  "\\begin{frame}{One}OneWords\\end{frame}\n" ++
  "\\begin{center}\n\\section{Centred Part}\nCentredWords\n\\end{center}\n" ++
  "\\begin{frame}{Two}TwoWords\\end{frame}"

/-- A subsection hook declared after a section, before any subsection it opens. -/
private def lateSubHook : String :=
  "\\begin{frame}{Opening}OpeningWords\\end{frame}\n\\section{Alpha Part}\n" ++
  "\\AtBeginSubsection[]{\\begin{frame}{Sub}SubWords \\insertsubsection\\end{frame}}\n" ++
  "\\subsection{Alpha One}\n\\begin{frame}{First}FirstWords\\end{frame}\n" ++
  "\\subsection{Alpha Two}\n\\begin{frame}{Second}SecondWords\\end{frame}"

/-- References across a starred section and `\appendix`, which beamer numbers on. -/
private def appendixed : String :=
  "\\begin{frame}{Opening}OpeningWords, see \\ref{sec:a}, \\ref{sec:b}, \\ref{sec:backup}, " ++
  "\\ref{sub:x}.\\end{frame}\n" ++
  "\\section{Alpha}\\label{sec:a}\n\\begin{frame}{First}FirstWords\\end{frame}\n" ++
  "\\section*{Starred}\n\\section{Beta}\\label{sec:b}\n\\subsection{Sub X}\\label{sub:x}\n" ++
  "\\begin{frame}{Second}SecondWords\\end{frame}\n\\appendix\n" ++
  "\\section{Backup}\\label{sec:backup}\n\\begin{frame}{Spare}SpareWords\\end{frame}"

end SectionPages

open SectionPages in
/-- Page counts over `Layout.Out` and stages over the typed HTML tree, beamer's measured on invented
decks: no section page, a theme's own, the document's hooks, a footline naming the section, labels
and notes around the frames, and content outside frames. -/
def sectionPageChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let foot := "\\chrome{ footer = { left = \\sectiontitle } }"
  verify ref fonts "no section page" ("\\theme{default}" ++ foot) sectioned
    { pageless with
      foots := #[("", ""), ("Alpha Part", ""), ("Alpha Part", ""), ("Beta Part", ""),
        ("Gamma Part", "")] }
  let themed : Expected :=
    { pages := #[(.frame, "OpeningWords"), (.section, "Alpha Part"), (.frame, "FirstWords"),
        (.frame, "SecondWords"), (.section, "Beta Part"), (.frame, "ThirdWords"),
        (.section, "Gamma Part"), (.frame, "FourthWords")]
      labels := #[("sec:alpha", "FirstWords"), ("sub:detail", "SecondWords"),
        ("sec:beta", "ThirdWords")]
      anchors := #[("Alpha Part", "Alpha Part"), ("Beta Part", "Beta Part")]
      headings := #[("h3", "Alpha Detail", "SecondWords")] }
  verify ref fonts "a theme's section page" "\\theme{moloch}" sectioned themed
  verify ref fonts "a theme after the document's hook sets its own, as beamer's, and says so"
    "\\AtBeginSection[]{}\n\\theme{moloch}" sectioned { themed with warns := #["W0104"] }
  verify ref fonts "a progress bar's colour declares no section page"
    "\\theme{default}\n\\setbeamercolor{progress bar}{fg=red}" sectioned pageless
  verify ref fonts "the document's section hook" ("\\theme{default}\n" ++ outlineHook) sectioned hooked
  verify ref fonts "the document's hook declared before the first section" "\\theme{default}"
    (outlineHook ++ "\n" ++ sectioned) hooked
  verify ref fonts "the document's empty hook replaces the theme's"
    "\\theme{moloch}\n\\AtBeginSection{}" sectioned pageless
  verify ref fonts "moloch's sectionpage=none sets none, as its own empty hook"
    "\\usetheme[sectionpage=none]{moloch}" sectioned pageless
  verify ref fonts "the document's subsection hook"
    "\\theme{default}\n\\AtBeginSubsection{\\begin{frame}{Sub}SubWords\\end{frame}}" sectioned
    { pages := #[(.frame, "OpeningWords"), (.frame, "FirstWords"), (.frame, "SubWords"),
        (.frame, "SecondWords"), (.frame, "ThirdWords"), (.frame, "FourthWords")]
      labels := #[("sec:alpha", "FirstWords"), ("sub:detail", "SecondWords"),
        ("sec:beta", "ThirdWords")]
      anchors := #[("Alpha Part", "FirstWords"), ("Beta Part", "ThirdWords")]
      headings := #[("h2", "Alpha Part", "FirstWords"), ("h3", "Alpha Detail", "SubWords"),
        ("h2", "Beta Part", "ThirdWords"), ("h2", "Gamma Part", "FourthWords")] }
  verify ref fonts "a hook reaching its frame through the document's command"
    ("\\theme{default}\n" ++
      "\\newcommand{\\outlineframe}{\\begin{frame}{Outline}OutlineWords \\insertsection\\end{frame}}\n" ++
      "\\AtBeginSection[]{\\outlineframe}") sectioned hooked
  verify ref fonts "a hook reaching its frame through the document's environment"
    ("\\theme{default}\n" ++
      "\\newenvironment{outline}{\\begin{frame}{Outline}OutlineWords \\insertsection\\end{frame}}{}\n" ++
      "\\AtBeginSection[]{\\begin{outline}\\end{outline}}") sectioned hooked
  verify ref fonts "a subsection hook after a section opens every subsection" "\\theme{default}"
    lateSubHook
    { pages := #[(.frame, "OpeningWords"), (.frame, "SubWords Alpha One"), (.frame, "FirstWords"),
        (.frame, "SubWords Alpha Two"), (.frame, "SecondWords")]
      labels := #[]
      anchors := #[("Alpha Part", "SubWords Alpha One")]
      headings := #[("h2", "Alpha Part", "SubWords Alpha One"), ("h3", "Alpha One", "SubWords Alpha One"),
        ("h3", "Alpha Two", "SubWords Alpha Two")] }
  verify ref fonts "a hook declared after a section opens the later ones, as beamer's"
    "\\theme{default}" lateHook
    { pages := #[(.frame, "OpeningWords"), (.frame, "FirstWords"), (.frame, "OutlineWords Beta Part"),
        (.frame, "SecondWords")]
      labels := #[]
      anchors := #[("Alpha Part", "FirstWords"), ("Beta Part", "OutlineWords Beta Part")]
      headings := #[("h2", "Alpha Part", "FirstWords"), ("h2", "Beta Part", "OutlineWords Beta Part")] }
  verify ref fonts "a label in a section's title" "\\theme{default}" titleLabel
    { pages := #[(.frame, "OpeningWords"), (.frame, "FirstWords")]
      labels := #[("sec:kettle", "FirstWords")]
      anchors := #[("Kettle Part", "FirstWords")]
      headings := #[("h2", "Kettle Part", "FirstWords")] }
  verify ref fonts "a section and a label after the last frame" "\\theme{default}" trailing
    { pages := #[(.frame, "OpeningWords"), (.frame, "LastWords")]
      labels := #[("sec:last", "LastWords"), ("deck:end", "LastWords")]
      anchors := #[("Last Part", "LastWords")]
      headings := #[("h2", "Last Part", "LastWords")] }
  verify ref fonts "labels under a language, size or colour outside the frames, no section page"
    "\\usepackage[french,english]{babel}\n\\theme{default}" scopedLabels
    { pages := #[(.frame, "OneWords"), (.frame, "DeuxWords"), (.frame, "FourWords"),
        (.frame, "FiveWords")]
      labels := #[("sec:fr", "DeuxWords"), ("sec:small", "FourWords"), ("sec:red", "FiveWords")]
      anchors := #[("Partie Alpha", "DeuxWords"), ("Small Part", "FourWords"),
        ("Red Part", "FiveWords")]
      headings := #[("h2", "Partie Alpha", "DeuxWords"), ("h2", "Small Part", "FourWords"),
        ("h2", "Red Part", "FiveWords")] }
  verify ref fonts "labels under a language, size or colour outside the frames, a theme's section page"
    "\\usepackage[french,english]{babel}\n\\theme{moloch}" scopedLabels
    { pages := #[(.frame, "OneWords"), (.section, "Partie Alpha"), (.frame, "DeuxWords"),
        (.section, "Small Part"), (.frame, "FourWords"), (.section, "Red Part"), (.frame, "FiveWords")]
      labels := #[("sec:fr", "DeuxWords"), ("sec:small", "FourWords"), ("sec:red", "FiveWords")]
      anchors := #[("Partie Alpha", "Partie Alpha"), ("Small Part", "Small Part"),
        ("Red Part", "Red Part")] }
  verify ref fonts "blocks outside the frames that set nothing" "\\theme{default}" quiet
    { pages := #[(.frame, "OneWords"), (.frame, "TwoWords"), (.frame, "ThreeWords"),
        (.frame, "FourWords")]
      labels := #[("quiet:c", "FourWords")] }
  verify ref fonts "a section inside a block outside the frames inks as its heading" "\\theme{moloch}"
    nestedSection
    { pages := #[(.frame, "OneWords"), (.loose, "CentredWords"), (.frame, "TwoWords")]
      labels := #[] }
  verify ref fonts "content outside frames, no section page" "\\theme{default}" loose
    { pages := #[(.frame, "OneWords"), (.loose, "LooseBefore"), (.frame, "TwoWords")]
      labels := #[("sec:middle", "LooseAfter")]
      headings := #[("h2", "Middle Part", "LooseBefore")] }
  verify ref fonts "content outside frames, a theme's section page" "\\theme{moloch}" loose
    { pages := #[(.frame, "OneWords"), (.loose, "LooseBefore"), (.section, "Middle Part"),
        (.loose, "LooseAfter"), (.frame, "TwoWords")]
      labels := #[("sec:middle", "LooseAfter")] }
  verify ref fonts "a section after content outside frames" "\\theme{default}" looseThenSection
    { pages := #[(.frame, "OneWords"), (.loose, "LooseOnly"), (.frame, "TwoWords")]
      labels := #[("sec:late", "TwoWords")]
      anchors := #[("Late Part", "TwoWords")]
      headings := #[("h2", "Late Part", "TwoWords")] }
  let t := fun claim => check ref ("section pages / " ++ claim)
  let ds := (elabStr (deck169 "\\usetheme[sectionpage=none]{moloch}" sectioned)).2
  t s!"moloch's sectionpage=none is read, never skipped ({ds.toList.map (·.code)})"
    (!ds.any (·.code == "W0104"))
  let census (pre : String) := censusOfSrc fonts (deck169 pre sectioned)
  for pre in ["\\theme{default}", "\\theme{moloch}"] do
    let c := census pre
    t s!"a reference to a section shows beamer's number ({pre})"
      ((pageWith c "FirstWords").any (pageHas c · "see 2.") &&
        (pageWith c "SecondWords").any (pageHas c · "detail 1.") &&
        (pageWith c "ThirdWords").any (pageHas c · "back to 1."))
  let c := censusOfSrc fonts (deck169 "\\theme{default}" appendixed)
  t "a starred section steps the count and the appendix numbers on, as beamer's"
    ((pageWith c "OpeningWords").any (pageHas c · "see 1, 3, 4, 1."))
  let inFrame := "\\begin{frame}{Opening}OpeningWords, see \\ref{fr:first}.\\end{frame}\n" ++
    "\\section{Alpha Part}\n\\begin{frame}{First}\\label{fr:first}FirstWords\\end{frame}"
  let c := censusOfSrc fonts (deck169 "\\theme{default}" inFrame)
  t "a label in a frame takes its frame's number, as beamer's"
    ((pageWith c "OpeningWords").any (pageHas c · "see 2.") &&
      !(elabStr (deck169 "\\theme{default}" inFrame)).2.any (·.code == "W0349"))
  let named := "\\begin{frame}{Opening}OpeningWords, called \\nameref{fr:first} and " ++
    "\\nameref{sec:alpha}.\\end{frame}\n\\section{Alpha Part}\\label{sec:alpha}\n" ++
    "\\begin{frame}{First}\\label{fr:first}FirstWords\\end{frame}"
  let c := censusOfSrc fonts (deck169 "\\theme{default}" named)
  t "nameref names a frame's label by its section and a section's by its title, as beamer's"
    ((pageWith c "OpeningWords").any (pageHas c · "called Alpha Part and Alpha Part."))
  let c := censusOfSrc fonts (dvDoc "" ("\\section{Alpha}\\label{a}Words.\n\n" ++
    "\\begin{figure}[h]Body.\\caption{Panel words}\\label{f}\\end{figure}\n" ++
    "See \\nameref{a} and \\nameref{f}."))
  t "nameref sets a section's title and a float's caption in an article, as hyperref's"
    ((pageWith c "See Alpha").any (pageHas c · "See Alpha and Panel words."))
  let starred := "\\section*{Intro Words}\\label{i}Words.\\section{Plain \\emph{emph}}\\label{m}" ++
    "See \\nameref{i}, \\nameref{m}, \\nameref*{m} and \\ref*{m}."
  let (sdoc, sds) := elabStr (dvDoc "" starred)
  let c := censusOfSrc fonts (dvDoc "" starred)
  t "nameref names an unnumbered heading, and starred references set their text unlinked"
    (!sds.any (fun d => d.code == "W0349" || d.severity == .error) &&
      (pageWith c "See Intro").any (pageHas c · "See Intro Words, Plain emph, Plain emph and 1.") &&
      ((HtmlDoc.emit {} sdoc).1.splitOn "href=\"#m\"").length == 2)
  let (tdoc, _) := elabStr (dvDoc "" ("\\section{Plain \\emph{emph} $x^2$}\\label{m}" ++
    "See \\nameref*{m}."))
  let titled := (elemNodesList (· == "span") #[] (docNodesOf tdoc).toList).filter fun n =>
    match n with
    | .elem _ attrs _ => HtmlDoc.attrOf? attrs "class" == some (HtmlDoc.roleClass Ir.titleTextRole)
    | _ => false
  t "a starred nameref sets its title as typeset, emphasis and formula kept, unlinked"
    (titled.size == 1 && titled.all (fun n =>
      (elemNodesList (· == "em") #[] [n]).size == 1 &&
        (elemNodesList (· == "math") #[] [n]).size == 1 &&
        (elemNodesList (· == "a") #[] [n]).isEmpty))
  let chained := "\\section{Alpha}\\label{a}Words.\\section{More on \\nameref{a}}\\label{b}Words." ++
    "\\section{Eq \\eqref{e} and \\ref{a}}\\label{c}\\begin{equation}x\\label{e}\\end{equation}" ++
    "\\section{Further \\nameref{b}}\\label{d}See \\nameref{b}; \\nameref{c}; \\nameref{d}."
  let c := censusOfSrc fonts (dvDoc "" chained)
  t "nameref sets a title's own references resolved, along a chain of titles, as hyperref's"
    (!(elabStr (dvDoc "" chained)).2.any (·.code == "W0349") &&
      (pageWith c "See More").any
        (pageHas c · "See More on Alpha; Eq (1) and 1; Further More on Alpha."))
  let looped := "\\section{Self \\nameref{s}}\\label{s}See \\nameref{s}."
  let c := censusOfSrc fonts (dvDoc "" looped)
  t "a title naming itself ends its chain at ??, named"
    ((elabStr (dvDoc "" looped)).2.any (·.code == "W0349") &&
      (pageWith c "See Self").any (pageHas c · "See Self ??."))
  let capless := "\\section{Sec Words}\\begin{figure}[h]Body.\\label{f}\\end{figure}" ++
    "\\section{}\\label{z}See \\nameref{f} and \\nameref{z}."
  let (fdoc, fds) := elabStr (dvDoc "" capless)
  let c := censusOfSrc fonts (dvDoc "" capless)
  t "a captionless float's label names its heading, a blank title nothing, named, no link empty"
    ((pageWith c "See Sec").any (pageHas c · "See Sec Words and ??.") &&
      fds.any (·.code == "W0349") &&
      ((HtmlDoc.emit {} fdoc).1.splitOn "\"></a>").length == 1)
  let ranged (star : String) : String := "\\documentclass{article}\n\\usepackage{cleveref}\n" ++
    "\\begin{document}\n\\section{One}\\label{s1}Words.\\section{Two}\\label{s2}" ++
    s!"See \\crefrange{star}\{s1}\{s2}.\n\\end\{document}\n"
  let (rdoc, rds) := elabStr (ranged "*")
  let inked := fun (src : String) =>
    String.ofList ((censusText (censusOfSrc fonts src)).toList.filter (!·.isWhitespace))
  t "a starred cleveref range sets the unstarred range's text, unlinked"
    (!rds.any (·.code == "W0301") && hasStr (inked (ranged "*")) "sections1to2." &&
      inked (ranged "*") == inked (ranged "") &&
      !hasStr (HtmlDoc.emit {} rdoc).1 "href=\"#s1\"")
  let afterFrame := "\\begin{frame}{Opening}OpeningWords, see \\ref{after}.\\end{frame}\n" ++
    "\\section{Alpha Part}\n\\begin{frame}{First}FirstWords\\end{frame}\n\\label{after}\n" ++
    "\\begin{frame}{Second}SecondWords\\end{frame}"
  let c := censusOfSrc fonts (deck169 "\\theme{default}" afterFrame)
  t "a label after a frame binds its section's number again, as beamer's"
    ((pageWith c "OpeningWords").any (pageHas c · "see 1."))
  let (_, lds) := elabStr (deck169 ("\\theme{default}\n" ++ outlineHook) lateHook)
  t "a hook after a section replaces the earlier one silently, as beamer's"
    (!lds.any fun d => d.code == "W0307" || d.code == "W0340")
  let labelled := "\\begin{frame}{One}OneWords, see \\ref{fl}.\\end{frame}\n" ++
    "\\begin{frame}[label=fl]{Two}TwoWords\\end{frame}"
  let c := censusOfSrc fonts (deck169 "\\theme{default}" labelled)
  t "a frame's label option labels the frame, its number the frame's, as beamer's"
    (!(elabStr (deck169 "\\theme{default}" labelled)).2.any (·.code == "W0349") &&
      (pageWith c "OneWords").any (pageHas c · "see 2."))
  verify ref fonts "a hook in the body ends the theme's section pages from there on, as beamer's"
    "\\theme{moloch}"
    ("\\begin{frame}{Zero}ZeroWords\\end{frame}\n\\section{Alpha Part}\n" ++
      "\\begin{frame}{One}OneWords\\end{frame}\n\\AtBeginSection{}\n\\section{Beta Part}\n" ++
      "\\begin{frame}{Two}TwoWords\\end{frame}")
    { pages := #[(.frame, "ZeroWords"), (.section, "Alpha Part"), (.frame, "OneWords"),
        (.frame, "TwoWords")]
      labels := #[]
      anchors := #[("Alpha Part", "Alpha Part"), ("Beta Part", "TwoWords")]
      headings := #[("h2", "Beta Part", "TwoWords")] }
  -- A hook a group declares ends with the group, as beamer's `\def`.
  let grouped := "\\begin{frame}{Zero}ZeroWords\\end{frame}\n" ++ outlineHook ++
    "\n\\section{Alpha Part}\n\\begin{frame}{One}OneWords\\end{frame}\n" ++
    "{\\AtBeginSection{\\begin{frame}{Inner}InnerWords \\insertsection\\end{frame}}}\n" ++
    "\\section{Beta Part}\n\\begin{frame}{Two}TwoWords\\end{frame}\n" ++
    "\\section*{Gamma Part}\n\\begin{frame}{Three}ThreeWords\\end{frame}"
  let c := censusOfSrc fonts (deck169 "\\theme{default}" grouped)
  t "a hook a group declares ends with the group, the outer one opening the next section"
    ((pageWith c "OutlineWords Beta Part").isSome && !hasStr (censusText c) "InnerWords")
  let art := "\\documentclass{article}\n\\AtBeginSection[]{\\begin{frame}{Outline}\\end{frame}}\n" ++
    "\\begin{document}\n\\section{Alpha}\nAlpha words.\n\\AtBeginSubsection{KeptWords}\n" ++
    "\\subsection{Beta}\nBeta words.\\sectionpage\n\\end{document}"
  let ads := (elabStr art).2
  t "outside a deck the hooks and the section page stay unknown commands, the body's argument kept"
    ((ads.filter (·.code == "W0301")).size == 3 && !ads.any (·.code == "W0307") &&
      hasStr (censusText (censusOfSrc fonts art)) "KeptWords")
  let kidsOf (pre body : String) := mainKids (HtmlDoc.emitTree {} (elabStr (deck169 pre body)).1).2.1
  let kids := kidsOf "\\theme{default}" trailing
  t "a note between frames rides the frame before it, a trailing one the last"
    (stageWith kids "EarlyNoteWords" == stageWith kids "OpeningWords" &&
      stageWith kids "LateNoteWords" == stageWith kids "LastWords")
  let kids := kidsOf "\\theme{default}\n\\logo{LogoMarkWords}" looseThenSection
  t "content outside frames carries the logo in force, as a frame's stage"
    (kids.any (stageKind · == some .loose) &&
      (kids.filter isStage).all fun s => hasStr (nodeTextOne "" s) "LogoMarkWords")
  let wrapped := "\\begin{frame}{Opening}OpeningWords\\end{frame}\n" ++
    "\\section{Web Part}\\label{sec:web}\n" ++
    "\\begin{ifbackend}{html}\n\\begin{frame}{WebOnly}WebOnlyWords\\end{frame}\n\\end{ifbackend}\n" ++
    "\\begin{frame}{Both}BothWords\\end{frame}"
  let kids := kidsOf "\\theme{default}" wrapped
  t "a section before a frame set for one backend lands on that frame"
    (kids.any fun k => holdsId (Ir.labelAnchor "sec:web") k &&
      hasStr (nodeTextOne "" k) "WebOnlyWords" && (navHeadings #[k]).contains ("h2", "Web Part"))
