module

public import Tests.Support

public section

open LeanTex.Core

/-! A deck's section stands on a page of its own only where its design declares a section page, as
beamer's theme hook does; any other names navigation alone: its anchor and its label land on what is
set next, its title reaches the footline, and content outside every frame takes a page of its own. -/

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

/-- Whether a node stands out of the row's flow, so it moves no stage off the snap grid. -/
private def outOfFlow : Html.Node → Bool
  | .elem _ attrs _ => hasStr ((HtmlDoc.attrOf? attrs "style").getD "") "position: absolute"
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

/-- The out-of-flow headings of the row, their tag and words, in order. -/
private def navHeadings (kids : Array Html.Node) : Array (String × String) :=
  (elemNodesList (fun t => t == "h2" || t == "h3" || t == "h4") #[] kids.toList).filterMap fun k =>
    match k with
    | .elem tag _ _ => if outOfFlow k then some (tag, (nodeTextOne "" k).trimAscii.toString) else none
    | _ => none

/-- The index of the first stage holding the `id`, among the row's stages. -/
private def stageWithId (kids : Array Html.Node) (id : String) : Option Nat :=
  (kids.filter isStage).findIdx? (holdsId id)

/-- The index of the first stage whose shown words hold the marker. -/
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
anchors land, its footlines and its out-of-flow headings. -/
private structure Expected where
  pages : Array (Kind × String)
  labels : Array (String × String)
  anchors : Array (String × String) := #[]
  foots : Array (String × String) := #[]
  headings : Array (String × String) := #[]

private def verify (ref : IO.Ref (List String)) (fonts : Font.FontSet) (name pre body : String)
    (e : Expected) : IO Unit := do
  let t := fun claim => check ref ("section pages / " ++ name ++ " / " ++ claim)
  let (doc, ds) := elabStr (deck169 pre body)
  let out := layoutOf fonts doc
  let census := censusOf (coveredColorsOf doc) out
  let (_, html, hds) := HtmlDoc.emitTree {} doc
  let kids := mainKids html
  t "the deck builds clean"
    (!(ds ++ hds ++ out.diags).any fun d => d.severity == .error || d.code == "W0301")
  let titles := e.pages.filterMap fun (k, m) => if k == .section then some m else none
  t s!"the PDF ships the expected pages ({census.size} pages)"
    (census.size == e.pages.size &&
      e.pages.toList.zipIdx.all fun ((kind, marker), i) =>
        pageHas census i marker && out.pages[i]?.map (pageKind · titles) == some kind)
  t "every element of the web deck's row is a stage or stands out of its flow"
    (kids.all fun k => isStage k || outOfFlow k)
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
    (navHeadings kids == e.headings)
  let pdf := Pdf.write (Layout.Geom.ofPage doc.page) fonts out.pages doc.info
    (tree := Struct.ofDoc (Layout.pdfView doc))
  let tagged := match PdfRead.objects pdf with
    | .ok es => es.val.filterMap fun en =>
      match en.val.get? "S", en.val.get? "K" with
      | some (.name s), none => if s.startsWith "H" then (en.val.get? "ActualText").map (s, ·) else none
      | _, _ => none
    | .error _ => #[]
  t "and names itself in the tagged PDF by its words, as a heading holding no ink"
    (tagged == e.headings.map fun (tag, title) => (tag.toUpper, PdfRead.textString title))

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

end SectionPages

open SectionPages in
/-- Page counts over `Layout.Out` and stages over the typed HTML tree, beamer's measured on invented
decks: no section page, a theme's own, a footline naming the section, and content outside frames. -/
def sectionPageChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let foot := "\\chrome{ footer = { left = \\sectiontitle } }"
  verify ref fonts "no section page" ("\\theme{default}" ++ foot) sectioned
    { pages := #[(.frame, "OpeningWords"), (.frame, "FirstWords"), (.frame, "SecondWords"),
        (.frame, "ThirdWords"), (.frame, "FourthWords")]
      labels := #[("sec:alpha", "FirstWords"), ("sub:detail", "SecondWords"),
        ("sec:beta", "ThirdWords")]
      anchors := #[("Alpha Part", "FirstWords"), ("Beta Part", "ThirdWords")]
      foots := #[("", ""), ("Alpha Part", ""), ("Alpha Part", ""), ("Beta Part", ""),
        ("Gamma Part", "")]
      headings := #[("h2", "Alpha Part"), ("h3", "Alpha Detail"), ("h2", "Beta Part"),
        ("h2", "Gamma Part")] }
  verify ref fonts "a theme's section page" "\\theme{moloch}" sectioned
    { pages := #[(.frame, "OpeningWords"), (.section, "Alpha Part"), (.frame, "FirstWords"),
        (.frame, "SecondWords"), (.section, "Beta Part"), (.frame, "ThirdWords"),
        (.section, "Gamma Part"), (.frame, "FourthWords")]
      labels := #[("sec:alpha", "FirstWords"), ("sub:detail", "SecondWords"),
        ("sec:beta", "ThirdWords")]
      anchors := #[("Alpha Part", "Alpha Part"), ("Beta Part", "Beta Part")]
      headings := #[("h3", "Alpha Detail")] }
  verify ref fonts "content outside frames, no section page" "\\theme{default}" loose
    { pages := #[(.frame, "OneWords"), (.loose, "LooseBefore"), (.frame, "TwoWords")]
      labels := #[("sec:middle", "LooseAfter")]
      headings := #[("h2", "Middle Part")] }
  verify ref fonts "content outside frames, a theme's section page" "\\theme{moloch}" loose
    { pages := #[(.frame, "OneWords"), (.loose, "LooseBefore"), (.section, "Middle Part"),
        (.loose, "LooseAfter"), (.frame, "TwoWords")]
      labels := #[("sec:middle", "LooseAfter")] }
  verify ref fonts "a section after content outside frames" "\\theme{default}" looseThenSection
    { pages := #[(.frame, "OneWords"), (.loose, "LooseOnly"), (.frame, "TwoWords")]
      labels := #[("sec:late", "TwoWords")]
      anchors := #[("Late Part", "TwoWords")]
      headings := #[("h2", "Late Part")] }
  let t := fun claim => check ref ("section pages / " ++ claim)
  let (doc, _) := elabStr (deck169 "\\theme{default}" looseThenSection)
  let kids := mainKids (HtmlDoc.emitTree {} doc).2.1
  t "a section set after content outside frames names the stage set next, between the two"
    (navHeadings (kids.filter outOfFlow) == #[("h2", "Late Part")] &&
      (kids.filter isStage).all fun k => navHeadings #[k] == #[])
  let census (pre : String) := censusOfSrc fonts (deck169 pre sectioned)
  for pre in ["\\theme{default}", "\\theme{moloch}"] do
    let c := census pre
    t s!"a reference to a section shows beamer's number ({pre})"
      ((pageWith c "FirstWords").any (pageHas c · "see 2.") &&
        (pageWith c "SecondWords").any (pageHas c · "detail 1.") &&
        (pageWith c "ThirdWords").any (pageHas c · "back to 1."))
  -- the outside content's two paragraphs and the section between them share one page and one stage
  let (doc, _) := elabStr (deck169 "\\theme{default}" loose)
  let kids := mainKids (HtmlDoc.emitTree {} doc).2.1
  t "the outside content's section stands between its paragraphs on its stage"
    (match (kids.filter isStage)[1]? with
     | some stage =>
       let text := nodeTextOne "" stage
       hasStr text "LooseBefore" && hasStr text "LooseAfter" &&
         navHeadings #[stage] == #[("h2", "Middle Part")]
     | none => false)
