import Tests.Support

open LeanTex.Core

namespace SlideLabels

/-- An empty alias leaves a section divider's ID unspecified. All other
aliases are the authored frame slug or the existing reveal spacer ID. -/
private structure Expected where
  snaps : Array (String × String)
  pageMarkers : Array String
  pageFooters : Array (Option (String × String))
  htmlFooters : Array (String × String)
  tracks : Array (String × String) := #[]
  shadowedFragments : Array String := #[]

private def attr (attrs : Array (String × String)) (key : String) : Option String :=
  (attrs.find? (·.1 == key)).map (·.2)

/-- Inspect emitted elements and shipped page ink. In particular, no expected
number is computed from the document's frame census: that is what broke. -/
private def verify (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (name : String) (input : Ir.Doc × Array Diag) (expected : Expected) : IO Unit := do
  let (doc, ds) := input
  let t := fun claim => check ref ("slide labels / " ++ name ++ " / " ++ claim)
  let (_, html, htmlDs) := HtmlDoc.emitTree {} doc
  let out := layoutOf fonts doc
  let census := censusOf (coveredColorsOf doc) out
  let elements := elemAttrsList (fun _ => true) #[] html.toList
  let snaps := elements.filterMap fun (_, attrs) =>
    if (attr attrs "data-snap").isSome then some attrs else none
  let labels := snaps.map fun attrs => (attr attrs "data-slide-label").getD ""
  t "source and backends accept the invented deck"
    (!(ds ++ htmlDs ++ out.diags).any fun d =>
      d.severity == .error || d.code == "W0301" || d.code == "W0302")
  t "every emitted snap carries exactly one nonblank canonical label"
    (snaps.all fun attrs =>
      let values := attrs.filter (·.1 == "data-slide-label")
      values.size == 1 && !(values[0]?.map (·.2.trimAscii.toString.isEmpty)).getD true)
  t "canonical labels follow the expected stage and reveal order"
    (labels == expected.snaps.map (·.2))
  t "canonical labels are unique"
    (labels.toList.eraseDups.length == labels.size)
  t "authored slugs and reveal spacer IDs still identify their original snaps"
    (snaps.size == expected.snaps.size &&
      expected.snaps.toList.zipIdx.all fun ((alias, _), i) =>
        alias.isEmpty || (snaps[i]?.bind fun attrs => attr attrs "id") == some alias)
  let tracks := elements.filterMap fun (_, attrs) =>
    if ((attr attrs "class").getD "").splitOn " " |>.contains "slide-track" then
      some attrs
    else none
  t "stepped frame slugs remain track aliases"
    (tracks.filterMap (attr · "id") == expected.tracks.map (·.1))
  t "each track declares its first canonical reveal as its alias owner"
    (tracks.map (fun attrs => attr attrs "data-slide-label") ==
      expected.tracks.map (some ∘ Prod.snd))
  let collisions := htmlDs.filter (·.code == "W0327")
  t "different-target alias collisions are named once by their shadowed fragment"
    (collisions.size == expected.shadowedFragments.size &&
      expected.shadowedFragments.all fun fragment =>
        (collisions.filter (·.subject == some fragment)).size == 1)
  t "layout ships the expected pages in source order"
    (census.size == expected.pageMarkers.size &&
      expected.pageMarkers.toList.zipIdx.all fun (marker, i) => pageOccurs census i marker == 1)
  t "layout suppresses numeric furniture on title, divider and standout pages"
    (out.pages.map (·.foot.isSome) == expected.pageFooters.map (·.isSome))
  t "layout footer slots count logical frames including standouts"
    (pdfFoots out == expected.pageFooters.filterMap id)
  t "layout paints the declared footer text once on each page"
    (expected.pageFooters.toList.zipIdx.all fun (footer, i) =>
      match footer with
      | none => true
      | some (left, right) =>
        (left.isEmpty || pageOccurs census i left == 1) &&
        (right.isEmpty || pageOccurs census i right == 1))
  t "typed HTML footers count the same frames without numbering standouts"
    (slideFootsList #[] html.toList == expected.htmlFooters)

private def fractionTheme : String :=
  "\\theme{moloch}\\chrome{footer={right=\\framefraction}}"

private def mixedChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit :=
  verify ref fonts "mixed stages" (elabStr (deck169
    (fractionTheme ++ "\\title{TitleProbe}")
    ("\\maketitle\n\\section{RepeatSection}\n" ++
     "\\begin{frame}{Repeat}FirstBody\\end{frame}\n" ++
     "\\begin{frame}[standout]{Aside}StandoutBody\\end{frame}\n" ++
     "\\section{RepeatSection}\n" ++
     "\\begin{frame}{Repeat}StepAlpha\n\n\\pause\nStepBeta\n\n\\pause\nStepGamma\\end{frame}\n" ++
     "\\begin{frame}FinalBody\\end{frame}"))) {
    snaps := #[("slide", "titlepage"), ("", "section-0"), ("repeat", "1"),
      ("aside", "2"), ("", "section-1"), ("repeat-2-1", "3.1"),
      ("repeat-2-2", "3.2"), ("repeat-2-3", "3.3"), ("slide-2", "4")]
    pageMarkers := #["TitleProbe", "RepeatSection", "FirstBody", "StandoutBody",
      "RepeatSection", "StepAlpha", "StepAlpha", "StepAlpha", "FinalBody"]
    pageFooters := #[none, none, some ("", "1 / 4"), none, none,
      some ("", "3 / 4"), some ("", "3 / 4"), some ("", "3 / 4"), some ("", "4 / 4")]
    htmlFooters := #[("", "1 / 4"), ("", "3 / 4"), ("", "4 / 4")]
    tracks := #[("repeat-2", "3.1")]
  }

private def numericAliasChecks (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit :=
  -- The first frame's authored #2 conflicts with the second frame's canonical
  -- number; the authored #1 and dotted-title slug #1-2 must also survive.
  -- A no-title deck still starts its canonical sequence at 1.1, not 0 or 2.
  verify ref fonts "numeric aliases without a title page" (elabStr (deck169 fractionTheme
    ("\\begin{frame}{2}DigitAlpha\n\n\\pause\nDigitBeta\\end{frame}\n" ++
     "\\begin{frame}[standout]{1.2}DottedBody\\end{frame}\n" ++
     "\\begin{frame}{1}OneBody\\end{frame}\n" ++
     "\\begin{frame}{2}RepeatDigitBody\\end{frame}"))) {
    snaps := #[("2-1", "1.1"), ("2-2", "1.2"), ("1-2", "2"), ("1", "3"), ("2-3", "4")]
    pageMarkers := #["DigitAlpha", "DigitAlpha", "DottedBody", "OneBody", "RepeatDigitBody"]
    pageFooters := #[some ("", "1 / 4"), some ("", "1 / 4"), none,
      some ("", "3 / 4"), some ("", "4 / 4")]
    htmlFooters := #[("", "1 / 4"), ("", "3 / 4"), ("", "4 / 4")]
    tracks := #[("2", "1.1")]
    shadowedFragments := #["1", "2"]
  }

private def appendixChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let body :=
    "\\section{RepeatSection}\n" ++
    "\\begin{frame}{Main}MainFirst\\end{frame}\n" ++
    "\\begin{frame}[standout]{Aside}MainAside\\end{frame}\n" ++
    "\\begin{frame}{End}MainLast\\end{frame}\n\\appendix\n\\section{RepeatSection}\n" ++
    "\\begin{frame}{Main}AppendixAlpha\n\n\\pause\nAppendixBeta\\end{frame}\n" ++
    "\\begin{frame}[standout]{Aside}AppendixAside\\end{frame}\n" ++
    "\\begin{frame}{End}AppendixLast\\end{frame}"
  let pageMarkers := #["RepeatSection", "MainFirst", "MainAside", "MainLast",
    "RepeatSection", "AppendixAlpha", "AppendixAlpha", "AppendixAside", "AppendixLast"]
  verify ref fonts "explicit appendix reset" (elabStr (deck169
    (fractionTheme ++ "\\usepackage{appendixnumberbeamer}") body)) {
    snaps := #[("", "section-0"), ("main", "1"), ("aside", "2"), ("end", "3"),
      ("", "section-1"), ("main-2-1", "appendix-1.1"), ("main-2-2", "appendix-1.2"),
      ("aside-2", "appendix-2"), ("end-2", "appendix-3")]
    pageMarkers
    pageFooters := #[none, some ("", "1 / 3"), none, some ("", "3 / 3"), none,
      some ("", "1 / 3"), some ("", "1 / 3"), none, some ("", "3 / 3")]
    htmlFooters := #[("", "1 / 3"), ("", "3 / 3"), ("", "1 / 3"), ("", "3 / 3")]
    tracks := #[("main-2", "appendix-1.1")]
  }
  verify ref fonts "appendix without a reset" (elabStr (deck169 fractionTheme body)) {
    snaps := #[("", "section-0"), ("main", "1"), ("aside", "2"), ("end", "3"),
      ("", "section-1"), ("main-2-1", "4.1"), ("main-2-2", "4.2"),
      ("aside-2", "5"), ("end-2", "6")]
    pageMarkers
    pageFooters := #[none, some ("", "1 / 6"), none, some ("", "3 / 6"), none,
      some ("", "4 / 6"), some ("", "4 / 6"), none, some ("", "6 / 6")]
    htmlFooters := #[("", "1 / 6"), ("", "3 / 6"), ("", "4 / 6"), ("", "6 / 6")]
    tracks := #[("main-2", "4.1")]
  }

private def standoutNoteChecks (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit := do
  let body :=
    "\\begin{frame}{Before}BeforeBody\\end{frame}\n\\framefoot{StandoutNote}\n" ++
    "\\begin{frame}[standout]{Focus}FocusAlpha\n\n\\pause\nFocusBeta\\end{frame}\n" ++
    "\\framefoot{NormalNote}\\begin{frame}{After}AfterBody\\end{frame}\n" ++
    "\\framefoot{}\\begin{frame}[standout]{Empty}EmptyBody\\end{frame}\n" ++
    "\\begin{frame}{Last}LastBody\\end{frame}"
  for restored in [false, true] do
    let input := elabStr (deck169
      (fractionTheme ++ "\\chrome{standout-note=" ++ toString restored ++ "}") body)
    let note := if restored then some ("StandoutNote", "") else none
    let htmlNote := if restored then #[("StandoutNote", "")] else #[]
    verify ref fonts ("standout note " ++ toString restored) input {
      snaps := #[("before", "1"), ("focus-1", "2.1"), ("focus-2", "2.2"),
        ("after", "3"), ("empty", "4"), ("last", "5")]
      pageMarkers := #["BeforeBody", "FocusAlpha", "FocusAlpha", "AfterBody", "EmptyBody", "LastBody"]
      pageFooters := #[some ("", "1 / 5"), note, note, some ("NormalNote", "3 / 5"),
        none, some ("", "5 / 5")]
      htmlFooters := #[("", "1 / 5")] ++ htmlNote ++ #[("NormalNote", "3 / 5"), ("", "5 / 5")]
      tracks := #[("focus", "2.1")]
    }
    let census := censusOf (coveredColorsOf input.1) (layoutOf fonts input.1)
    let compact (s : String) := String.ofList (s.toList.filter (!·.isWhitespace))
    let focusText := "FocusAlphaFocusBeta" ++ if restored then "StandoutNote" else ""
    check ref ("slide labels / standout note " ++ toString restored ++
        " / shipped standout ink contains the explicit note only, never its counted number")
      ([1, 2].all (fun i => (census[i]?.map (compact ∘ CensusPage.text)) == some focusText) &&
        (census[4]?.map (compact ∘ CensusPage.text)) == some "EmptyBody")

private def sectionChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let body :=
    "\\section{RepeatSection}\n\\begin{frame}{One}FirstBody\\end{frame}\n" ++
    "\\section{RepeatSection}\n\\begin{frame}{Two}SecondBody\\end{frame}"
  -- Without sectionProgress these headings still ship ink, but are not HTML
  -- snap stages. Do not equate that deck's physical page count with its snaps.
  verify ref fonts "sections without progress" (elabStr (deck169 "\\theme{default}" body)) {
    snaps := #[("one", "1"), ("two", "2")]
    pageMarkers := #["RepeatSection", "FirstBody", "RepeatSection", "SecondBody"]
    pageFooters := #[none, none, none, none]
    htmlFooters := #[]
  }
  verify ref fonts "sections with progress" (elabStr (deck169 "\\theme{moloch}" body)) {
    snaps := #[("", "section-0"), ("one", "1"), ("", "section-1"), ("two", "2")]
    pageMarkers := #["RepeatSection", "FirstBody", "RepeatSection", "SecondBody"]
    pageFooters := #[none, some ("", "1"), none, some ("", "2")]
    htmlFooters := #[("", "1"), ("", "2")]
  }
  -- A prior heading with no divider must not consume section-0. The palette
  -- change is read at each stage, not just from the document's final palette.
  verify ref fonts "only emitted dividers consume section labels" (elabStr (deck169
    "\\theme{default}"
    ("\\section{UnmarkedSection}\n\\begin{frame}{One}FirstBody\\end{frame}\n" ++
     "\\palette{progressfg=#123456}\n\\section{RepeatSection}\n" ++
     "\\begin{frame}[standout]{Aside}AsideBody\\end{frame}\n" ++
     "\\section{RepeatSection}\n\\begin{frame}{Two}SecondBody\\end{frame}"))) {
    snaps := #[("one", "1"), ("", "section-0"), ("aside", "2"), ("", "section-1"), ("two", "3")]
    pageMarkers := #["UnmarkedSection", "FirstBody", "RepeatSection", "AsideBody",
      "RepeatSection", "SecondBody"]
    pageFooters := #[none, none, none, none, none, none]
    htmlFooters := #[]
  }

private def repeatedTitleChecks (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit := do
  -- The surface currently consumes only the first \maketitle / \titlepage.
  -- Compose copies of a source-elaborated title frame to exercise repeated
  -- emitted title pages without making a parser change part of this test.
  let (title, titleDs) := elabStr (deck169
    (fractionTheme ++ "\\title{TitleEcho}") "\\maketitle")
  let (first, firstDs) := elabStr (deck169 fractionTheme
    "\\begin{frame}{Repeat}FirstBody\\end{frame}")
  let (aside, asideDs) := elabStr (deck169 fractionTheme
    "\\begin{frame}[standout]{Aside}AsideBody\\end{frame}")
  let (last, lastDs) := elabStr (deck169 fractionTheme
    "\\begin{frame}{Repeat}LastBody\\end{frame}")
  let doc := { title with body :=
    title.body ++ first.body ++ title.body ++ aside.body ++ title.body ++ last.body }
  verify ref fonts "repeated source-elaborated title pages"
    (doc, titleDs ++ firstDs ++ asideDs ++ lastDs) {
    snaps := #[("slide", "titlepage"), ("repeat", "1"), ("slide-2", "titlepage-2"),
      ("aside", "2"), ("slide-3", "titlepage-3"), ("repeat-2", "3")]
    pageMarkers := #["TitleEcho", "FirstBody", "TitleEcho", "AsideBody", "TitleEcho", "LastBody"]
    pageFooters := #[none, some ("", "1 / 3"), none, none, none, some ("", "3 / 3")]
    htmlFooters := #[("", "1 / 3"), ("", "3 / 3")]
  }

private def collisionChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  verify ref fonts "semantic and numeric alias collisions" (elabStr (deck169
    (fractionTheme ++ "\\title{CollisionTitle}")
    ("\\maketitle\n\\section{Divider}\n" ++
     "\\begin{frame}{titlepage}TitleAliasBody\\end{frame}\n" ++
     "\\begin{frame}{section-0}SectionAliasBody\\end{frame}\n" ++
     "\\begin{frame}{2}NumericAliasBody\\end{frame}"))) {
    snaps := #[("slide", "titlepage"), ("", "section-0"), ("titlepage", "1"),
      ("section-0", "2"), ("2", "3")]
    pageMarkers := #["CollisionTitle", "Divider", "TitleAliasBody", "SectionAliasBody", "NumericAliasBody"]
    pageFooters := #[none, none, some ("", "1 / 3"), some ("", "2 / 3"), some ("", "3 / 3")]
    htmlFooters := #[("", "1 / 3"), ("", "2 / 3"), ("", "3 / 3")]
    shadowedFragments := #["titlepage", "section-0", "2"]
  }
  -- Both old reveal spacers are still present. They belong to the main
  -- frame, whereas the canonical appendix routes belong to later frames.
  verify ref fonts "appendix labels shadow main reveal aliases" (elabStr (deck169
    (fractionTheme ++ "\\usepackage{appendixnumberbeamer}")
    ("\\begin{frame}{Appendix}MainAlpha\n\n\\pause\nMainBeta\\end{frame}\n" ++
     "\\appendix\n\\begin{frame}{Extra}ExtraBody\\end{frame}\n" ++
     "\\begin{frame}[standout]{Aside}ExtraAside\\end{frame}"))) {
    snaps := #[("appendix-1", "1.1"), ("appendix-2", "1.2"), ("extra", "appendix-1"),
      ("aside", "appendix-2")]
    pageMarkers := #["MainAlpha", "MainAlpha", "ExtraBody", "ExtraAside"]
    pageFooters := #[some ("", "1 / 1"), some ("", "1 / 1"), some ("", "1 / 2"), none]
    htmlFooters := #[("", "1 / 1"), ("", "1 / 2")]
    tracks := #[("appendix", "1.1")]
    shadowedFragments := #["appendix-1", "appendix-2"]
  }
  verify ref fonts "a frame's own numeric alias is not a collision" (elabStr (deck169
    fractionTheme "\\begin{frame}{1}OwnBody\\end{frame}")) {
    snaps := #[("1", "1")]
    pageMarkers := #["OwnBody"]
    pageFooters := #[some ("", "1 / 1")]
    htmlFooters := #[("", "1 / 1")]
  }
  verify ref fonts "a track's own first-step alias is not a collision" (elabStr (deck169
    fractionTheme "\\begin{frame}{1}OwnAlpha\n\n\\pause\nOwnBeta\\end{frame}")) {
    snaps := #[("1-1", "1.1"), ("1-2", "1.2")]
    pageMarkers := #["OwnAlpha", "OwnAlpha"]
    pageFooters := #[some ("", "1 / 1"), some ("", "1 / 1")]
    htmlFooters := #[("", "1 / 1")]
    tracks := #[("1", "1.1")]
  }

private def linkChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := fun claim => check ref ("slide labels / canonical links / " ++ claim)
  let targets := #["1", "1.1", "1.2", "2", "titlepage", "section-0", "section-1",
    "appendix-1", "appendix-1.1", "appendix-1.2", "appendix-2", "intro", "intro-1", "aside"]
  let links := String.join (targets.toList.map fun target => "\\href{#" ++ target ++ "}{Go} ")
  let source (extra : String) := deck169
    (fractionTheme ++ "\\usepackage{appendixnumberbeamer}\\title{LinkTitle}")
    ("\\maketitle\n\\section{Divider}\n\\begin{frame}{Intro}" ++ links ++ extra ++
     "\n\n\\pause\nNextBody\\end{frame}\n" ++
     "\\begin{frame}[standout]{Aside}AsideBody\\end{frame}\n" ++
     "\\appendix\n\\section{Divider}\n" ++
     "\\begin{frame}{Extra}ExtraAlpha\n\n\\pause\nExtraBeta\\end{frame}\n" ++
     "\\begin{frame}{Last}LastBody\\end{frame}")
  let (doc, ds) := elabStr (source "")
  let (_, html, htmlDs) := HtmlDoc.emitTree {} doc
  t "link source is accepted" (!ds.any (·.severity == .error))
  t "the deck navigation script ships with the canonical targets"
    (html.any fun
      | .script _ js => js == HtmlDoc.deckScript
      | _ => false)
  let hrefs := (elemAttrsList (· == "a") #[] html.toList).filterMap fun (_, attrs) =>
    attr attrs "href"
  t "typed anchors preserve every authored canonical and legacy href"
    (hrefs == targets.map ("#" ++ ·))
  t "stepped, semantic and appendix fragments including first-step aliases resolve"
    (!htmlDs.any (·.code == "W0326"))
  let (missing, _) := elabStr (source
    "\\href{#missing-slide}{Missing}\\href{#missing-slide}{Again}")
  let (_, _, missingDs) := HtmlDoc.emitTree {} missing
  let unresolved := missingDs.filter (·.code == "W0326")
  t "a nonexistent fragment is still named once"
    (unresolved.size == 1 && unresolved.all (fun d => hasStr d.message "#missing-slide"))
  -- The exemption needs a shipped deck script. A static article has neither
  -- those canonical routes nor their targets, even though their names parse.
  let (article, _) := elabStr (dvDoc "\\theme{default}"
    ("\\href{#1.1}{Step}\\href{#titlepage}{Title}" ++
     "\\href{#section-0}{Section}\\href{#appendix-1}{Appendix}"))
  let (_, articleHtml, articleDs) := HtmlDoc.emitTree {} article
  t "static articles retain missing-target checks for deck-shaped fragments"
    ((articleDs.filter (·.code == "W0326")).size == 4 &&
      !articleHtml.any (fun
        | .script _ js => js == HtmlDoc.deckScript
        | _ => false))

end SlideLabels

/-- Canonical fragments and authored aliases over typed HTML, with logical
frame counts independently witnessed by shipped page order and footer ink.
The caller can use `findFont` and `oneFaceOf` from Tests.Support, so these
invented decks need only the checked-in corpus font. -/
def slideLabelChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  SlideLabels.mixedChecks ref fonts
  SlideLabels.numericAliasChecks ref fonts
  SlideLabels.appendixChecks ref fonts
  SlideLabels.standoutNoteChecks ref fonts
  SlideLabels.sectionChecks ref fonts
  SlideLabels.repeatedTitleChecks ref fonts
  SlideLabels.collisionChecks ref fonts
  SlideLabels.linkChecks ref
