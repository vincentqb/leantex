module

public import Tests.Support

public section

open LeanTex.Core

namespace SlideLabels

/-- Expected labels; an empty alias leaves a section divider's id unspecified. -/
private structure Expected where
  snaps : Array (String × String)
  pageMarkers : Array String
  pageFooters : Array (Option (String × String))
  htmlFooters : Array (String × String)
  tracks : Array (String × String) := #[]
  shadowedFragments : Array String := #[]

private def attr (attrs : Array (String × String)) (key : String) : Option String :=
  (attrs.find? (·.1 == key)).map (·.2)

/-- Reads emitted elements and shipped ink, computing no expected number from the document's frame
census. -/
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
  t "authored slugs and reveal spacer IDs identify their original snaps"
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
  t "a cross-target alias collision is named once by its shadowed fragment"
    (collisions.size == expected.shadowedFragments.size &&
      expected.shadowedFragments.all fun fragment =>
        (collisions.filter (·.subject == some fragment)).size == 1)
  t "layout ships the expected pages in source order"
    (census.size == expected.pageMarkers.size &&
      expected.pageMarkers.toList.zipIdx.all fun (marker, i) => pageOccurs census i marker == 1)
  t "layout suppresses numeric furniture on title, divider and standout pages"
    (out.pages.map (·.foot.isSome) == expected.pageFooters.map (·.isSome))
  t "layout footer slots count logical frames, a standout bearing none"
    (pdfFoots out == expected.pageFooters.filterMap id)
  t "layout paints the declared footer text once on each page"
    (expected.pageFooters.toList.zipIdx.all fun (footer, i) =>
      match footer with
      | none => true
      | some (left, right) =>
        (left.isEmpty || pageOccurs census i left == 1) &&
        (right.isEmpty || pageOccurs census i right == 1))
  t "typed HTML footers count the same frames"
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
      ("aside", "standout"), ("", "section-1"), ("repeat-2-1", "2.1"),
      ("repeat-2-2", "2.2"), ("repeat-2-3", "2.3"), ("slide-2", "3")]
    pageMarkers := #["TitleProbe", "RepeatSection", "FirstBody", "StandoutBody",
      "RepeatSection", "StepAlpha", "StepAlpha", "StepAlpha", "FinalBody"]
    pageFooters := #[none, none, some ("", "1 / 3"), none, none,
      some ("", "2 / 3"), some ("", "2 / 3"), some ("", "2 / 3"), some ("", "3 / 3")]
    htmlFooters := #[("", "1 / 3"), ("", "2 / 3"), ("", "3 / 3")]
    tracks := #[("repeat-2", "2.1")]
  }

private def numericAliasChecks (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit :=
  -- The first frame's authored #2 conflicts with the second frame's canonical number.
  verify ref fonts "numeric aliases without a title page" (elabStr (deck169 fractionTheme
    ("\\begin{frame}{2}DigitAlpha\n\n\\pause\nDigitBeta\\end{frame}\n" ++
     "\\begin{frame}[standout]{1.2}DottedBody\\end{frame}\n" ++
     "\\begin{frame}{1}OneBody\\end{frame}\n" ++
     "\\begin{frame}{2}RepeatDigitBody\\end{frame}"))) {
    snaps := #[("2-1", "1.1"), ("2-2", "1.2"), ("1-2", "standout"), ("1", "2"), ("2-3", "3")]
    pageMarkers := #["DigitAlpha", "DigitAlpha", "DottedBody", "OneBody", "RepeatDigitBody"]
    pageFooters := #[some ("", "1 / 3"), some ("", "1 / 3"), none,
      some ("", "2 / 3"), some ("", "3 / 3")]
    htmlFooters := #[("", "1 / 3"), ("", "2 / 3"), ("", "3 / 3")]
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
    snaps := #[("", "section-0"), ("main", "1"), ("aside", "standout"), ("end", "2"),
      ("", "section-1"), ("main-2-1", "appendix-1.1"), ("main-2-2", "appendix-1.2"),
      ("aside-2", "standout-2"), ("end-2", "appendix-2")]
    pageMarkers
    pageFooters := #[none, some ("", "1 / 2"), none, some ("", "2 / 2"), none,
      some ("", "1 / 2"), some ("", "1 / 2"), none, some ("", "2 / 2")]
    htmlFooters := #[("", "1 / 2"), ("", "2 / 2"), ("", "1 / 2"), ("", "2 / 2")]
    tracks := #[("main-2", "appendix-1.1")]
  }
  verify ref fonts "appendix without a reset" (elabStr (deck169 fractionTheme body)) {
    snaps := #[("", "section-0"), ("main", "1"), ("aside", "standout"), ("end", "2"),
      ("", "section-1"), ("main-2-1", "3.1"), ("main-2-2", "3.2"),
      ("aside-2", "standout-2"), ("end-2", "4")]
    pageMarkers
    pageFooters := #[none, some ("", "1 / 4"), none, some ("", "2 / 4"), none,
      some ("", "3 / 4"), some ("", "3 / 4"), none, some ("", "4 / 4")]
    htmlFooters := #[("", "1 / 4"), ("", "2 / 4"), ("", "3 / 4"), ("", "4 / 4")]
    tracks := #[("main-2", "3.1")]
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
      snaps := #[("before", "1"), ("focus-1", "standout.1"), ("focus-2", "standout.2"),
        ("after", "2"), ("empty", "standout-2"), ("last", "3")]
      pageMarkers := #["BeforeBody", "FocusAlpha", "FocusAlpha", "AfterBody", "EmptyBody", "LastBody"]
      pageFooters := #[some ("", "1 / 3"), note, note, some ("NormalNote", "2 / 3"),
        none, some ("", "3 / 3")]
      htmlFooters := #[("", "1 / 3")] ++ htmlNote ++ #[("NormalNote", "2 / 3"), ("", "3 / 3")]
      tracks := #[("focus", "standout.1")]
    }
    let census := censusOf (coveredColorsOf input.1) (layoutOf fonts input.1)
    let compact (s : String) := String.ofList (s.toList.filter (!·.isWhitespace))
    let noted (words : String) := words ++ if restored then "StandoutNote" else ""
    check ref ("slide labels / standout note " ++ toString restored ++
        " / shipped standout ink contains the explicit note only, never a number")
      ([(1, "FocusAlpha"), (2, "FocusAlphaFocusBeta")].all (fun (i, words) =>
          (census[i]?.map (compact ∘ CensusPage.text)) == some (noted words)) &&
        (census[4]?.map (compact ∘ CensusPage.text)) == some "EmptyBody")

private def sectionChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let body :=
    "\\section{RepeatSection}\n\\begin{frame}{One}FirstBody\\end{frame}\n" ++
    "\\section{RepeatSection}\n\\begin{frame}{Two}SecondBody\\end{frame}"
  -- Without a section page these sections ship no ink and open no stage, as beamer's.
  verify ref fonts "sections without progress" (elabStr (deck169 "\\theme{default}" body)) {
    snaps := #[("one", "1"), ("two", "2")]
    pageMarkers := #["FirstBody", "SecondBody"]
    pageFooters := #[none, none]
    htmlFooters := #[]
  }
  verify ref fonts "sections with progress" (elabStr (deck169 "\\theme{moloch}" body)) {
    snaps := #[("", "section-0"), ("one", "1"), ("", "section-1"), ("two", "2")]
    pageMarkers := #["RepeatSection", "FirstBody", "RepeatSection", "SecondBody"]
    pageFooters := #[none, some ("", "1"), none, some ("", "2")]
    htmlFooters := #[("", "1"), ("", "2")]
  }
  -- A hook with an empty starred argument sets a divider for each section and none for a starred one.
  verify ref fonts "only emitted dividers consume section labels" (elabStr (deck169
    "\\theme{default}\n\\AtBeginSection[]{\\begin{frame}{Outline}x\\end{frame}}"
    ("\\section*{UnmarkedSection}\n\\begin{frame}{One}FirstBody\\end{frame}\n" ++
     "\\section{RepeatSection}\n" ++
     "\\begin{frame}[standout]{Aside}AsideBody\\end{frame}\n" ++
     "\\section{RepeatSection}\n\\begin{frame}{Two}SecondBody\\end{frame}"))) {
    snaps := #[("one", "1"), ("", "section-0"), ("aside", "standout"), ("", "section-1"),
      ("two", "2")]
    pageMarkers := #["FirstBody", "RepeatSection", "AsideBody", "RepeatSection", "SecondBody"]
    pageFooters := #[none, none, none, none, none]
    htmlFooters := #[]
  }

private def repeatedTitleChecks (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit := do
  -- The surface reads only the first title, so repeated title pages are composed from copies.
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
      ("aside", "standout"), ("slide-3", "titlepage-3"), ("repeat-2", "2")]
    pageMarkers := #["TitleEcho", "FirstBody", "TitleEcho", "AsideBody", "TitleEcho", "LastBody"]
    pageFooters := #[none, some ("", "1 / 2"), none, none, none, some ("", "2 / 2")]
    htmlFooters := #[("", "1 / 2"), ("", "2 / 2")]
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
  verify ref fonts "appendix labels shadow main reveal aliases" (elabStr (deck169
    (fractionTheme ++ "\\usepackage{appendixnumberbeamer}")
    ("\\begin{frame}{Appendix}MainAlpha\n\n\\pause\nMainBeta\\end{frame}\n" ++
     "\\appendix\n\\begin{frame}{Extra}ExtraBody\\end{frame}\n" ++
     "\\begin{frame}[standout]{Aside}ExtraAside\\end{frame}"))) {
    snaps := #[("appendix-1", "1.1"), ("appendix-2", "1.2"), ("extra", "appendix-1"),
      ("aside", "standout")]
    pageMarkers := #["MainAlpha", "MainAlpha", "ExtraBody", "ExtraAside"]
    pageFooters := #[some ("", "1 / 1"), some ("", "1 / 1"), some ("", "1 / 1"), none]
    htmlFooters := #[("", "1 / 1"), ("", "1 / 1")]
    tracks := #[("appendix", "1.1")]
    shadowedFragments := #["appendix-1"]
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
  let targets := #["1", "1.1", "1.2", "standout", "titlepage", "section-0", "section-1",
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
  t "stepped, semantic and appendix fragments resolve, first-step aliases too"
    (!htmlDs.any (·.code == "W0326"))
  let (missing, _) := elabStr (source
    "\\href{#missing-slide}{Missing}\\href{#missing-slide}{Again}")
  let (_, _, missingDs) := HtmlDoc.emitTree {} missing
  let unresolved := missingDs.filter (·.code == "W0326")
  t "a nonexistent fragment is still named once"
    (unresolved.size == 1 && unresolved.all (fun d => hasStr d.message "#missing-slide"))
  -- The exemption needs a shipped deck script; a static article has no canonical routes.
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

/-- Canonical fragments and authored aliases over the typed HTML, frame counts witnessed by page
order and footer ink. -/
def slideLabelChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  SlideLabels.mixedChecks ref fonts
  SlideLabels.numericAliasChecks ref fonts
  SlideLabels.appendixChecks ref fonts
  SlideLabels.standoutNoteChecks ref fonts
  SlideLabels.sectionChecks ref fonts
  SlideLabels.repeatedTitleChecks ref fonts
  SlideLabels.collisionChecks ref fonts
  SlideLabels.linkChecks ref
