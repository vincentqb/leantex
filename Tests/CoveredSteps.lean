module

public import Tests.Support

public section

open LeanTex.Core

/-! A pending step covers as the covering in force where it starts covers it, one a body declares
included, each run in the cover of its own colour and its marker with it, and a `\pause` reveals
the rest of its frame after it, wherever its scope ends, as beamer's pause counter does. -/

namespace Tests.CoveredSteps

/-- The colours of the runs a page sets with exactly `text`, in reading order. -/
def runColors (out : Layout.Out) (page : Nat) (text : String) : Array Ir.Color :=
  (out.pages[page]?.map fun p => p.lines.flatMap fun l => l.segs.filterMap fun s => match s with
    | .run _ c _ _ gs _ _ _ _ _ _ => if String.ofList (gs.map (·.2.1)).toList == text then some c else none
    | _ => none).getD #[]

/-- The runs of the line setting `word` on a page: text and left edge. -/
def lineOf (out : Layout.Out) (page : Nat) (word : String) : Array (String × Dim.Length) :=
  ((out.pages[page]?.bind fun p => p.lines.find? fun l => (wordRun #[l] word).isSome).map fun l =>
    (lineRuns l).map fun (_, s, x, _) => (s, x)).getD #[]

/-- The style an element carrying `cls` and holding `word` declares. -/
def styleHolding (tree : Array Html.Node) (cls word : String) : Option String :=
  (elemNodesList (fun _ => true) #[] tree.toList).findSome? fun n => match n with
    | .elem _ attrs kids =>
      if (((HtmlDoc.attrOf? attrs "class").getD "").splitOn " ").contains cls &&
          hasStr (nodeTextOne "" (.elem "div" #[] kids)) word then HtmlDoc.attrOf? attrs "style"
      else none
    | .text _ | .style _ | .script .. => none

/-- The styles of every element carrying `cls`, or of every one when `cls` is empty, and holding
`word`, outermost first. -/
def stylesHolding (tree : Array Html.Node) (cls word : String) : Array String :=
  (elemNodesList (fun _ => true) #[] tree.toList).filterMap fun n => match n with
    | .elem _ attrs kids =>
      if (cls.isEmpty || (((HtmlDoc.attrOf? attrs "class").getD "").splitOn " ").contains cls) &&
          hasStr (nodeTextOne "" (.elem "div" #[] kids)) word then
        some ((HtmlDoc.attrOf? attrs "style").getD "")
      else none
    | .text _ | .style _ | .script .. => none

/-- Whether the web page steps the frame `id` on a track of its own. -/
def stepsOnTrack (tree : Array Html.Node) (id : String) : Bool :=
  (elemAttrsList (fun _ => true) #[] tree.toList).any fun (_, a) =>
    HtmlDoc.attrOf? a "id" == some id && (HtmlDoc.attrOf? a "data-snapped").isSome

/-- A share or covered colour the body declares covers the steps after it, to its group's end, in
both artifacts, as beamer's `\setbeamercovered` does in the body. -/
def bodyShareChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← serifFacesSet | failures ref "body share: the serif faces load"
  let frames :=
    "\\begin{frame}{One}\nAlpha shows.\n\n\\pause\nBravo waits.\n\\end{frame}\n" ++
    "\\setbeamercovered{transparent}\n" ++
    "\\begin{frame}{Two}\nCharlie shows.\n\n\\pause\nDelta waits.\n\\end{frame}\n" ++
    "\\begin{frame}{Three}\nEcho shows.\n\n\\setbeamercovered{invisible}\n\\pause\nFoxtrot waits.\n" ++
    "\\end{frame}\n" ++
    "\\begin{frame}{Four}\nGolf shows.\n\n\\pause\nHotel waits.\n\\end{frame}"
  let (doc, ds) := elabStr (dvDeck "" frames)
  let out := layoutOf fonts doc
  let d := Ir.Design.ofDoc doc
  let cover := Oklab.cover 15 d.bg d.fg
  t "body share: no cover the body declares is named ignored" (!(ds.any (·.code == "W0340")))
  t "body share: one page per step" (out.pages.size == 8)
  t "body share: a frame before the body's share hides its pending step"
    ((wordOn out 0 "Bravo").isNone && wordOn out 1 "Bravo" == some d.fg)
  t "body share: the frames after it cover theirs at its 15%"
    (wordOn out 2 "Delta" == some cover && wordOn out 6 "Hotel" == some cover &&
      wordOn out 3 "Delta" == some d.fg && wordOn out 7 "Hotel" == some d.fg)
  t "body share: a share declared inside a frame covers to the frame's end"
    ((wordOn out 4 "Foxtrot").isNone && wordOn out 5 "Foxtrot" == some d.fg)
  let (_, tree, _) := HtmlDoc.emitTree {} doc
  let trackStyle (id : String) : String :=
    ((elemAttrsList (· == "div") #[] tree.toList).findSome? fun (_, a) =>
      if HtmlDoc.attrOf? a "id" == some id then HtmlDoc.attrOf? a "style" else none).getD ""
  t "body share, web page: the frames after it restate its share, in reach"
    (hasStr (trackStyle "two") "--ltx-step-share: 15%; --ltx-step-reach: initial" &&
      hasStr (trackStyle "four") "--ltx-step-share: 15%; --ltx-step-reach: initial" &&
      !hasStr (trackStyle "one") "--ltx-step-share")
  t "body share, web page: a share of none inside a frame hides its step, out of reach"
    ((styleHolding tree "step" "Foxtrot").any (hasStr · "--ltx-step-share: 0%; --ltx-step-reach: hidden"))
  let (html, _) := HtmlDoc.emit {} doc
  t "body share, web page: a step's share and reach read the properties an epoch restates"
    (hasStr html "opacity: var(--ltx-step-share, 0%)" &&
      hasStr html "visibility: var(--ltx-step-reach, inherit)" &&
      hasStr html "html { --ltx-step-reach: hidden; }")
  let (_, dynDs) := elabStr (dvDeck "" ("\\setbeamercovered{dynamic}\n" ++
    "\\begin{frame}\nKilo.\n\n\\pause\nLima.\n\\end{frame}"))
  t "body share: an approximated covering the body declares is named as the preamble's is"
    (dynDs.any (·.code == "W0109") && !(dynDs.any (·.code == "W0340")))
  for (pre, body) in [("\\setbeamercovered{transparent}\n", "\\setbeamercovered{highly dynamic}\n"),
      ("\\setbeamercovered{transparent=99}\n", "\\setbeamercovered{transparent=100}\n")] do
    let (_, sameDs) := elabStr (dvDeck pre (body ++ "\\begin{frame}\nKilo.\n\n\\pause\nLima.\n\\end{frame}"))
    t s!"body share: an approximation at the preamble's own share is named ({body.trimAscii.toString})"
      ((sameDs.filter (·.code == "W0109")).size == 1 && !(sameDs.any (·.code == "W0340")))
  let grey := Ir.Color.ofHtml 0x77 0x77 0x77
  let (colDoc, colDs) := elabStr (dvDeck "\\setbeamercovered{transparent}\n"
    ("\\begin{frame}{A}\nKilo shows.\n\n\\pause\nLima waits.\n\\end{frame}\n" ++
     "\\palette{ covered = #777777 }\n" ++
     "\\begin{frame}{B}\nMike shows.\n\n\\pause\nNovember waits.\n\\end{frame}"))
  let colOut := layoutOf fonts colDoc
  let cd := Ir.Design.ofDoc colDoc
  t "body covered colour: the frames after it cover runs with no colour of their own in it"
    (!(colDs.any (·.code == "W0340")) && wordOn colOut 0 "Lima" == some (Oklab.cover 15 cd.bg cd.fg) &&
      wordOn colOut 2 "November" == some grey)
  let pre := "\\setbeamercovered{transparent}\n"
  let (lateDoc, _) := elabStr (dvDeck pre
    ("\\begin{frame}{T}\nAlpha.\n\n\\uncover<2->{Bravo.}\n\n\\uncover<3->{Charlie.}\n\n" ++
     "\\setbeamercovered{invisible}\n\nDelta.\n\\end{frame}\n" ++
     "\\begin{frame}{U}\nEcho.\n\n\\pause\nFoxtrot.\n\n\\setbeamercovered{invisible}\n\n\\pause\n" ++
     "Golf.\n\\end{frame}"))
  let lateOut := layoutOf fonts lateDoc
  let ld := Ir.Design.ofDoc lateDoc
  t "frame share: every step covers what starts before a share the frame declares at the share before it"
    (wordOn lateOut 1 "Charlie." == some (Oklab.cover 15 ld.bg ld.fg) && wordOn lateOut 2 "Charlie." == some ld.fg)
  let (_, lateTree, _) := HtmlDoc.emitTree {} lateDoc
  let (lateHtml, _) := HtmlDoc.emit {} lateDoc
  t "frame share, web page: a step inside a covered one hides by its own covering"
    ((stylesHolding lateTree "step" "Golf").any (hasStr · "--ltx-step-reach: hidden") &&
      hasStr lateHtml ("[data-snapped=\"1\"] :is(.step, .step-set):not([data-steps~=\"1\"]) " ++
        ":is(.step, .step-set):not(.step-hide):not([data-steps~=\"1\"]) " ++
        "{ visibility: var(--ltx-step-reach, inherit); }"))
  let (altDoc, _) := elabStr (dvDeck pre
    ("\\begin{frame}{A}\nKilo.\n\n\\only<3>{Lima.\n\n\\setbeamercovered{invisible}\n\n}\n\n" ++
     "\\uncover<2->{Mike.}\n\n\\uncover<4->{November.}\n\\end{frame}"))
  let altOut := layoutOf fonts altDoc
  let ad := Ir.Design.ofDoc altDoc
  let altCover := Oklab.cover 15 ad.bg ad.fg
  t "alternative share: it covers past the alternative on the steps that set it, as beamer's does"
    (wordOn altOut 0 "Mike." == some altCover && wordOn altOut 0 "November." == some altCover &&
      wordOn altOut 1 "November." == some altCover && (wordOn altOut 2 "November.").isNone)
  let (_, altTree, _) := HtmlDoc.emitTree {} altDoc
  let novSteps := stylesHolding altTree "step" "November."
  t "alternative share, web page: one set on some steps only hides nothing past the alternative"
    (!novSteps.isEmpty && (stylesHolding altTree "" "November.").all fun st =>
      !hasStr st "--ltx-step-reach: hidden" && !hasStr st "--ltx-step-share: 0%")
  let (allDoc, _) := elabStr (dvDeck pre
    ("\\begin{frame}{B}\nNovember.\n\n\\only<1->{Oscar.\n\n\\setbeamercovered{invisible}\n\n}\n\n" ++
     "\\pause\nPapa.\n\\end{frame}"))
  let allOut := layoutOf fonts allDoc
  let (_, allTree, _) := HtmlDoc.emitTree {} allDoc
  t "alternative share: one set on every step covers past the alternative in both artifacts"
    ((wordOn allOut 0 "Papa.").isNone && (wordOn allOut 1 "Papa.").isSome &&
      (stylesHolding allTree "step" "Papa.").any (hasStr · "--ltx-step-reach: hidden"))
  let (soDoc, _) := elabStr (dvDeck pre
    "\\begin{frame}[standout]\nRomeo.\n\n\\setbeamercovered{invisible}\n\n\\pause\nSierra.\n\\end{frame}")
  let (_, soTree, _) := HtmlDoc.emitTree {} soDoc
  let soSteps := stylesHolding soTree "step" "Sierra."
  t "frame share, web page: a share alone keeps the ink the frame sets"
    (soSteps.any (hasStr · "--ltx-step-reach: hidden") &&
      soSteps.all fun st => !hasStr st ("color: " ++ HtmlDoc.roleRef .ink))

/-- A covered run takes the cover of the colour in force, a body's ink, an enclosing colour or a
marker's own, and an item's marker covers only where its item does. -/
def dimPathChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← serifFacesSet | failures ref "dim path: the serif faces load"
  let red := Ir.Color.ofHtml 0xFF 0x00 0x00
  let blue := Ir.Color.ofHtml 0x00 0x00 0xFF
  let pre := "\\setbeamercovered{transparent}\n"
  let (mDoc, _) := elabStr (dvDeck (pre ++ "\\style{itemize}{ marker = {\\textcolor{red}{*}} }\n")
    "\\begin{frame}\n\\begin{itemize}\n\\item Kilo shows.\n\\item<2-> Lima waits.\n\\end{itemize}\n\\end{frame}")
  let mOut := layoutOf fonts mDoc
  let md := Ir.Design.ofDoc mDoc
  t "dim path: a pending item's marker of its own colour covers in that colour"
    (runColors mOut 0 "*" == #[red, Oklab.cover 15 md.bg red] && runColors mOut 1 "*" == #[red, red])
  let (pDoc, _) := elabStr (dvDeck "\\style{itemize}{ marker = {*} }\n"
    "\\begin{frame}\n\\begin{itemize}\n\\item \\textcolor{red}{Kilo all red.}\n\\item Lima plain.\n\\end{itemize}\n\\end{frame}")
  let pOut := layoutOf fonts pDoc
  let pd := Ir.Design.ofDoc pDoc
  t "dim path: an item whose text is all one colour keeps its marker in the ink"
    (runColors pOut 0 "*" == #[pd.fg, pd.fg] && wordOn pOut 0 "Kilo" == some red)
  let (iDoc, _) := elabStr (dvDeck pre
    "\\begin{frame}\n\\color{blue}Kilo shows.\n\n\\pause\nLima waits.\n\\end{frame}")
  let iOut := layoutOf fonts iDoc
  let id := Ir.Design.ofDoc iDoc
  t "dim path: a body ink covers in its own cover, not the preamble ink's"
    (wordOn iOut 0 "Kilo" == some blue && wordOn iOut 0 "Lima" == some (Oklab.cover 15 id.bg blue))
  let (cDoc, _) := elabStr (dvDeck pre
    "\\begin{frame}\n\\textcolor{red}{Kilo \\uncover<2>{Lima}} words.\n\\end{frame}")
  let cOut := layoutOf fonts cDoc
  let cd := Ir.Design.ofDoc cDoc
  t "dim path: a pending step inside a colour covers in that colour's cover"
    (wordOn cOut 0 "Lima" == some (Oklab.cover 15 cd.bg red) && wordOn cOut 1 "Lima" == some red)
  let (dDoc, _) := elabStr (dvDeck pre
    "\\begin{frame}\n\\begin{description}\n\\item[One] India.\n\\pause\n\\item[Two] Juliet.\n\\end{description}\n\\end{frame}")
  let dOut := layoutOf fonts dDoc
  t "dim path: a covered description item runs its label in where it runs shown, no marker set"
    (lineOf dOut 0 "Juliet." == lineOf dOut 1 "Juliet." &&
      ((lineOf dOut 0 "Juliet.")[0]?.map (·.1)) == some "Two")
  let (nDoc, _) := elabStr (dvDeck (pre ++ "\\palette{ covered = #777777 }\n\\style{itemize}{ marker = {*} }\n")
    "\\begin{frame}\n\\begin{itemize}\n\\item \\textcolor{covered}{Kilo quiet.}\n\\end{itemize}\n\\end{frame}")
  let nOut := layoutOf fonts nDoc
  let nd := Ir.Design.ofDoc nDoc
  t "dim path: an item set in the covered colour, on no step, keeps its marker in the ink"
    (runColors nOut 0 "*" == #[nd.fg] && wordOn nOut 0 "Kilo" == some (Ir.Color.ofHtml 0x77 0x77 0x77))
  let (fDoc, _) := elabStr (dvDeck pre
    "\\begin{frame}{V}\nAlpha.\n\n\\pause\nBravo.\n\n\\palette{ fg = #AA0000 }\n\nCharlie.\n\\end{frame}")
  let fOut := layoutOf fonts fDoc
  let fd := Ir.Design.ofDoc fDoc
  t "dim path: each step opens in the colours its frame opens in"
    (wordOn fOut 1 "Alpha." == some fd.fg && wordOn fOut 1 "Charlie." == some (Ir.Color.ofHtml 0xAA 0 0))
  let marked := "\\style{itemize}{ marker = {*} }\n"
  let (aDoc, _) := elabStr ("\\documentclass{article}\n" ++ marked ++ "\\begin{document}\nAlpha.\n\n" ++
    "\\pause\nBravo.\n\\begin{itemize}\n\\item Charlie.\n\\item<2-> Delta.\n\\end{itemize}\n\\end{document}")
  let aOut := layoutOf fonts aDoc
  let ad := Ir.Design.ofDoc aDoc
  t "dim path: an item stepped outside every frame keeps its marker in the ink"
    (runColors aOut 0 "*" == #[ad.fg, ad.fg])
  let (lDoc, _) := elabStr (dvDeck (pre ++ marked)
    ("\\begin{frame}{A}\nAlpha.\n\\end{frame}\n\\begin{itemize}\n\\item<2-> Charlie.\n\\end{itemize}\n" ++
     "\\begin{frame}{B}\nEcho.\n\\end{frame}"))
  let lOut := layoutOf fonts lDoc
  let ld := Ir.Design.ofDoc lDoc
  t "dim path: an item stepped between frames keeps its marker in the ink beside its text"
    (runColors lOut 1 "*" == #[ld.fg] && wordOn lOut 1 "Charlie." == some ld.fg)

/-- A `\pause` reveals what follows it in reading order after it, past its column, list or block,
and a block beamer typesets on some steps only counts its pauses there. -/
def pauseScopeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← serifFacesSet | failures ref "pause scope: the serif faces load"
  let shipsOn (out : Layout.Out) (page : Nat) (ws : List String) : Bool :=
    ws.all fun w => (wordOn out page w).isSome
  let hidesOn (out : Layout.Out) (page : Nat) (ws : List String) : Bool :=
    ws.all fun w => (wordOn out page w).isNone
  let build (body : String) : Ir.Doc × Layout.Out :=
    let doc := (elabStr (dvDeck "" ("\\begin{frame}\n" ++ body ++ "\n\\end{frame}"))).1
    (doc, layoutOf fonts doc)
  let (colDoc, cols) := build ("\\begin{columns}\n\\column{0.45\\textwidth}\nKilo one.\n\n\\pause\n" ++
    "Lima two.\n\\column{0.45\\textwidth}\nMike three.\n\\end{columns}\nNovember four.")
  t "pause scope: a pause in a column hides the next column and what follows the columns"
    (cols.pages.size == 2 && shipsOn cols 0 ["Kilo"] && hidesOn cols 0 ["Lima", "Mike", "November"] &&
      shipsOn cols 1 ["Kilo", "Lima", "Mike", "November"])
  let (_, colTree, _) := HtmlDoc.emitTree {} colDoc
  t "pause scope, web page: the next column and what follows the columns step at the pause's step"
    ((styleHolding colTree "step" "Mike").isSome && (styleHolding colTree "step" "November").isSome)
  let (_, nested) := build ("\\begin{itemize}\n\\item Kilo one.\n\\begin{itemize}\n\\item Lima two.\n" ++
    "\\end{itemize}\n\\pause\n\\item Mike three.\n\\end{itemize}\nNovember four.")
  t "pause scope: a pause after a nested list hides the next item and what follows the list"
    (nested.pages.size == 2 && shipsOn nested 0 ["Kilo", "Lima"] && hidesOn nested 0 ["Mike", "November"] &&
      shipsOn nested 1 ["Mike", "November"])
  let (_, inner) := build ("\\begin{itemize}\n\\item Kilo one.\n\\begin{itemize}\n\\item Lima two.\n" ++
    "\\pause\n\\item Mike three.\n\\end{itemize}\n\\item November four.\n\\end{itemize}")
  t "pause scope: a pause in a nested list hides the outer items after it"
    (inner.pages.size == 2 && shipsOn inner 0 ["Kilo", "Lima"] && hidesOn inner 0 ["Mike", "November"] &&
      shipsOn inner 1 ["Mike", "November"])
  let (_, unc) := build ("Kilo one.\n\n\\uncover<3>{Lima two.\n\n\\pause\n\nMike three.}\n\nNovember four.")
  t "pause scope: a pause inside a block uncover counts from the frame's pauses, its rest shown"
    (unc.pages.size == 3 && shipsOn unc 0 ["Kilo"] && hidesOn unc 0 ["Lima", "Mike", "November"] &&
      shipsOn unc 1 ["November"] && hidesOn unc 1 ["Lima", "Mike"] &&
      shipsOn unc 2 ["Lima", "Mike", "November"])
  let (_, only) := build ("Kilo one.\n\n\\only<2>{Lima two.\n\n\\pause\n\nMike three.}\n\nNovember four.")
  t "pause scope: a pause beamer typesets on one step only counts on none of the others"
    (only.pages.size == 2 && shipsOn only 0 ["Kilo", "November"] && hidesOn only 0 ["Lima", "Mike"] &&
      shipsOn only 1 ["Kilo", "Lima", "Mike", "November"])
  let spec := layoutOf fonts (elabStr (dvDeck "\\style{itemize}{ marker = {*} }\n"
    ("\\begin{frame}\n\\begin{itemize}\n\\item Kilo one.\n\\pause\n\\item<3-> Lima two.\n" ++
      "\\item Mike three.\n\\end{itemize}\n\\end{frame}"))).1
  t "pause scope: an item's own selector after a pause keeps its marker on its line"
    (spec.pages.size == 3 && hidesOn spec 1 ["Lima"] && shipsOn spec 1 ["Mike"] &&
      (lineOf spec 2 "Lima").any (·.1 == "*"))
  let (_, desc) := build ("\\begin{description}\n\\item[One] India.\n\\pause\n\\item[Two] Juliet.\n" ++
    "\\end{description}")
  t "pause scope: a description item after a pause hides its label with it"
    (hidesOn desc 0 ["Two", "Juliet."] && shipsOn desc 1 ["Two", "Juliet."])
  let frameA := "\\begin{frame}{A}\nAlpha.\n\n\\pause\nBravo.\n"
  let frameB := "\\begin{frame}{B}\nEcho.\n\n\\pause\nFoxtrot.\n\\end{frame}"
  for (what, between, loose) in [
      ("in a note", "\\note{Charlie.\n\n\\pause\nDelta.}\n\\end{frame}\n", false),
      ("between frames", "\\end{frame}\n\n\\pause\n\n", false),
      ("in a list between frames",
        "\\end{frame}\n\\begin{itemize}\n\\item Charlie.\n\\pause\n\\item Delta.\n\\end{itemize}\n", true)] do
    let (doc, ds) := elabStr (dvDeck "" (frameA ++ between ++ frameB))
    let out := layoutOf fonts doc
    let b := if loose then 3 else 2
    let (_, tree, _) := HtmlDoc.emitTree {} doc
    t s!"pause scope: a pause {what} reveals nothing, named, the next frame keeping its steps"
      (out.pages.size == b + 2 && shipsOn out b ["Echo."] && hidesOn out b ["Foxtrot."] &&
        shipsOn out (b + 1) ["Echo.", "Foxtrot."] && (!loose || shipsOn out 2 ["Charlie.", "Delta."]) &&
        stepsOnTrack tree "b" && ds.any (·.code == "W0105"))

end Tests.CoveredSteps
