module

public import Tests.Support

public section

open LeanTex.Core

/-! A table of contents over `Layout.Out` and the typed HTML tree, beamer's and article's measured
under lualatex on invented documents. -/

namespace ContentsChecks

/-- The first line on page `i` whose text holds `word`. -/
private def lineWith (out : Layout.Out) (i : Nat) (word : String) : Option Layout.LineOut :=
  (out.pages[i]?).bind fun p => p.lines.find? fun l => hasStr (lineText l) word

/-- The colour, link and face of a line's first glyph run. -/
private def firstRun (l : Layout.LineOut) : Option (Ir.Color × Option String × Nat) :=
  l.segs.findSome? fun s => match s with
    | .run fontIdx color link _ _ _ _ _ _ _ _ => some (color, link, fontIdx)
    | _ => none

/-- The right edge of a line's last glyph run, from the line's origin. -/
private def inkEnd (l : Layout.LineOut) : Dim.Length :=
  (l.segs.foldl (fun (acc : Dim.Length × Dim.Length) s =>
    let x := acc.1 + s.advance
    match s with
    | .run .. => (x, x)
    | _ => (x, acc.2)) (l.x, l.x)).2

/-- The page an entry's link lands on, its first linked run's. -/
private def landsOn (out : Layout.Out) (l : Layout.LineOut) : Option Nat :=
  (l.segs.findSome? fun s => match s with
    | .run _ _ (some url) .. => some url
    | _ => none).bind fun url =>
      (Layout.destination? out.pages ((url.drop 1).toString)).map (·.1)

/-- The contents' lines of page 0: those above the first line holding `body`. -/
private def contentsLines (out : Layout.Out) (body : String) : Array Layout.LineOut :=
  match out.pages[0]? with
  | some p => p.lines.takeWhile fun l => !hasStr (lineText l) body
  | none => #[]

/-- The contents navigations of an emitted body, each as its entries' classes, words and links. -/
private def navEntries (body : Array Html.Node) : Array (Array (String × String × String)) :=
  (elemNodesList (· == "nav") #[] body.toList).filterMap fun n => match n with
    | .elem _ attrs kids =>
      if !((HtmlDoc.attrOf? attrs "class").getD "").startsWith "contents" then none else
      some ((elemNodesList (fun t => t == "p" || t == "li") #[] kids.toList).filterMap fun k =>
        match k with
        | .elem _ pattrs _ =>
          let href := ((elemNodesList (· == "a") #[] [k])[0]?).bind fun a => match a with
            | .elem _ aattrs _ => HtmlDoc.attrOf? aattrs "href"
            | _ => none
          some ((HtmlDoc.attrOf? pattrs "class").getD "", (nodeTextOne "" k).trimAscii.toString,
            href.getD "")
        | _ => none)
    | _ => none

/-- Whether an emitted body carries an element answering to `id`. -/
private def holdsId (body : Array Html.Node) (id : String) : Bool :=
  (elemNodesList (fun _ => true) #[] body.toList).any fun k => match k with
    | .elem _ attrs _ => HtmlDoc.attrOf? attrs "id" == some id
    | _ => false

private def deckSrc (toc : String) : String :=
  "\\documentclass{beamer}\n\\usetheme{default}\n" ++
  "\\AtBeginSection[]{\\begin{frame}{Outline}\\tableofcontents[currentsection]\\end{frame}}\n" ++
  "\\begin{document}\n" ++
  s!"\\begin\{frame}\{Overview}{toc}\\end\{frame}\n" ++
  "\\section{Kettles}\n\\begin{frame}{Boiling}Water boils.\\end{frame}\n" ++
  "\\subsection{Spouts}\n\\begin{frame}{Pouring}Tea pours.\\end{frame}\n" ++
  "\\section{Teapots}\n\\begin{frame}{Steeping}Leaves steep.\\end{frame}\n" ++
  "\\section{Trays}\n\\begin{frame}{Carrying}Trays carry.\\end{frame}\n" ++
  "\\section*{Saucers}\n\\begin{frame}{Resting}Cups rest.\\end{frame}\n" ++
  "\\end{document}\n"

private def flowSrc (pre : String) : String :=
  "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\n\\tableofcontents\n" ++
  "\\section{Kettles}\nWater boils.\n\\subsection{Spouts}\nTea pours.\n\\newpage\n" ++
  "\\section{Teapots}\nLeaves steep.\n\\subsubsection{Lids}\nLids rattle.\n" ++
  "\\section*{Saucers}\nCups rest.\n\\end{document}\n"

end ContentsChecks

open ContentsChecks in
/-- A deck's `\tableofcontents` and its `currentsection` replay in a hook frame, and an article's
with its folios, over the pages and the web page both backends set from one contents block. -/
def contentsChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := fun claim => check ref ("contents / " ++ claim)
  -- A deck: the overview frame, then the hook's outline before each unstarred section.
  let (deck, deckDiags) := elabStr (deckSrc "\\tableofcontents")
  let out := (fittedOf fonts deck).out
  t s!"a deck's contents build clean ({deckDiags.toList.map (·.code)})"
    (!deckDiags.any fun d => d.severity == .error || d.code == "W0301" || d.code == "W0307")
  t s!"the hook's outline stands before each unstarred section, none before the starred one \
({out.pages.size} pages)" (out.pages.size == 9)
  let words := ["Kettles", "Spouts", "Teapots", "Trays"]
  let ys (i : Nat) : List (Option Dim.Length) := words.map fun w => (lineWith out i w).map (·.y)
  t "the contents list the unstarred sections and subsections in order, not the starred one"
    ((ys 0).all Option.isSome && (lineWith out 0 "Saucers").isNone &&
      (ys 0).filterMap id == ((ys 0).filterMap id).mergeSort (· ≤ ·))
  let x (w : String) : Option Dim.Length := (lineWith out 0 w).map (·.x)
  let size := ((lineWith out 0 "Kettles").map (·.size)).getD 0
  t "a subsection's entry stands 1.5em in from its section's, the default inner theme's leftskip"
    (((x "Spouts").bind fun s => (x "Kettles").map fun k => s - k == size * 3 / 2) == some true)
  -- beamer's `\vfill` before each section entry: equal leftovers between the section groups.
  match ys 0 with
  | [some k, some s, some te, some tr] =>
    let pitch := s - k
    t s!"the sections' groups share the frame's leftover equally ({reprStr (te - s - pitch)}, {reprStr (tr - te - pitch)})"
      ((te - s - pitch - (tr - te - pitch)).abs ≤ Dim.Length.quantum && te - s - pitch > 0)
  | _ => t "the overview's four entries ship" false
  -- beamer's links: a section's entry opens the page set after it, a subsection's its frame.
  let lands (w : String) : Option Nat := (lineWith out 0 w).bind (landsOn out)
  t s!"each entry opens the page beamer's opens ({words.map lands})"
    (words.map lands == [some 1, some 3, some 4, some 6])
  -- `currentsection`: the other sections and their subsections shaded, the current one shown.
  let design := Ir.Design.ofPalette deck.palette
  let shade := Oklab.cover Ir.contentsShadeShare design.bg design.fg
  let color (i : Nat) (w : String) : Option Ir.Color :=
    ((lineWith out i w).bind firstRun).map (·.1)
  t "the first outline shows Kettles and its subsection, the later sections shaded"
    (color 1 "Kettles" == some design.fg && color 1 "Spouts" == some design.fg &&
      color 1 "Teapots" == some shade && color 1 "Trays" == some shade)
  t "the second outline shows Teapots alone, the others and their subsections shaded"
    (color 4 "Kettles" == some shade && color 4 "Spouts" == some shade &&
      color 4 "Teapots" == some design.fg && color 4 "Trays" == some shade)
  -- `hideallsubsections`: no subsection entry, and a section's entry after `\vskip1.5em`.
  let (tight, _) := elabStr (deckSrc "\\tableofcontents[hideallsubsections]")
  let tout := (fittedOf fonts tight).out
  let ty (w : String) : Option Dim.Length := (lineWith tout 0 w).map (·.y)
  t "hidden subsections leave their sections a 1.5em skip apart"
    ((lineWith tout 0 "Spouts").isNone &&
      ((ty "Kettles").bind fun k => (ty "Teapots").bind fun te => (ty "Trays").map fun tr =>
        te - k == tr - te && te - k > size * 3 / 2) == some true)
  -- The web deck sets the same entries in a named landmark, each linking the stage its PDF opens.
  let (_, body, _) := HtmlDoc.emitTree {} deck
  let navs := navEntries body
  t s!"the web deck lists the same entries in each contents landmark ({navs.size})"
    (navs.size == 4 && navs.all fun es => es.map (·.2.1) == #["Kettles", "Spouts", "Teapots", "Trays"])
  t "every entry's link names a stage of the web deck"
    (navs.all fun es => es.all fun (_, _, href) => href.startsWith "#" &&
      holdsId body (href.drop 1).toString)
  t "the outlines shade as the PDF does"
    ((navs[1]?.map fun es => es.map fun (c, _, _) => hasStr c "shaded") ==
      some #[false, false, true, true])
  -- A flow: article's contents with the folio of each heading's page, after the Contents heading.
  let (flow, flowDiags) := elabStr (flowSrc "")
  let fout := (fittedOf fonts flow).out
  t s!"an article's contents build clean ({flowDiags.toList.map (·.code)})"
    (!(flowDiags ++ fout.diags).any fun d => d.severity == .error || d.code == "W0301" ||
      d.code == "W0326")
  let fl (w : String) : Option Layout.LineOut := lineWith fout 0 w
  let flowYs := ["Contents", "Kettles", "Spouts", "Teapots", "Lids"].filterMap fun w =>
    (fl w).map (·.y)
  t "the contents stand under their heading, listing the unstarred headings in order"
    ((fl "Saucers").isNone && flowYs.length == 5 && flowYs == flowYs.mergeSort (· ≤ ·))
  let em := flow.page.fontSize
  let geom := Layout.Geom.ofPage flow.page
  let left := geom.hmargin
  t "a section's number stands at the margin, its title 1.5em in, as article's numberline"
    ((fl "Kettles").map (·.x) == some left)
  t "a subsection's number stands 1.5em in, a subsubsection's 3.8em"
    ((fl "Spouts").map (·.x) == some (left + em * 3 / 2) &&
      (fl "Lids").map (·.x) == some (left + em * 38 / 10))
  t "each entry ends on its heading's folio, right-aligned at the measure's end"
    (["Kettles", "Spouts", "Teapots", "Lids"].all fun w => match fl w with
      | some l => inkEnd l == left + geom.textWidth || inkEnd l + Dim.Length.quantum ≥ left + geom.textWidth
      | none => false)
  t "the folios are the pages the headings land on"
    (((fl "Kettles").map lineText).any (·.trimAscii.toString.endsWith "1") &&
      ((fl "Spouts").map lineText).any (·.trimAscii.toString.endsWith "1") &&
      ((fl "Teapots").map lineText).any (·.trimAscii.toString.endsWith "2") &&
      ((fl "Lids").map lineText).any (·.trimAscii.toString.endsWith "2"))
  t "each entry opens its heading's page"
    (["Kettles", "Spouts", "Teapots", "Lids"].map (fun w => (fl w).bind (landsOn fout)) ==
      [some 0, some 0, some 1, some 1])
  let (shallow, _) := elabStr (flowSrc "\\setcounter{tocdepth}{1}\n")
  let listed := (contentsLines (fittedOf fonts shallow).out "Water boils").map lineText
  t "tocdepth 1 lists the sections alone"
    (!listed.any (hasStr · "Spouts") && listed.any (hasStr · "Teapots"))
  let (deep, deepDiags) := elabStr (flowSrc "\\setcounter{tocdepth}{4}\n" |>.replace "Lids rattle."
    "Lids rattle.\n\\paragraph{Steam} Steam rises.")
  let deepListed := (contentsLines (fittedOf fonts deep).out "Water boils").map lineText
  t "a tocdepth past subsubsections is named, a run-in paragraph heading set in its text, not listed"
    (deepDiags.any (fun d => d.code == "W0104" && d.subject == some "contents:tocdepth") &&
      !deepListed.any (hasStr · "Steam") && deepListed.any (hasStr · "Lids"))
  let (_, fbody, _) := HtmlDoc.emitTree {} flow
  let fnav := navEntries fbody
  t "the web page lists the same entries, each linking a heading it carries"
    (fnav.size == 1 && fnav.all fun es =>
      es.map (·.2.1) == #["1 Kettles", "1.1 Spouts", "2 Teapots", "2.0.1 Lids"] &&
        es.all fun (_, _, href) => holdsId fbody (href.drop 1).toString)
  -- A page reference prints the folio its label lands on, in a flow and in a deck.
  let (paged, pagedDiags) := elabStr ("\\documentclass{article}\n\\begin{document}\n" ++
    "\\section{Kettles}\\label{sec:k}\nWater boils, as page~\\pageref{sec:t} says.\n\\newpage\n" ++
    "\\section{Teapots}\\label{sec:t}\nBack to page~\\pageref*{sec:k} again.\n\\end{document}\n")
  let pout := (fittedOf fonts paged).out
  t s!"a page reference builds clean ({pagedDiags.toList.map (·.code)})"
    (!pagedDiags.any fun d => d.severity == .error || d.code == "W0307" || d.code == "W0349")
  let said (i : Nat) (w : String) : String := ((lineWith pout i w).map fun l => letters (lineText l)).getD ""
  t "a page reference prints the folio of its label's page, its link opening it"
    (hasStr (said 0 "as page") "aspage2says" && (lineWith pout 0 "as page").bind (landsOn pout) == some 1)
  t "a starred page reference prints its folio unlinked"
    (hasStr (said 1 "Back to") "page1again" && ((lineWith pout 1 "Back to").bind (landsOn pout)).isNone)
  let (_, pbody, pds) := HtmlDoc.emitTree {} paged
  t "the web page, which has no pages, sets no folio for it and names the loss"
    (!hasStr (nodeTextList "" pbody.toList) "??" && pds.any (·.code == "W0007"))
  let (pdeck, _) := elabStr ("\\documentclass{beamer}\n\\begin{document}\n" ++
    "\\begin{frame}{One}See page \\pageref{three}.\\end{frame}\n" ++
    "\\begin{frame}{Two}\\only<1>{A}\\only<2>{B}\\end{frame}\n" ++
    "\\begin{frame}{Three}\\label{three}Words.\\end{frame}\n\\end{document}\n")
  let dout := (fittedOf fonts pdeck).out
  t "a deck's page reference prints its frame's first page, as beamer's"
    (((lineWith dout 0 "See page").map lineText).any (hasStr · "See page 4"))
  -- The twin lists the entries as the list its reader reads back, a fixed point of the round trip.
  let twin := MarkdownDoc.emit flow
  t "the twin lists the entries, nested as the headings are"
    (hasStr twin "- 1 Kettles\n  - 1.1 Spouts\n- 2 Teapots\n  - 2.0.1 Lids\n")
  t "the twin reads back to itself" (MarkdownDoc.emit (elabMd twin).1 == twin)

namespace ContentsChecks

private def edgeDeck (pre body : String) : String :=
  "\\documentclass{beamer}\n\\usetheme{default}\n" ++ pre ++ "\\begin{document}\n" ++ body ++
    "\\end{document}\n"

private def outlineDeck (hook : String) : String :=
  edgeDeck ("\\setcounter{secnumdepth}{0}\n\\AtBeginSection[]{" ++ hook ++ "}\n")
    ("\\section{Kettles}\n\\begin{frame}{Boiling}Water boils.\\end{frame}\n" ++
     "\\section{Teapots}\n\\begin{frame}{Steeping}Leaves steep.\\end{frame}\n")

/-- Where each leader dot's box opens on a line's rider, from the line's origin. -/
private def dotStarts (rider : Layout.LineOut) : Array Dim.Length :=
  (rider.segs.foldl (fun (acc : Dim.Length × Array Dim.Length) s => match s with
    | .gap w _ => (acc.1 + w, acc.2)
    | .poly .. => (acc.1, acc.2.push acc.1)
    | _ => (acc.1 + s.advance, acc.2)) (0, #[])).2

/-- Where a line's leader gap opens, from its origin. -/
private def leaderGapAt (l : Layout.LineOut) : Option Dim.Length :=
  (l.segs.foldl (fun (acc : Dim.Length × Option Dim.Length) s => match s with
    | .decoratedGap _ _ d => (acc.1 + s.advance, acc.2.orElse fun _ =>
        if d.leaders.isSome then some acc.1 else none)
    | _ => (acc.1 + s.advance, acc.2)) (0, none)).2

/-- The size of the run on a line whose glyphs spell `word`. -/
private def runSize (l : Layout.LineOut) (word : String) : Option Dim.Length :=
  l.segs.findSome? fun s => match s with
    | .run _ _ _ _ glyphs size .. =>
      if String.ofList (glyphs.toList.map (·.2.1)) == word then some size else none
    | _ => none

/-- The font of the run on a line whose glyphs spell `word`. -/
private def runFont (l : Layout.LineOut) (word : String) : Option Nat :=
  l.segs.findSome? fun s => match s with
    | .run fontIdx _ _ _ glyphs .. =>
      if String.ofList (glyphs.toList.map (·.2.1)) == word then some fontIdx else none
    | _ => none

end ContentsChecks

open ContentsChecks in
/-- A table of contents' edges against beamer's and article's: a deck's depth, subsubsections,
blank and counted headings, its frame command and section pages; a flow's folio kept with its words,
leader dots clear of the title, a section's number bold, short titles, and anchors apart. -/
def contentsEdgeChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := fun claim => check ref ("contents edges / " ++ claim)
  let deckBody := "\\begin{frame}{Overview}\\tableofcontents\\end{frame}\n" ++
    "\\section{Kettles}\n\\subsection{Spouts}\n\\subsubsection{Lids}\n" ++
    "\\begin{frame}{Boiling}Water boils.\\end{frame}\n\\section{}\n" ++
    "\\begin{frame}{Blank}Cups rest.\\end{frame}\n\\section{Teapots}\n" ++
    "\\begin{frame}{Steeping}Leaves steep.\\end{frame}\n"
  let (deck, _) := elabStr (edgeDeck "" deckBody)
  let out := (fittedOf fonts deck).out
  let lw (o : Layout.Out) (i : Nat) (w : String) : Option Layout.LineOut := lineWith o i w
  t "beamer's default depth lists a subsubsection at 3em, smaller than its section"
    (match lw out 0 "Kettles", lw out 0 "Lids" with
      | some k, some l => l.x - k.x == k.size * 3 &&
        (match runSize l "Lids", runSize k "Kettles" with
          | some a, some b => decide (a < b)
          | _, _ => false)
      | _, _ => false)
  let (_, body, _) := HtmlDoc.emitTree {} deck
  t "a blank-titled section is listed by nothing, as beamer writes no entry for it"
    ((navEntries body)[0]?.map (·.map (·.2.1)) == some #["Kettles", "Spouts", "Lids", "Teapots"])
  t "no contents link is empty" ((HtmlDoc.a11yFacts true true body).linksUnnamed == 0)
  let (shallow, _) := elabStr (edgeDeck "\\setcounter{tocdepth}{1}\n" deckBody)
  let sout := (fittedOf fonts shallow).out
  t "a deck's tocdepth 1 lists its sections alone"
    ((lw sout 0 "Kettles").isSome && (lw sout 0 "Teapots").isSome &&
      (lw sout 0 "Spouts").isNone && (lw sout 0 "Lids").isNone)
  -- secnumdepth 0 leaves beamer's counters stepping, so the outline still finds its section.
  let design (d : Ir.Doc) := Ir.Design.ofPalette d.palette
  let shown (d : Ir.Doc) (o : Layout.Out) (i : Nat) (w : String) : Bool :=
    ((lw o i w).bind firstRun).map (·.1) == some (design d).fg
  for (label, hook) in [("an environment frame",
      "\\begin{frame}{Outline}\\tableofcontents[currentsection]\\end{frame}"),
      ("beamer's frame command", "\\frame{\\frametitle{Outline}\\tableofcontents[currentsection]}")] do
    let (od, ods) := elabStr (outlineDeck hook)
    let oo := (fittedOf fonts od).out
    t s!"{label}: each outline shows its own section past secnumdepth 0 ({oo.pages.size} pages)"
      (oo.pages.size == 4 && shown od oo 0 "Kettles" && !shown od oo 0 "Teapots" &&
        !shown od oo 2 "Kettles" && shown od oo 2 "Teapots" &&
        !ods.any fun d => d.code == "W0301")
  let (fd, fds) := elabStr (edgeDeck "" "\\frame{Words in a frame.}\n\\frame[plain]{More words.}\n")
  t "beamer's frame command sets a frame"
    ((fittedOf fonts fd).out.pages.size == 2 && !fds.any fun d => d.code == "W0301")
  let (sd, sds) := elabStr (edgeDeck "\\AtBeginSubsection{\\begin{frame}\\subsectionpage\\end{frame}}\n"
    "\\section{Kettles}\n\\subsection{Spouts}\n\\begin{frame}{Pouring}Tea pours.\\end{frame}\n")
  let so := (fittedOf fonts sd).out
  t "a subsection's page stands before the frame after it"
    (!sds.any (fun d => d.code == "W0301") &&
      so.pages.size == 2 && (lw so 0 "Spouts").isSome && (lw so 1 "Tea").isSome)
  let (_, shds) := elabStr (edgeDeck "\\AtBeginSection{\\begin{frame}{Outline}\\sectionpage\\end{frame}}\n"
    "\\section{Kettles}\n\\begin{frame}{Boiling}Water boils.\\end{frame}\n")
  t "a section page sharing its frame with a title is named"
    (shds.any fun d => d.code == "W0307" && d.subject == some "sectionpage:shared")
  -- A flow: the folio travels with the words, the dots stand clear of the title, numbers bold.
  let longSrc := "\\documentclass{article}\n\\begin{document}\n\\tableofcontents\n" ++
    "\\section{Kettles}\nWater boils.\n\\subsection{Urn}\nTea pours.\n\\subsection{Ewer}\nTea pours.\n" ++
    "\\section{Teapots and a very long title that runs on past the measure of one line onto " ++
    "another line}\nLeaves steep.\n\\section{}\nCups rest.\n\\end{document}\n"
  let (long, _) := elabStr longSrc
  let lout := (fittedOf fonts long).out
  let lines := contentsLines lout "Water boils"
  t "no folio stands alone on a line, as article's unbreakable fill keeps the last words with it"
    (lines.all fun l => let s := (lineText l).trimAscii.toString
      s.isEmpty || !(s.all Char.isDigit))
  let riders := (lout.pages[0]?.map (·.lines)).getD #[]
  t "every leader dot's box opens past the title's end"
    (lines.all fun l => match leaderGapAt l with
      | some gx => riders.all fun r => r.y != l.y || r.x != l.x || (dotStarts r).all (· ≥ gx)
      | none => true)
  t "a section's number is set in its title's bold face"
    (match lw lout 0 "Kettles" with
      | some l => runFont l "1" == runFont l "Kettles" && (runFont l "1").isSome
      | none => false)
  let (_, lbody, _) := HtmlDoc.emitTree {} long
  t "a blank-titled entry links nothing, so no link reads empty"
    ((HtmlDoc.a11yFacts true false lbody).linksUnnamed == 0 && (Ir.linksSansText long).isEmpty)
  -- Short titles: article's contents, nameref and bookmarks read them; beamer's contents the long.
  let (short, _) := elabStr ("\\documentclass{article}\n\\begin{document}\n\\tableofcontents\n" ++
    "\\section[Short kettles]{Long kettles}\\label{k}\nAs \\nameref{k} says.\n\\end{document}\n")
  let shtml := (HtmlDoc.emit {} short).1
  t "article's contents list a short title"
    ((navEntries (HtmlDoc.emitTree {} short).2.1)[0]?.map (·.map (·.2.1)) == some #["1 Short kettles"])
  t "nameref sets the short title" (hasStr (Ir.blocksText short.body) "As Short kettles says" &&
    hasStr shtml "Short kettles</a> says")
  t "a flow's bookmark names the short title"
    ((Ir.outlineHeadings short).map (·.title) == #["Short kettles"])
  let (sdeck, _) := elabStr (edgeDeck ""
    ("\\begin{frame}{Overview}\\tableofcontents\\end{frame}\n\\section[Short]{Long}\n" ++
     "\\begin{frame}{\\insertsectionhead}x\\end{frame}\n"))
  let sdo := (fittedOf fonts sdeck).out
  t "beamer's contents list the long title, its section head the short"
    ((lw sdo 0 "Long").isSome && (lw sdo 0 "Short").isNone && (lw sdo 1 "Short").isSome)
  -- A deeper heading's anchor stays apart from a label's.
  let (ids, _) := elabStr ("\\documentclass{article}\n\\begin{document}\n\\tableofcontents\n" ++
    "\\section{Kettles}\n\\subsection{Overview}\\label{overview}\nWords.\n\\end{document}\n")
  let (_, ibody, _) := HtmlDoc.emitTree {} ids
  let allIds := (elemNodesList (fun _ => true) #[] ibody.toList).filterMap fun k => match k with
    | .elem _ attrs _ => HtmlDoc.attrOf? attrs "id"
    | _ => none
  t s!"no two elements share an id ({allIds})"
    (allIds.all fun i => (allIds.filter (· == i)).size == 1)

open ContentsChecks in
/-- A table of contents' edges a second reading found: same-titled unnumbered headings keep their
own short titles, a tie-only title links nothing, a frame command's text is all body, and a section
page names its own level. -/
def contentsEdgeChecks2 (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := fun claim => check ref ("contents edges / " ++ claim)
  let (dup, _) := elabStr ("\\documentclass{article}\n\\setcounter{secnumdepth}{0}\n" ++
    "\\begin{document}\n\\tableofcontents\n\\section[Tiny]{Intro}\\label{a}\nWords.\n" ++
    "\\section{Intro}\\label{b}\nSee \\nameref{b}.\n\\end{document}\n")
  t "same-titled unnumbered headings keep their own short titles"
    ((navEntries (HtmlDoc.emitTree {} dup).2.1)[0]?.map (·.map (·.2.1)) == some #["Tiny", "Intro"] &&
      (Ir.outlineHeadings dup).map (·.title) == #["Tiny", "Intro"] &&
      hasStr (Ir.blocksText dup.body) "See Intro.")
  let (tie, _) := elabStr ("\\documentclass{article}\n\\begin{document}\n\\tableofcontents\n" ++
    "\\section{~}\nWords.\n\\end{document}\n")
  t "a tie-only title links nothing"
    ((HtmlDoc.a11yFacts true false (HtmlDoc.emitTree {} tie).2.1).linksUnnamed == 0 &&
      (Ir.linksSansText tie).isEmpty)
  for (src, said) in [("\\frame{{Teapots} are there.}", "Teapots are there."),
      ("\\frame{[Bracket] words.}", "[Bracket] words."), ("\\frame{<2> words.}", "words.")] do
    let (fd, fds) := elabStr (edgeDeck "" (src ++ "\n"))
    let fo := (fittedOf fonts fd).out
    let text := String.intercalate " " (((fo.pages[0]?.map (·.lines)).getD #[]).toList.map lineText)
    t s!"beamer's frame command keeps '{said}' as body, no title taken from it ({text})"
      (hasStr text said && !fds.any (fun d => d.code == "W0110") &&
        (src != "\\frame{<2> words.}" || hasStr text "2"))
  let (_, sds) := elabStr (edgeDeck "\\AtBeginSubsection{\\frame{\\sectionpage}}\n"
    "\\section{Kettles}\n\\subsection{Spouts}\n\\begin{frame}{Pouring}Tea pours.\\end{frame}\n")
  t "a section page after a subsection is named, not set as the subsection's"
    (sds.any fun d => d.code == "W0307" && d.subject == some "sectionpage:sectionpage")

open ContentsChecks in
/-- A flow's contents read its declared names, added lines, TeX strings, macro headings and wrapped
unnumbered entries, page references and names of unnumbered labels, as article's under lualatex. -/
def contentsGapChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := fun claim => check ref ("contents gaps / " ++ claim)
  let src := "\\documentclass{article}\n\\renewcommand{\\contentsname}{Overview}\n" ++
    "\\newcommand{\\mysec}[1]{\\section{#1}\\label{sec:#1}}\n\\begin{document}\n\\tableofcontents\n" ++
    "\\section{Kettles}\nWater boils.\n\\section*{Preface}\n\\addcontentsline{toc}{section}{Preface}\n" ++
    "Words.\n\\section*{Long unnumbered}\n\\addcontentsline{toc}{section}{Short form}\nWords.\n" ++
    "\\mysec{Macro}\nWords.\n\\section{\\texorpdfstring{Tex form}{Plain form}}\n" ++
    "\\renewcommand{\\refname}{Sources}\n\\clearpage\n\\phantomsection\n" ++
    "\\addcontentsline{toc}{section}{\\refname}\n" ++
    "\\begin{thebibliography}{9}\\bibitem{a} A. Author, Title.\\end{thebibliography}\n" ++
    "\\end{document}\n"
  let (doc, ds) := elabStr src
  let (_, body, _) := HtmlDoc.emitTree {} doc
  let words := ((navEntries body)[0]?.map (·.map (·.2.1))).getD #[]
  t s!"the contents list a starred heading beside its entry, by the entry's words, a macro's heading, \
the TeX string and the reference list's renamed heading ({words})"
    (words == #["1 Kettles", "Preface", "Short form", "2 Macro", "3 Tex form", "Sources"])
  let out := (fittedOf fonts doc).out
  t "the contents and the reference list stand under their declared names"
    ((lineWith out 0 "Overview").isSome && (lineWith out 0 "Contents").isNone &&
      out.pages.any fun p => p.lines.any fun l => hasStr (lineText l) "Sources")
  t s!"the starred heading keeps its own words, the TeX string sets alone, no unknown command \
({ds.toList.map (·.code)})"
    (hasStr (Ir.blocksText doc.body) "Long unnumbered" && !hasStr (Ir.blocksText doc.body) "Plain" &&
      !ds.any fun d => d.code == "W0301")
  t "the contents print the reference list's folio"
    (((lineWith out 0 "Sources").map lineText).any (·.trimAscii.toString.endsWith "2"))
  let (lone, lds) := elabStr ("\\documentclass{article}\n\\begin{document}\n\\tableofcontents\n" ++
    "\\section{Kettles}\nWords.\n\n\\addtocontents{toc}{\\protect\\vspace{1em}}\n" ++
    "\\addcontentsline{toc}{section}{Stray}\nMore words.\n\\end{document}\n")
  t "material for the contents and an entry beside no starred heading are named, neither inked"
    (lds.any (fun d => d.code == "W0104" && d.subject == some "contents:addtocontents") &&
      lds.any (fun d => d.code == "W0104" && d.subject == some "contents:addcontentsline") &&
      !hasStr (Ir.blocksText lone.body) "toc" && !hasStr (Ir.blocksText lone.body) "Stray")
  -- A page reference prints the page of a label nothing numbers, as LaTeX's `\pageref` does.
  let (paged, pds) := elabStr ("\\documentclass{article}\n\\begin{document}\n\\label{start}" ++
    "Words.\n\\section{Kettles}\\label{kettles}\nSee page~\\pageref{start}, \\nameref{par} " ++
    "and \\nameref{fig:l}.\n\\paragraph{Spouts}\\label{par} Tea pours.\n" ++
    "\\begin{figure}\\begin{subfigure}{0.4\\textwidth}A\\caption{Left kettle}\\label{fig:l}" ++
    "\\end{subfigure}\\caption{Two kettles}\\end{figure}\n\\end{document}\n")
  let pout := (fittedOf fonts paged).out
  t s!"a page reference to a label nothing numbers prints its page, unnamed as a loss \
({pds.toList.map (·.code)})"
    ((((lineWith pout 0 "See page").map fun l => letters (lineText l)).getD "").startsWith "Seepage1," &&
      !pds.any fun d => d.code == "W0349")
  t "a label after a run-in heading names it, a subfloat's its own caption"
    (hasStr (Ir.blocksText paged.body) "Spouts and Left kettle.")
  -- A section's anchor yields to a label of the same name, so no two elements share an id.
  let (_, ibody, ids) := HtmlDoc.emitTree {} paged
  let allIds := (elemNodesList (fun _ => true) #[] ibody.toList).filterMap fun k => match k with
    | .elem _ attrs _ => HtmlDoc.attrOf? attrs "id"
    | _ => none
  t s!"a section named as a label takes its own anchor, unnamed as a clash ({allIds})"
    (allIds.contains "kettles" && allIds.all (fun i => (allIds.filter (· == i)).size == 1) &&
      !ids.any fun d => d.code == "W0327")
  -- article.cls's `\leftskip`: an unnumbered entry's lines after the first stand past the number.
  let (wrap, _) := elabStr ("\\documentclass{article}\n\\begin{document}\n\\tableofcontents\n" ++
    "\\section*{Kettles and their long descriptive titles that run past the measure of one line}\n" ++
    "\\addcontentsline{toc}{section}{Kettles and their long descriptive titles that run past the " ++
    "measure of one line}\nWater boils.\n\\end{document}\n")
  let wout := (fittedOf fonts wrap).out
  let lines := contentsLines wout "Water boils"
  let first := lines.find? fun l => hasStr (lineText l) "Kettles"
  let next := lines.find? fun l => hasStr (lineText l) "line"
  t "an unnumbered entry's wrapped line stands 1.5em in from its first"
    (match first, next with
      | some f, some n => f.y < n.y && n.x - f.x == wrap.page.fontSize * 3 / 2
      | _, _ => false)
  -- The web page's contents are a list, each entry an item reading its number apart.
  let items := elemNodesList (· == "li") #[] body.toList |>.filter fun k => match k with
    | .elem _ attrs _ => ((HtmlDoc.attrOf? attrs "class").getD "").startsWith "contents-entry"
    | _ => false
  let uls := elemNodesList (· == "ul") #[] body.toList |>.filter fun k => match k with
    | .elem _ attrs _ => HtmlDoc.attrOf? attrs "class" == some "contents-list"
    | _ => false
  t s!"the web page's contents are one list of an item per entry ({items.size})"
    (uls.size == 1 && items.size == 6)
  -- An entry before its starred heading, one past a label, one inside a paragraph, and a unit apart.
  let (more, mds) := elabStr ("\\documentclass{article}\n\\begin{document}\n\\tableofcontents\n" ++
    "\\addcontentsline{toc}{section}{Ahead}\n\\section*{Ahead long}\nWords.\n" ++
    "\\section*{Past}\n\\label{past}\n\\addcontentsline{toc}{section}{Past}\nSee [\\nameref{past}] " ++
    "and [\\nameref{other}].\n\\paragraph{Spouts} Tea pours.\n\\section*{Other}\\label{other}\n" ++
    "Words \\addcontentsline{toc}{section}{Inside} more words.\n\\section*{Unit}\n" ++
    "\\addcontentsline{toc}{subsection}{\\protect\\numberline{}Unit}\nText.\n\\end{document}\n")
  let (_, mbody, _) := HtmlDoc.emitTree {} more
  let mwords := ((navEntries mbody)[0]?.map (·.map (·.2.1))).getD #[]
  t s!"an entry lists the starred heading after it and the one before it past a label, not one \
inside a paragraph ({mwords})" (mwords == #["Ahead", "Past", "Unit"])
  t "a listed heading's label names its own title, and a run-in heading's name ends at the next heading"
    (hasStr (Ir.blocksText more.body) "See [Past] and [Other].")
  t "an entry inside a paragraph and one of another unit are named, nothing inked"
    (mds.any (fun d => d.code == "W0104" && d.subject == some "contents:addcontentsline") &&
      mds.any (fun d => d.code == "W0104" && d.subject == some "contents:addcontentsline:unit") &&
      !hasStr (Ir.blocksText more.body) "Inside" && hasStr (letters (Ir.blocksText more.body)) "Wordsmorewords" &&
      !mds.any fun d => d.code == "W0301")
  -- A frame a macro with a parameter sets takes its own number.
  let (deck, _) := elabStr ("\\documentclass{beamer}\n" ++
    "\\newcommand{\\myframe}[1]{\\begin{frame}{#1}Body of #1.\\end{frame}}\n\\begin{document}\n" ++
    "\\begin{frame}{One}Body.\\end{frame}\n\\myframe{Two}\n\\myframe{Three}\n" ++
    "\\begin{frame}{Four}Body.\\end{frame}\n\\end{document}\n")
  t s!"each frame a macro sets is numbered after the one before ({deck.frameNumbers})"
    (deck.frameNumbers.filterMap id == #[1, 2, 3, 4])

open ContentsChecks in
/-- A deck's contents and frames as beamer's options set them: pausesections stepping the entries,
sections= choosing them, firstsection reading to the same page, a mode specification keeping a frame
to its modes, and noframenumbering leaving a frame out of the count. -/
def contentsDeckChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := fun claim => check ref ("contents deck / " ++ claim)
  let body := "\\section{Kettles}\n\\begin{frame}{Boiling}Water boils.\\end{frame}\n" ++
    "\\section{Teapots}\n\\begin{frame}{Steeping}Leaves steep.\\end{frame}\n" ++
    "\\section{Trays}\n\\begin{frame}{Carrying}Trays carry.\\end{frame}\n"
  let deck (toc : String) : String :=
    "\\documentclass{beamer}\n\\usetheme{default}\n\\begin{document}\n" ++
      s!"\\begin\{frame}\{Overview}{toc}\\end\{frame}\n" ++ body ++ "\\end{document}\n"
  let (paused, pds) := elabStr (deck "\\tableofcontents[pausesections,firstsection=2]")
  let pout := (fittedOf fonts paused).out
  let design := Ir.Design.ofPalette paused.palette
  let shown (i : Nat) (w : String) : Bool :=
    ((lineWith pout i w).bind firstRun).map (·.1) == some design.fg
  t s!"pausesections sets an overview page per section, each showing one more entry \
({pout.pages.size} pages)"
    (pout.pages.size == 6 && shown 0 "Kettles" && !shown 0 "Teapots" && shown 1 "Teapots" &&
      !shown 1 "Trays" && shown 2 "Trays")
  t s!"firstsection reads to nothing it would name ({pds.toList.map (·.code)})"
    (!pds.any fun d => d.code == "W0104")
  let subBody := "\\section{Kettles}\n\\subsection{Copper}\n\\subsection{Steel}\n" ++
    "\\begin{frame}{Boiling}Water boils.\\end{frame}\n\\section{Teapots}\n\\subsection{Clay}\n" ++
    "\\begin{frame}{Steeping}Leaves steep.\\end{frame}\n"
  let (subs, _) := elabStr ("\\documentclass{beamer}\n\\usetheme{default}\n\\begin{document}\n" ++
    "\\begin{frame}{Overview}\\tableofcontents[pausesubsections]\\end{frame}\n" ++ subBody ++
    "\\end{document}\n")
  let sbout := (fittedOf fonts subs).out
  let sdesign := Ir.Design.ofPalette subs.palette
  let subShown (i : Nat) (w : String) : Bool :=
    ((lineWith sbout i w).bind firstRun).map (·.1) == some sdesign.fg
  t s!"pausesubsections steps each subsection alone, a section showing with the one before it \
({sbout.pages.size} pages)"
    (sbout.pages.size == 5 && subShown 0 "Kettles" && subShown 0 "Copper" && !subShown 0 "Steel" &&
      subShown 1 "Steel" && subShown 1 "Teapots" && !subShown 1 "Clay" && subShown 2 "Clay")
  let (chosen, _) := elabStr (deck "\\tableofcontents[sections={2-3}]")
  let cout := (fittedOf fonts chosen).out
  t "sections= lists the sections it names alone"
    ((lineWith cout 0 "Kettles").isNone && (lineWith cout 0 "Teapots").isSome &&
      (lineWith cout 0 "Trays").isSome)
  let (moded, mds) := elabStr ("\\documentclass{beamer}\n\\begin{document}\n" ++
    "\\begin{frame}{One}Body.\\end{frame}\n\\begin{frame}<article>{Article}Gone.\\end{frame}\n" ++
    "\\begin{frame}<handout:0>{Kept}Body.\\end{frame}\n" ++
    "\\begin{frame}[noframenumbering]{Backup}Body.\\end{frame}\n" ++
    "\\begin{frame}{Last}Body.\\end{frame}\n\\end{document}\n")
  t s!"an article frame ships no page, a handout-only spec leaves the frame as it is \
({mds.toList.map (·.code)})"
    (!hasStr (Ir.blocksText moded.body) "Gone" && hasStr (Ir.blocksText moded.body) "Kept" &&
      !mds.any fun d => d.code == "W0110")
  t s!"noframenumbering leaves its frame out of the count ({moded.frameNumbers})"
    (moded.frameNumbers.filterMap id == #[1, 2, 3] && moded.frameCount == 3)
  -- beamer's default section page names the section's number over its title, both centred.
  let paged := "\\documentclass{beamer}\n\\usetheme{default}\n" ++
    "\\AtBeginSection[]{\\begin{frame}\\sectionpage\\end{frame}}\n\\begin{document}\n" ++ body ++
    "\\end{document}\n"
  let (sp, _) := elabStr (paged.replace "\\begin{document}\n"
    "\\AtBeginSubsection[]{\\begin{frame}\\subsectionpage\\end{frame}}\n\\begin{document}\n\\section*{Lead}\n")
  let sout := (fittedOf fonts sp).out
  let mid (l : Layout.LineOut) : Dim.Length := l.x + (l.segs.foldl (fun w s => w + s.advance) 0) / 2
  t "the default section page sets 'Section 3' over the third section's title, both centred"
    (match lineWith sout 2 "Section", lineWith sout 2 "Teapots" with
      | some n, some ti => n.y < ti.y && (hasStr (lineText n) "3") &&
        (mid n - mid ti).abs * 50 < (Layout.Geom.ofPage sp.page).textWidth.abs
      | _, _ => false)
  -- beamer's `[c]` sets 1fill above the page's content against 1.5fill below.
  let pageH := (Layout.Geom.ofPage sp.page).pageH
  t s!"the document's section page frame stands above the page's middle, as beamer's [c] sets it \
({(lineWith sout 2 "Section").map (·.y.toBpString)}, \
{(lineWith sout 2 "Teapots").map (·.y.toBpString)} of {pageH.toBpString})"
    (match lineWith sout 2 "Section", lineWith sout 2 "Teapots" with
      | some n, some ti =>
        (n.y + ti.y) / 2 < pageH / 2 - pageH / 16 && (n.y + ti.y) / 2 > pageH / 2 - pageH / 8
      | _, _ => false)
  let sweb := (HtmlDoc.emit {} sp).1
  t "the web section page spends the same shares, the smaller above"
    (((sweb.splitOn "<section class=\"section-page")[1]?.map fun sec =>
      let sec := (sec.splitOn "</section>").headD ""
      match (sec.splitOn "flex-grow: 1000"), (sec.splitOn "flex-grow: 1500") with
      | [before, _], [_, after] => !hasStr before "Section" && !hasStr after "Section"
      | _, _ => false) == some true)
  let (top, _) := elabStr (paged.replace "\\begin{frame}\\sectionpage" "\\begin{frame}[t]\\sectionpage")
  let tout := (fittedOf fonts top).out
  t "a top-aligned section page frame sets its page at the top"
    ((lineWith tout 2 "Section").any fun n => n.y < pageH / 4)
  -- A hook calls a command the preamble defines after it, a shaded entry mixes its declared colour,
  -- and beamer's hyperref option is hypersetup's keys.
  let (hooked, hds) := elabStr ("\\documentclass[hyperref={colorlinks}]{beamer}\n\\usetheme{default}\n" ++
    "\\AtBeginSection[]{\\begin{frame}{Outline}\\mynote\\tableofcontents[currentsection]\\end{frame}}\n" ++
    "\\newcommand{\\mynote}{Defined later.}\n\\begin{document}\n" ++
    "\\section{Kettles \\textcolor{red}{hot}}\n\\begin{frame}{One}Body.\\end{frame}\n" ++
    "\\section{Teapots}\n\\begin{frame}{Two}Body.\\end{frame}\n\\end{document}\n")
  t s!"a section hook calls a command defined after it, and the hyperref option is read \
({hds.toList.map (·.code)})"
    (hasStr (Ir.blocksText hooked.body) "Defined later." &&
      !hds.any fun d => d.code == "W0301" || d.code == "W0104")
  let hout := (fittedOf fonts hooked).out
  let hdesign := Ir.Design.ofPalette hooked.palette
  let colorsOf (l : Layout.LineOut) : List Ir.Color := l.segs.toList.filterMap fun s => match s with
    | .run _ color .. => some color
    | _ => none
  let red := ((lineWith hout 0 "Kettles").map colorsOf).bind fun cs => cs.find? (· != hdesign.fg)
  t "a shaded entry's declared colour is mixed over the page as its other words are"
    (match lineWith hout 2 "Kettles", red with
      | some l, some red => (colorsOf l).contains (red.mix Ir.contentsShadeShare hdesign.bg) &&
          !(colorsOf l).contains red
      | _, _ => false)
  let (_, sbody, _) := HtmlDoc.emitTree {} sp
  t "the web deck's section page carries the same name line, counting the starred section"
    ((elemNodesList (· == "p") #[] sbody.toList).any fun k => match k with
      | .elem _ attrs _ => HtmlDoc.attrOf? attrs "class" == some "section-name" &&
          hasStr (nodeTextOne "" k) "Section\u00A03"
      | _ => false)
  let (hyp, _) := elabStr ("\\documentclass[hyperref={pdftitle={Kettles, Teapots}}]{beamer}\n" ++
    "\\begin{document}\n\\begin{frame}{One}Body.\\end{frame}\n\\end{document}\n")
  t s!"beamer's hyperref option keeps a braced value whole ({hyp.info.title})"
    (hyp.info.title == some "Kettles, Teapots")

/-- Each web slide's footline text, in order: its right band's words, empty where it sets none. -/
private def slideFeet (html : String) : Array String :=
  ((html.splitOn "<section ").drop 1).toArray.map fun sec =>
    let sec := (sec.splitOn "</section>").headD ""
    match (sec.splitOn "class=\"band-right\"")[1]? with
    | some rest => (((rest.splitOn ">")[1]?.getD "").splitOn "<").headD ""
    | none => ""

open ContentsChecks in
/-- Frames count as the theme in force numbers them: beamer's `\maketitle` frame counted, moloch's
plain and uncounted, a title page showing no number; a noframenumbering frame shows the number before
it, a plain frame no footline and no logo, in both backends. -/
def frameCountChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := fun claim => check ref ("frame count / " ++ claim)
  let deck (theme : String) : String :=
    "\\documentclass{beamer}\n" ++ theme ++ "\\title{Kettle Notes}\n\\logo{Logomark}\n" ++
    "\\begin{document}\n\\maketitle\n\\begin{frame}{First}Alpha.\\end{frame}\n" ++
    "\\begin{frame}[noframenumbering]{Second}Beta.\\end{frame}\n" ++
    "\\begin{frame}[plain]{Third}Gamma.\\end{frame}\n" ++
    "\\begin{frame}{Fourth}Delta.\\end{frame}\n\\end{document}\n"
  let footText (p : Layout.PageOut) : String :=
    (p.foot.map fun b => Ir.plainText (Ir.bandInlines b)).getD ""
  let (beamer, _) := elabStr (deck "")
  let bout := (fittedOf fonts beamer).out
  t s!"beamer counts its title frame, a noframenumbering frame shows the number before it and a \
plain frame none ({bout.pages.map footText})"
    (bout.pages.map footText == #["", "2", "2", "", "4"])
  let (moloch, _) := elabStr (deck "\\usetheme{moloch}\n")
  let mout := (fittedOf fonts moloch).out
  t s!"moloch's title frame is plain and uncounted ({mout.pages.map footText})"
    (mout.pages.map footText == #["", "1", "1", "", "3"])
  let (framed, _) := elabStr ((deck "\\usetheme{moloch}\n").replace "\\maketitle"
    "\\begin{frame}\\titlepage\\end{frame}")
  t s!"moloch's own footline numbers a title page its frame counts \
({(fittedOf fonts framed).out.pages.map footText})"
    ((fittedOf fonts framed).out.pages.map footText == #["1", "2", "2", "", "4"])
  t "a plain frame sets no logo, the frames beside it theirs"
    ((lineWith bout 3 "Logomark").isNone && (lineWith bout 2 "Logomark").isSome &&
      (lineWith mout 3 "Logomark").isNone && (lineWith mout 4 "Logomark").isSome)
  let bweb := (HtmlDoc.emit {} beamer).1
  let mweb := (HtmlDoc.emit {} moloch).1
  t s!"the web decks' footlines show the same numbers ({slideFeet bweb}, {slideFeet mweb})"
    (slideFeet bweb == #["", "2", "2", "", "4"] && slideFeet mweb == #["", "1", "1", "", "3"])
  t "a plain web slide carries no logo"
    (((bweb.splitOn "<section ")[4]?.map fun s => hasStr s "Logomark") == some false &&
      ((bweb.splitOn "<section ")[3]?.map fun s => hasStr s "Logomark") == some true)
