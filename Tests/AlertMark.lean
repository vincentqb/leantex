module

public import Tests.Support
public import LeanTex.Core.SeedPalette

public section

open LeanTex.Core

/-! A container accent (`SeedPalette.Seeds.container`) never sets as text on a light page, and an
alert sets in the ink on a mark of the accent in both artifacts. -/

namespace Tests.AlertMark

def yellow : Ir.Color := Ir.Color.ofHtml 0xFA 0xCC 0x15

/-- Invented seeds, each with whether its accent serves as a container: yellows that do, one with an
example of its hue, accents that keep their colour as text, and yellows an alert or ink rules out. -/
def seeds : List (String × SeedPalette.Seeds × Bool) := [
  ("a yellow accent on white",
    { ink := Ir.Color.black, paper := Ir.Color.white, accent := yellow }, true),
  ("a pure yellow with a yellow example",
    { ink := Ir.Color.black, paper := Ir.Color.white, accent := Ir.Color.ofHtml 0xFF 0xFF 0x00,
      exampleColor := some (Ir.Color.ofHtml 0xE5 0xE5 0x00) }, true),
  ("an orange accent",
    { ink := Ir.Color.ofHtml 0x2B 0x24 0x40, paper := Ir.Color.white,
      accent := Ir.Color.ofHtml 0xE8 0x5D 0x2A }, false),
  ("a teal accent on cream",
    { ink := Ir.Color.ofHtml 0x3B 0x2F 0x2A, paper := Ir.Color.ofHtml 0xFB 0xF6 0xEC,
      accent := Ir.Color.ofHtml 0x0D 0x94 0x88 }, false),
  ("an amber accent on a dark paper",
    { ink := Ir.Color.ofHtml 0xF4 0xF1 0xEA, paper := Ir.Color.ofHtml 0x1B 0x24 0x30,
      accent := Ir.Color.ofHtml 0xF2 0xA5 0x41 }, false),
  ("a mustard meeting a deck's floor as given",
    { ink := Ir.Color.ofHtml 0x1C 0x19 0x17, paper := Ir.Color.white,
      accent := Ir.Color.ofHtml 0xA6 0x8A 0x00 }, false),
  ("a yellow under a grey ink too faint on it to mark",
    { ink := Ir.Color.ofHtml 0x44 0x44 0x44, paper := Ir.Color.white, accent := yellow }, false),
  ("a lemon beside a declared alert of its hue",
    { ink := Ir.Color.black, paper := Ir.Color.white, accent := Ir.Color.ofHtml 0xF0 0xE4 0x42,
      alert := some (Ir.Color.ofHtml 0xCC 0xCC 0x00) }, false)]

/-- A container accent marks text and never sets as text, at either depth and in each light scheme
alike: the alert is the ink on the accent's mark at `markInk`, any other accent ships no mark, and
no tone the generator derives is disliked. -/
def containerChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (label, s, want) in seeds do
    for (depth, d) in [("a deck", Ir.GroundDepth.decks), ("a document", Ir.GroundDepth.documents)] do
      for (scheme, tg) in [("", s.targets d), (" asking more", (s.targets d).more)] do
        let at_ := s!"container, {label}, {depth}{scheme}"
        t s!"{at_}: the accent serves as a container exactly where owed" (s.container tg == want)
        match SeedPalette.generate s tg with
        | .error f => t s!"{at_}: generates, not fail at {reprStr f.role}" false
        | .ok g =>
          let c := g.colors
          if want then
            t s!"{at_}: the alert sets in the ink on a mark of the accent"
              (c.alert == s.ink && c.alertMark == some s.accent)
            t s!"{at_}: the accent never sets as text or an edge on the page"
              (c.accentText == s.ink && c.accentEdge == s.ink && c.alertBand == s.ink)
            t s!"{at_}: the ink reads on the mark in every light scheme"
              (SeedPalette.markInk ≤ Contrast.contrastMilli s.ink s.accent &&
                tg.text ≤ SeedPalette.markInk)
          else
            t s!"{at_}: no mark" c.alertMark.isNone
          let declared := [s.ink, s.accent] ++ s.alert.toList ++ s.exampleColor.toList
          let derived := [c.surface, c.surfaceStrong, c.rule, c.accentWash, c.accentSoft, c.muted,
            c.diagramMuted, c.mutedOnInverse, c.accentText, c.accentEdge, c.accentOnInverse, c.alert,
            c.alertBand, c.exampleBand] ++ c.exampleText.toList
          t s!"{at_}: no derived tone stands in the disliked region"
            (derived.all fun x => declared.contains x || !dislikedBox x)

/-- The mark's ink on a line: every `.decoration .highlight` seg of the
riders painted before the line, with its left edge and width. -/
private def marksBefore (lines : Array Layout.LineOut) (i : Nat) :
    Array (Ir.Color × Dim.Sp × Dim.Sp) := Id.run do
  let mut out := #[]
  let mut j := i
  while j > 0 do
    j := j - 1
    let some l := lines[j]? | break
    if l.segs.any (fun s => match s with | .run .. => true | _ => false) then break
    let mut x := l.x
    for seg in l.segs do
      match seg with
      | .decoration (.highlight _ _) w _ _ c => out := out.push (c, x, w); x := x + w
      | .decoration _ w _ _ _ | .gap w _ | .decoratedGap w _ _ | .rule w _ _ _ | .image _ w _ =>
        x := x + w
      | .run _ _ _ w _ _ _ _ _ _ _ => x := x + w
      | .poly _ _ => pure ()
  return out

/-- The marks under the line setting `word`, or none where no line sets it. -/
private def marksUnder (lines : Array Layout.LineOut) (word : String) :
    Option (Array (Ir.Color × Dim.Sp × Dim.Sp)) :=
  (lines.findIdx? fun l => hasStr (lineText l) word).map (marksBefore lines)

/-- Every highlight seg a laid-out document ships. -/
private def highlightSegs (out : Layout.Out) : Array Ir.Color :=
  (allLines out).flatMap fun l => l.segs.filterMap fun s => match s with
    | .decoration (.highlight _ _) _ _ _ c => some c
    | _ => none

def seedsLine : String := "\\palette[seeds]{ ink = #000000, paper = #FFFFFF, accent = #FACC15 }\n"

/-- An alert on a container accent ships on its mark in both artifacts: one mark under each line's
stretch of it, painted before the page's text object in the PDF, and a styled span in the HTML. -/
def markChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← serifFacesSet | failures ref "mark: the serif faces load"
  let (doc, ds) := elabStr (dvDeck seedsLine
    "\\begin{frame}\nPlain words and \\alert{marked words} close.\n\\end{frame}")
  t s!"mark: the deck elaborates clean ({(ds.filter (·.severity != .note)).map (·.code)})"
    (ds.all (·.severity == .note))
  t "mark: the report finds no pairing short" (ds.all (·.code != "W0315"))
  let out := layoutOf fonts doc
  let lines := allLines out
  match lines.findIdx? (fun l => hasStr (lineText l) "marked") with
  | none => t "mark: the alerted line ships" false
  | some i =>
    let marks := marksBefore lines i
    -- The line's runs, each with whether it stands on the mark.
    let grounded := Id.run do
      let mut out : Array (Dim.Sp × Dim.Sp × Bool) := #[]
      let mut x := lines[i]!.x
      for seg in lines[i]!.segs do
        match seg with
        | .run _ _ _ w _ _ _ _ _ ground _ => out := out.push (x, w, ground == some yellow); x := x + w
        | .gap w _ | .decoratedGap w _ _ | .rule w _ _ _ | .decoration _ w _ _ _ | .image _ w _ =>
          x := x + w
        | .poly _ _ => pure ()
      return out
    let covered (x w : Dim.Sp) : Bool := marks.any fun (_, mx, mw) => mx ≤ x && x + w ≤ mx + mw
    t s!"mark: one mark in the accent, the alert's whole stretch, is painted before its line ({marks.size})"
      (marks.size == 1 && marks.all (·.1 == yellow))
    t "mark: the mark spans the alerted runs and no other"
      ((grounded.filter (·.2.2)).size == 2 && grounded.all fun (x, w, onMark) => covered x w == onMark)
    t "mark: the alerted runs set in the ink on the mark"
      (wordRun lines "marked" == some (Ir.Color.black, some yellow))
  let geom := Layout.Geom.ofPage doc.page
  let stream := match (Pdf.pageStreams geom fonts out.pages)[0]? with
    | some b => String.fromUTF8! b
    | none => ""
  -- The same deck without the alert paints the accent's other fills, the progress bar among them.
  let (pdoc, _) := elabStr (dvDeck seedsLine
    "\\begin{frame}\nPlain words and marked words close.\n\\end{frame}")
  let plainStream := match (Pdf.pageStreams geom fonts (layoutOf fonts pdoc).pages)[0]? with
    | some b => String.fromUTF8! b
    | none => ""
  let fillsBeforeText (s : String) : Nat := (((s.splitOn "BT\n").headD "").splitOn yellow.pdfFill).length - 1
  t s!"mark: the PDF paints the alert's one mark before its page's text object ({fillsBeforeText stream}, {fillsBeforeText plainStream})"
    (hasStr stream "BT\n" && fillsBeforeText stream == fillsBeforeText plainStream + 1)
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  let spans := (elemNodesList (· == "span") #[] body.toList).filter fun n => match n with
    | .elem _ attrs _ => attrs.any fun (k, v) => k == "style" && hasStr v "background-color" &&
        hasStr v (Ir.ColorRef.role .alertMark).property
    | _ => false
  t "mark: the web page sets the alert on a span whose background is the alert's mark"
    (spans.size == 1 && spans.all fun n => nodeTextOne "" n == "marked words")
  t "mark: the web page ships no mark element, whose highlight role an alert does not have"
    (elemNodesList (· == "mark") #[] body.toList).isEmpty
  t "mark: the stylesheet declares the alert's mark" (hasStr css ((Ir.ColorRef.role .alertMark).property ++ ":"))
  -- A long alert in a narrow box breaks with its mark.
  let long := "\\begin{frame}\n\\begin{minipage}{3cm}\n\\alert{a long alerted sentence that " ++
    "must break across lines}\n\\end{minipage}\n\\end{frame}"
  let (ldoc, _) := elabStr (dvDeck seedsLine long)
  let llines := allLines (layoutOf fonts ldoc)
  let set := (List.range llines.size).filter fun i =>
    let tx := lineText llines[i]!
    hasStr tx "alerted" || hasStr tx "break" || hasStr tx "lines"
  t s!"mark: a long alert sets on more than one line ({set.length})" (set.length ≥ 2)
  t "mark: each line the alert sets on has one mark of its own"
    (set.all fun i => (marksBefore llines i).size == 1)
  -- A TeX build names the mark as an xcolor colour of its key, which both
  -- engines read: leantex as the role.
  let (xdoc, _) := elabStr (dvDeck ("\\usepackage{xcolor}\n\\palette{ alert = #1C1917 }\n" ++
      "\\definecolor{alertmark}{HTML}{FFEE00}\n")
    "\\begin{frame}\nWords and \\alert{marked words}.\n\\end{frame}")
  t "mark: an xcolor alertmark declares the alert's mark"
    (Ir.Design.declared? xdoc.palette .alertMark == some (Ir.Color.ofHtml 0xFF 0xEE 0x00))
  let xlines := allLines (layoutOf fonts xdoc)
  t "mark: and the alert sets on it"
    ((marksUnder xlines "marked").any fun ms => ms.any (·.1 == Ir.Color.ofHtml 0xFF 0xEE 0x00))

/-- Where an alert's mark stands and where not: not on a ground the accent reads on, nor under an
alert declared after the seeds, nor in a dark scheme; quieted on a covered step, only on the steps an
overlay alerts, never under a picture's label; and an alert short on its mark reported. -/
def placeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← serifFacesSet | failures ref "mark place: the serif faces load"
  let (sdoc, _) := elabStr (dvDeck seedsLine
    "\\begin{frame}[standout]\nA \\alert{standout} word.\n\\end{frame}")
  let sout := layoutOf fonts sdoc
  t "mark place: on the ink, an alert sets with no mark" (highlightSegs sout).isEmpty
  t "mark place: and its run is the accent on the ink"
    ((wordRun (allLines sout) "standout").any fun (c, _) => c == yellow)
  let red := Ir.Color.ofHtml 0xDC 0x26 0x26
  let (rdoc, _) := elabStr (dvDeck (seedsLine ++ "\\palette{ alert = #DC2626 }\n")
    "\\begin{frame}\nA \\alert{declared} word.\n\\end{frame}")
  let rout := layoutOf fonts rdoc
  t "mark place: an alert the document declares after the seeds sets in its own colour, unmarked"
    ((highlightSegs rout).isEmpty && (wordRun (allLines rout) "declared").any (·.1 == red))
  let pageMarks (out : Layout.Out) (k : Nat) (word : String) : Option (Array Ir.Color) :=
    (out.pages[k]?.bind fun p => marksUnder p.lines word).map (·.map (·.1))
  let (cdoc, _) := elabStr (dvDeck seedsLine
    "\\begin{frame}\nFirst.\n\n\\uncover<2>{A \\alert{covered} word.}\n\\end{frame}")
  let cout := layoutOf fonts cdoc
  t "mark place: a covered step's mark is quieted with the text it stands behind"
    ((pageMarks cout 0 "covered").any fun ms => !ms.isEmpty && ms.all (· != yellow))
  t "mark place: and the step that reveals it shows the accent"
    ((pageMarks cout 1 "covered").any fun ms => !ms.isEmpty && ms.all (· == yellow))
  let (odoc, _) := elabStr (dvDeck seedsLine
    "\\begin{frame}\nAn \\alert<2>{overlaid} word.\n\n\\uncover<2>{Then.}\n\\end{frame}")
  let oout := layoutOf fonts odoc
  t "mark place: an alert an overlay selects is marked on its step only"
    ((pageMarks oout 0 "overlaid").any (·.isEmpty) &&
      (pageMarks oout 1 "overlaid").any fun ms => !ms.isEmpty && ms.all (· == yellow))
  let (pdoc, _) := elabStr (dvDeck (seedsLine ++ "\\usepackage{tikz}\n")
    "\\begin{frame}\n\\begin{tikzpicture}\n\\node[fill=black!10] {\\alert{label}};\n\\end{tikzpicture}\n\\end{frame}")
  t "mark place: a picture's label ships no mark, as its web page's SVG label sets none"
    (highlightSegs (layoutOf fonts pdoc)).isEmpty
  let (ddoc, dds) := elabStr (dvDeck (seedsLine ++ "\\output{ schemes = print, light, dark }\n")
    "\\begin{frame}\nPlain words and \\alert{marked words} close.\n\\end{frame}")
  let (dhead, _, hds) := HtmlDoc.emitTree {} ddoc
  let dcss := treeCssList "" dhead.toList
  t s!"mark place: a deck asking a dark scheme ships it, its mark taken out there ({(dds ++ hds).map (·.code)})"
    (hasStr dcss "light-dark(#facc15, transparent)" && (dds ++ hds).all (·.code != "W0308"))
  let judged (mark : String) : Array Diag :=
    (elabStr (dvDeck ("\\usepackage{xcolor}\n\\palette{ alert = #1C1917 }\n" ++ mark)
      "\\begin{frame}\nWords and \\alert{marked words}.\n\\end{frame}")).2
  t "mark place: an alert that does not read on a declared mark is reported"
    ((judged "\\definecolor{alertmark}{HTML}{3A3A3A}\n").any (·.code == "W0315"))
  t "mark place: and one that reads on it is not"
    ((judged "\\definecolor{alertmark}{HTML}{FFEE00}\n").all (·.code != "W0315"))

end Tests.AlertMark
