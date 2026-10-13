module

public import Tests.Support
public import LeanTex.Core.SeedPalette

public section

open LeanTex.Core

/-! A container accent (`SeedPalette.Seeds.container`) never sets as text on a light page, and an
alert sets in the ink on a mark of the accent in both artifacts. -/

namespace Tests.AlertMark

/-- Invented seeds: a yellow accent on white, which serves as a container,
and three that keep their colour as text. -/
def seeds : List (String × SeedPalette.Seeds × Bool) := [
  ("a yellow accent on white",
    { ink := Ir.Color.black, paper := Ir.Color.white, accent := Ir.Color.ofHtml 0xFA 0xCC 0x15 },
    true),
  ("an orange accent",
    { ink := Ir.Color.ofHtml 0x2B 0x24 0x40, paper := Ir.Color.white,
      accent := Ir.Color.ofHtml 0xE8 0x5D 0x2A }, false),
  ("a teal accent on cream",
    { ink := Ir.Color.ofHtml 0x3B 0x2F 0x2A, paper := Ir.Color.ofHtml 0xFB 0xF6 0xEC,
      accent := Ir.Color.ofHtml 0x0D 0x94 0x88 }, false),
  ("an amber accent on a dark paper",
    { ink := Ir.Color.ofHtml 0xF4 0xF1 0xEA, paper := Ir.Color.ofHtml 0x1B 0x24 0x30,
      accent := Ir.Color.ofHtml 0xF2 0xA5 0x41 }, false)]

/-- A container accent marks text and never sets as text, at either depth: the alert is the ink on
the accent's mark at 4.5:1, any other accent ships no mark, and no derived tone is disliked. -/
def containerChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (label, s, want) in seeds do
    for (depth, d) in [("a deck", Ir.GroundDepth.decks), ("a document", Ir.GroundDepth.documents)] do
      let tg := s.targets d
      t s!"container, {label}, {depth}: the accent serves as a container exactly where owed"
        (s.container tg == want)
      match SeedPalette.generate s tg with
      | .error f => t s!"container, {label}, {depth}: generates, not fail at {reprStr f.role}" false
      | .ok g =>
        let c := g.colors
        if want then
          t s!"container, {label}, {depth}: the alert sets in the ink on a mark of the accent"
            (c.alert == s.ink && c.alertMark == some s.accent)
          t s!"container, {label}, {depth}: the accent never sets as text or an edge on the page"
            (c.accentText == s.ink && c.accentEdge == s.ink && c.alertBand == s.ink)
          t s!"container, {label}, {depth}: the ink reads on the mark at 4.5:1"
            (Contrast.aaText ≤ Contrast.contrastMilli s.ink s.accent)
        else
          t s!"container, {label}, {depth}: no mark" c.alertMark.isNone
        let derived := [c.surface, c.surfaceStrong, c.rule, c.accentWash, c.accentSoft, c.muted,
          c.diagramMuted, c.mutedOnInverse, c.accentText, c.accentEdge, c.accentOnInverse, c.alert,
          c.alertBand, c.exampleBand] ++ c.exampleText.toList
        t s!"container, {label}, {depth}: no derived tone stands in the disliked region"
          (derived.all fun x => x == s.accent || x == s.ink || !ContrastSolve.disliked x)

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

/-- An alert on a container accent ships on its mark in both artifacts: under its runs before the
line's text in the PDF, as a `mark` in the HTML, and under each line a long alert breaks onto. -/
def markChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← serifFacesSet | failures ref "mark: the serif faces load"
  let accent := Ir.Color.ofHtml 0xFA 0xCC 0x15
  let pre := "\\palette[seeds]{ ink = #000000, paper = #FFFFFF, accent = #FACC15 }\n"
  let (doc, ds) := elabStr (dvDeck pre
    "\\begin{frame}\nPlain words and \\alert{marked words} close.\n\\end{frame}")
  t s!"mark: the deck elaborates clean ({(ds.filter (·.severity != .note)).map (·.code)})"
    (ds.all (·.severity == .note))
  t "mark: the report finds no pairing short" (ds.all (·.code != "W0315"))
  let lines := allLines (layoutOf fonts doc)
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
        | .run _ _ _ w _ _ _ _ _ ground _ => out := out.push (x, w, ground == some accent); x := x + w
        | .gap w _ | .decoratedGap w _ _ | .rule w _ _ _ | .decoration _ w _ _ _ | .image _ w _ =>
          x := x + w
        | .poly _ _ => pure ()
      return out
    let covered (x w : Dim.Sp) : Bool := marks.any fun (_, mx, mw) => mx ≤ x && x + w ≤ mx + mw
    t s!"mark: a mark in the accent is painted before the alerted line ({marks.size})"
      (!marks.isEmpty && marks.all (·.1 == accent))
    t "mark: the mark spans the alerted runs and no other"
      ((grounded.filter (·.2.2)).size == 2 && grounded.all fun (x, w, onMark) => covered x w == onMark)
    t "mark: the alerted runs set in the ink on the mark"
      (lines[i]!.segs.all fun s => match s with
        | .run _ c _ _ gs _ _ _ _ ground _ =>
          !(String.ofList (gs.map (·.2.1)).toList == "marked") || (c == Ir.Color.black && ground == some accent)
        | _ => true)
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  let marksHtml := elemNodesList (· == "mark") #[] body.toList
  t "mark: the web page sets the alert in a mark"
    (marksHtml.size == 1 && marksHtml.all fun n => nodeTextOne "" n == "marked words")
  t "mark: the mark's background is the alert's mark"
    (marksHtml.all fun n => match n with
      | .elem _ attrs _ => attrs.any fun (k, v) => k == "style" && hasStr v "background-color" &&
          hasStr v (Ir.ColorRef.role .alertMark).property
      | _ => false)
  t "mark: the stylesheet declares the alert's mark" (hasStr css ((Ir.ColorRef.role .alertMark).property ++ ":"))
  -- A long alert in a narrow box breaks with its mark.
  let long := "\\begin{frame}\n\\begin{minipage}{3cm}\n\\alert{a long alerted sentence that " ++
    "must break across lines}\n\\end{minipage}\n\\end{frame}"
  let (ldoc, _) := elabStr (dvDeck pre long)
  let llines := allLines (layoutOf fonts ldoc)
  let set := (List.range llines.size).filter fun i =>
    let tx := lineText llines[i]!
    hasStr tx "alerted" || hasStr tx "break" || hasStr tx "lines"
  t s!"mark: a long alert sets on more than one line ({set.length})" (set.length ≥ 2)
  t "mark: each line the alert sets on has its own mark"
    (set.all fun i => !(marksBefore llines i).isEmpty)
  -- A TeX build names the mark as an xcolor colour of its key, which both
  -- engines read: leantex as the role.
  let (xdoc, _) := elabStr (dvDeck ("\\usepackage{xcolor}\n\\palette{ alert = #1C1917 }\n" ++
      "\\definecolor{alertmark}{HTML}{FFEE00}\n")
    "\\begin{frame}\nWords and \\alert{marked words}.\n\\end{frame}")
  t "mark: an xcolor alertmark declares the alert's mark"
    (Ir.Design.declared? xdoc.palette .alertMark == some (Ir.Color.ofHtml 0xFF 0xEE 0x00))
  let xlines := allLines (layoutOf fonts xdoc)
  t "mark: and the alert sets on it"
    (match xlines.findIdx? (fun l => hasStr (lineText l) "marked") with
     | some i => (marksBefore xlines i).any (·.1 == Ir.Color.ofHtml 0xFF 0xEE 0x00)
     | none => false)

end Tests.AlertMark
