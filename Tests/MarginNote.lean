module

public import Tests.Support

public section

open LeanTex.Core

/-! A margin note sets beside its line as LaTeX's `\marginpar` does, below the note before it and
its push, in the page's own margin or the other where reversed; on the web page it is an aside
after its paragraph, in the article layout's margin column beside its anchor. -/

namespace Tests.MarginNote

/-- An invented paragraph long enough to set several lines. -/
private def words : String :=
  "Alpha bravo charlie delta echo foxtrot golf hotel india juliet kilo lima mike november oscar \
papa quebec romeo sierra tango uniform victor whiskey xray yankee zulu."

private def texDoc (opts pre body : String) : String :=
  s!"\\documentclass[{opts}]\{article}" ++ pre ++ "\\begin{document}" ++ body ++ "\\end{document}"

/-- The lines of a page the note text `w` opens, as a margin note sets them. -/
private def linesWith (out : Layout.Out) (page : Nat) (w : String) : Array Layout.LineOut :=
  (out.pages[page]?.map fun p => p.lines.filter fun l => (wordRun #[l] w).isSome).getD #[]

private def firstY (out : Layout.Out) (page : Nat) (w : String) : Option Dim.Length :=
  (linesWith out page w)[0]?.map (·.y)

private def firstX (out : Layout.Out) (page : Nat) (w : String) : Option Dim.Length :=
  (linesWith out page w)[0]?.map (·.x)

/-- The marginnote numbers lualatex 1.24 sets: paper width, text width, two-sided, body size, a
book's size file; then `\marginparwidth`, `\marginparsep` and `\marginparpush` in points. -/
private def latexRows : List ((Dim.Length × Nat × Bool × Nat × Bool) × (Int × Int × Int)) :=
  let letter := Dim.inch 17 / 2
  let a4 := Dim.mm 210
  [((letter, 345, false, 10, false), (65, 11, 5)), ((letter, 360, false, 11, false), (59, 10, 5)),
   ((letter, 390, false, 12, false), (44, 10, 7)), ((letter, 345, true, 10, false), (121, 11, 5)),
   ((letter, 345, true, 10, true), (125, 7, 5)), ((letter, 360, true, 11, true), (116, 7, 5)),
   ((letter, 390, true, 12, true), (98, 7, 7)), ((a4, 345, false, 10, false), (57, 11, 5)),
   ((a4, 360, false, 11, false), (50, 10, 5)), ((a4, 390, false, 12, false), (35, 10, 7)),
   ((a4, 345, true, 10, true), (115, 7, 5)), ((a4, 360, true, 11, false), (103, 10, 5))]

def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  for ((w, tw, two, size, book), (mw, sep, push)) in latexRows do
    let page : Ir.PageSpec := { width := w, hmargin := (w - Dim.pt tw) / 2, fontSize := Dim.pt size,
                                twoside := two }
    let mp := Ir.MarginPar.ofPage page book
    t s!"margin note: {size}pt, {tw}pt text, two-sided {two}, book {book} sets lualatex's \
{mw}/{sep}/{push}pt ({repr mp})"
      (mp.width == Dim.pt mw && mp.sep == Dim.pt sep && mp.push == Dim.pt push)
  -- The PDF: beside its line, pushed, a note between paragraphs beside the line before it.
  let src := texDoc "" "" (words ++ "\\marginpar{Kestrel note with words enough to wrap twice.} " ++
    words ++ "\\marginpar{Plover note.} " ++ words ++ "\n\n\\marginpar{Heron note.}\n" ++ words)
  let (doc, ds) := elabStr src
  t s!"margin note: a margin note elaborates clean ({ds.map (·.message)})" ds.isEmpty
  let out := layoutOf oneFace doc
  let g := Layout.Geom.ofPage doc.page
  let mp := doc.page.marginPar
  let right := g.hmargin + g.textWidth + mp.sep
  let anchor := (out.pages[0]?.bind fun p => p.lines.find? fun l =>
    (wordRun #[l] "zulu.").isSome && l.x < right).map (·.y)
  t s!"margin note: its first baseline stands on its line's ({repr (firstY out 0 "Kestrel")}, {repr anchor})"
    (firstY out 0 "Kestrel" == anchor && anchor.isSome)
  t "margin note: it stands a separation right of the text block, its lines within the column"
    (firstX out 0 "Kestrel" == some right && 1 < (linesAfter out 0 "Kestrel" right).size &&
      (linesAfter out 0 "Kestrel" right).all (·.setWidth ≤ mp.width))
  let kestrelEnd := ((linesAfter out 0 "Kestrel" right).back?.map (·.y)).getD 0
  t s!"margin note: the next note stands below it and its push ({repr (firstY out 0 "Plover")})"
    ((firstY out 0 "Plover").any (kestrelEnd + mp.push ≤ ·))
  t "margin note: a note between paragraphs stands below the notes before it"
    ((firstY out 0 "Heron").any fun y => ((firstY out 0 "Plover").getD 0) < y)
  let (lone, _) := elabStr (texDoc "" "" (words ++ "\n\n\\marginpar{Heron note.}\n" ++ words))
  let loneOut := layoutOf oneFace lone
  t s!"margin note: a note between paragraphs stands beside the last line before it, not the next \
({repr (firstY loneOut 0 "Heron")}, {repr (firstY loneOut 0 "zulu.")})"
    (firstY loneOut 0 "Heron" == firstY loneOut 0 "zulu." && (firstY loneOut 0 "zulu.").isSome)
  t s!"margin note: the note between paragraphs joins the paragraph before it, standing between"
    (doc.body.size == 2 && (match doc.body[0]? with
      | some (Ir.Block.para c) => (Ir.marginNotesIn c).size == 3 &&
          (Ir.marginNotesIn c).all (fun (m, b) => m.between == (Ir.plainText b == "Heron note."))
      | _ => false))
  -- Reversed, and on a verso of a two-sided page.
  let (rev, _) := elabStr (texDoc "" "\\reversemarginpar" (words ++ "\\marginpar{Kestrel note.}"))
  let revOut := layoutOf oneFace rev
  let rg := Layout.Geom.ofPage rev.page
  t "margin note: reversed, it stands a separation left of the text block"
    (firstX revOut 0 "Kestrel" == some (rg.hmargin - rev.page.marginPar.sep - rev.page.marginPar.width))
  let (two, _) := elabStr (texDoc "twoside" "" (words ++ "\\marginpar{Recto note.}\\newpage " ++
    words ++ "\\marginpar{Verso note.}"))
  let twoOut := layoutOf oneFace two
  -- The text block's left edge: where most of the page's own lines start.
  let xs := ((twoOut.pages[1]?.map fun p => (p.lines.filter (!·.margin)).map (·.x))).getD #[]
  let textLeft := (xs.foldl (fun (best : Option (Dim.Length × Nat)) x =>
    let n := (xs.filter (· == x)).size
    match best with
    | some (_, k) => if k < n then some (x, n) else best
    | none => some (x, n)) none).map (·.1) |>.getD 0
  t s!"margin note: on a verso it takes the outer, left margin ({repr (firstX twoOut 1 "Verso")})"
    (firstX twoOut 1 "Verso" == some (textLeft - two.page.marginPar.sep - two.page.marginPar.width))
  -- `\reversemarginpar` resets `\@mparbottom`: the next note stands beside its own line.
  let (sw, _) := elabStr (texDoc "" "" ("Short.\\marginpar{Kite note with words enough to wrap three or " ++
    "four times in its column.}\n\nNext.\\reversemarginpar\\marginpar{Swift note.}"))
  let swOut := layoutOf oneFace sw
  t s!"margin note: after a margin switch a note stands beside its line ({repr (firstY swOut 0 "Swift")})"
    (firstY swOut 0 "Swift" == firstY swOut 0 "Next." && (firstY swOut 0 "Next.").isSome)
  -- LaTeX's `\reversemarginpar` is a local switch, `\@if@reversemargin`.
  let (grouped, _) := elabStr (texDoc "" "" ("{\\reversemarginpar " ++ words ++ "\\marginpar{Kite note.}}" ++
    words ++ "\\marginpar{Swift note.}"))
  let sideModes := grouped.body.foldl (fun acc b => match b with
    | .para c => acc ++ (Ir.marginNotesIn c).map (·.1.reversed)
    | _ => acc) #[]
  t s!"margin note: a group's end restores the margin side ({sideModes})"
    (sideModes == #[true, false])
  -- The column fits the declared margin: a narrower one narrows it, one leaving none sets the text.
  let (narrow, _) := elabStr (texDoc "" "\\usepackage[margin=1in]{geometry}" (words ++ "\\marginpar{Kite.}"))
  t s!"margin note: a one-inch margin leaves size10.clo's formula 3pt ({repr narrow.page.marginPar})"
    (narrow.page.marginPar.width == Dim.pt 3)
  let (none_, noneDs) := elabStr (texDoc "" "\\usepackage[margin=0.5in]{geometry}"
    (words ++ "\\marginpar{Kite words.}"))
  t "margin note: a margin with no room for the column sets the note in its text, named"
    (!Ir.foldBlocks (fun b _ => b) (fun b x => b || x matches .marginNote _ _) false none_.body &&
      hasStr (Ir.blocksText none_.body) "Kite words." &&
      noneDs.any fun d => d.kind == .W0457 && hasStr d.message "page")
  -- `\@bsphack` and `\@esphack`: a note between two spaces leaves one.
  let (sp, _) := elabStr (texDoc "" "" "Left words \\marginpar{Kite.} right words.")
  t s!"margin note: a note between two spaces leaves one ({repr (Ir.blocksText sp.body)})"
    (hasStr (Ir.blocksText sp.body) "Left words Kite.right words.")
  -- A margin paragraph sets as a line, `\@parboxrestore`'s flush, unindented paragraph.
  let (twoPar, twoParDs) := elabStr (texDoc "" "" (words ++ "\\marginpar{First line.\n\nSecond line.}"))
  let twoParNotes := twoPar.body.foldl (fun acc b => match b with
    | .para c => acc ++ (Ir.marginNotesIn c).map (·.2)
    | _ => acc) #[]
  t "margin note: a paragraph break in a note is a line break, unnamed"
    (twoParDs.all (·.kind != .W0371) && twoParNotes.any fun b => b.any (· matches .linebreak _))
  -- Elaboration: the package forms, the refusals.
  let (pk, pkDs) := elabStr (texDoc "" "\\usepackage{marginnote}\\usepackage{sidenotes}"
    ("A.\\marginnote{Ragged.}[2pt] B.\\sidenote{First.} C.\\sidenote{Second.} D.\\sidenote[7]{Seventh.} " ++
      "E.\\sidenote{Third.} F.\\marginnote[Left.]{Right.}"))
  let modes := pk.body.foldl (fun acc b => match b with
    | .para c => acc ++ (Ir.marginNotesIn c).map (·.1)
    | _ => acc) #[]
  t s!"margin note: marginnote's is ragged, sidenotes' numbered in turn or as given ({modes.map (·.num)})"
    (pkDs.all (fun d => d.kind == .N0100 || d.kind == .W0104) && modes.all (·.ragged) &&
      modes.map (·.num) == #[none, some 1, some 2, some 7, some 3, none] &&
      !hasStr (Ir.blocksText pk.body) "Left." && pkDs.any (·.kind == .W0104))
  let (fl, flDs) := elabStr (texDoc "" "" ("\\begin{figure}x\\caption{A caption.\\marginpar{Float note.}}" ++
    "\\end{figure}\n\nText."))
  t "margin note: in a float it sets in the text, named once"
    (!Ir.foldBlocks (fun b _ => b) (fun b x => b || x matches .marginNote _ _) false fl.body &&
      hasStr (Ir.blocksText fl.body) "Float note." &&
      (flDs.filter (·.kind == .W0457)).size == 1)
  let (deck, deckDs) := elabStr ("\\documentclass{beamer}\\begin{document}\\begin{frame}{T}" ++
    "x\\marginpar{Deck note.}\\end{frame}\\end{document}")
  t "margin note: on a frame it sets in the text, named for the class"
    (hasStr (Ir.blocksText deck.body) "Deck note." &&
      deckDs.any fun d => d.kind == .W0457 && d.message == "unsupported margin for class beamer")
  let (_, leftDs) := elabStr (texDoc "" "" "x\\marginpar[Left text.]{Right text.}")
  t "margin note: the left margin's own text is named"
    (leftDs.any fun d => d.kind == .W0104 && hasStr d.message "[left]")
  -- The web page: an aside after its paragraph, positioned only in the article layout.
  let (art, _) := elabStr (texDoc "" "\\page{ web = article }"
    ("\\section{One}" ++ words ++ "\\marginpar{Kestrel note.}\\section{Two}y"))
  let (_, body, _) := HtmlDoc.emitTree {} art
  let asides := elemAttrsList (· == "aside") #[] body.toList
  t "margin note: the web page sets one aside, a note, named against its anchor"
    (asides.size == 1 && asides.all fun (_, a) => HtmlDoc.attrOf? a "role" == some "note" &&
      HtmlDoc.attrOf? a "id" == some "mn1" &&
      (elemAttrsList (fun _ => true) #[] body.toList).any fun (_, b) =>
        HtmlDoc.attrOf? b "id" == some "mn1-at")
  let facts := HtmlDoc.a11yFacts true false body
  t "margin note: assistive technology reads the aside with its text"
    (facts.marginNotes == 1 && facts.marginNotesEmpty == 0)
  let artCss := HtmlDoc.baseCss {} art
  t "margin note: the article layout sets it in the margin column beside its anchor"
    (hasStr artCss "@supports (anchor-name: --a)" && hasStr artCss "anchor(var(--mn-at) top)")
  let (book, _) := elabStr (texDoc "" "" (words ++ "\\marginpar{Kestrel note.}"))
  t "margin note: the book layout keeps it after its paragraph"
    (!hasStr (HtmlDoc.baseCss {} book) "anchor(var(--mn-at) top)" &&
      hasStr (HtmlDoc.baseCss {} book) "aside.margin-note")
  -- Markdown: MyST's aside and margin directives.
  let (md, mdDs) := elabMd ("A paragraph.\n\n:::{aside}\nAn aside.\n:::\n\nNext.\n\n:::{margin}\n" ++
    "A margin.\n\nIts second line.\n:::\n")
  let mdNotes := md.body.foldl (fun acc b => match b with
    | .para c => acc ++ (Ir.marginNotesIn c).map fun (m, b) => (m.between, Ir.plainText b)
    | _ => acc) #[]
  t s!"margin note: MyST's aside and margin stand beside the paragraph before them ({mdNotes})"
    (mdDs.isEmpty && mdNotes.map (·.1) == #[true, true] &&
      (mdNotes.map (·.2)).any (hasStr · "Its second line"))
  t "margin note: the markdown twin writes each as MyST's aside after its paragraph"
    (hasStr (MarkdownDoc.emit md) ":::{aside}\nAn aside.\n:::")
  let (_, listDs) := elabMd "A paragraph.\n\n:::{aside}\n- a list\n\n:::\n"
  t "margin note: an aside holding a list sets in the text, named"
    (listDs.any fun d => hasStr d.message "margin note")
  let (_, openDs) := elabMd "A paragraph.\n\n:::{aside}\nNever closed.\n"
  t "margin note: an aside no fence closes is named"
    (openDs.any fun d => d.kind == .W0392 && hasStr d.message "aside")
  -- Notes waiting after a heading stand beside a list's first line, else set in the text.
  let (headed, _) := elabMd "# Heading\n\n:::{margin}\nBeside the list.\n:::\n\n- one item\n- two\n"
  t "margin note: a note before a list stands beside its first item"
    (headed.body.any fun b => match b with
      | .list _ _ items => items[0]?.any fun item => item.any fun ib => match ib with
        | .para c => !(Ir.marginNotesIn c).isEmpty
        | _ => false
      | _ => false)
  let (twice, _) := elabMd "# Heading\n\n:::{margin}\nOne.\n:::\n\n:::{margin}\nTwo.\n:::\n\nText after.\n"
  t "margin note: two notes waiting after a heading open no empty paragraph"
    (twice.body.all fun b => match b with
      | .para c => !(c.all fun x => x matches .marginNote _ _)
      | _ => true)
  let (tail, tailDs) := elabMd "# Heading\n\n:::{margin}\nNothing follows.\n:::\n"
  t "margin note: a note nothing follows sets in the text, named"
    (hasStr (Ir.blocksText tail.body) "Nothing follows." &&
      !Ir.foldBlocks (fun b _ => b) (fun b x => b || x matches .marginNote _ _) false tail.body &&
      tailDs.any (·.kind == .W0457))
  -- A list item's first paragraph sets its aside, so every anchor keeps its note.
  let (inItem, _) := elabStr (texDoc "" "\\page{ web = article }"
    ("\\begin{itemize}\\item Item words\\marginpar{Item note.}\n\nMore item words.\\end{itemize}" ++
      words ++ "\\marginpar{Kestrel note.}"))
  let (_, itemBody, _) := HtmlDoc.emitTree {} inItem
  let ids := (elemAttrsList (fun _ => true) #[] itemBody.toList).filterMap fun (_, a) => HtmlDoc.attrOf? a "id"
  t s!"margin note: a list item's paragraph sets its aside ({ids.filter (·.startsWith "mn")})"
    ((elemAttrsList (· == "aside") #[] itemBody.toList).size == 2 &&
      ["mn1-at", "mn1", "mn2-at", "mn2"].all ids.contains)
  let (outlined, _) := elabStr (texDoc "" "\\page{ web = article }"
    ("\\section{One}" ++ words ++ "\\marginpar{Kestrel note.}\\section{Two}y\\section{Three}z"))
  t "margin note: the margin's notes stand below an outline sharing their column"
    (hasStr (HtmlDoc.baseCss {} outlined) "anchor-name: --mn0")
  t "margin note: a labelled item's or a titled block's note stays in its flow"
    (hasStr (HtmlDoc.baseCss {} outlined) ":is(li.labelled, section[class]) aside.margin-note { position: static")

where
  linesAfter (out : Layout.Out) (page : Nat) (w : String) (x : Dim.Length) : Array Layout.LineOut :=
    let all := (out.pages[page]?.map (·.lines)).getD #[]
    match all.findIdx? fun l => (wordRun #[l] w).isSome with
    | some i => (all.extract i all.size).toList.takeWhile (·.x == x) |>.toArray
    | none => #[]

end Tests.MarginNote
