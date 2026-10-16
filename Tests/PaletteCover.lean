module

public import Tests.Support
public import LeanTex.Core.SeedPalette

public section

open LeanTex.Core

/-! A deck covers its pending steps at the share it declares, hidden when it declares none, and a
generated palette's derived text tones keep the covered-state contract there, its seeds as given. -/

namespace Tests.PaletteCover

/-- The covered-state contract read off its primitives: each covered form at a share, mixed toward
the page in Oklab and in sRGB, quieter on the page than the tone and 3:1 from it (SC 1.4.11). -/
def kept (share : Nat) (page c : Ir.Color) : Bool :=
  (coverForms share page c).all fun cv =>
    decide (Contrast.contrastMilli cv page < Contrast.contrastMilli c page) &&
      decide (Contrast.aaNonText ≤ Contrast.contrastMilli c cv)

/-- A colour over a page at a share as a browser's 8-bit alpha composites it: the share rounded to
an alpha out of 255, each channel rounded. -/
def alphaOver (share : Nat) (page c : Ir.Color) : Ir.Color :=
  let a := (share * 255 + 50) / 100
  let ch (x y : UInt8) : UInt8 := UInt8.ofNat ((x.toNat * a + y.toNat * (255 - a) + 127) / 255)
  { r := ch c.r page.r, g := ch c.g page.g, b := ch c.b page.b }

/-- Whether a share binds a palette's derived text: the tone search's passing end, black on a light
page and white on a dark one, keeps the contract there. -/
def binds (share : Nat) (s : SeedPalette.Seeds) : Bool :=
  kept share s.paper (if s.dark then Ir.Color.white else Ir.Color.black)

/-- Whether a colour is a seed a palette sets as text. -/
def isSeed (s : SeedPalette.Seeds) (c : Ir.Color) : Bool :=
  c == s.ink || c == s.accent || s.alert == some c || s.exampleColor == some c

/-- Invented seeds in both polarities: an orange meeting a deck's floor as given, a teal, a violet
ink's orange, a yellow container, a magenta with a green example too light for text, an amber too
light for text on white, and an amber on a dark paper. -/
def seeds : List (String × SeedPalette.Seeds) := [
  ("an orange meeting a deck's floor",
    { ink := Ir.Color.ofHtml 0x1C 0x19 0x17, paper := Ir.Color.white,
      accent := Ir.Color.ofHtml 0xF0 0x6E 0x00 }),
  ("a teal on cream",
    { ink := Ir.Color.ofHtml 0x3B 0x2F 0x2A, paper := Ir.Color.ofHtml 0xFB 0xF6 0xEC,
      accent := Ir.Color.ofHtml 0x0D 0x94 0x88 }),
  ("a violet ink's orange",
    { ink := Ir.Color.ofHtml 0x2B 0x24 0x40, paper := Ir.Color.white,
      accent := Ir.Color.ofHtml 0xE8 0x5D 0x2A }),
  ("a yellow container",
    { ink := Ir.Color.black, paper := Ir.Color.white, accent := Ir.Color.ofHtml 0xFA 0xCC 0x15 }),
  ("a magenta with a green example",
    { ink := Ir.Color.ofHtml 0x1A 0x1A 0x1A, paper := Ir.Color.white,
      accent := Ir.Color.ofHtml 0xC0 0x26 0xD3, exampleColor := some (Ir.Color.ofHtml 0x22 0xC5 0x5E) }),
  ("an amber too light for text on white",
    { ink := Ir.Color.ofHtml 0x1C 0x19 0x17, paper := Ir.Color.white,
      accent := Ir.Color.ofHtml 0xF2 0xA5 0x41 }),
  ("an amber on a dark paper",
    { ink := Ir.Color.ofHtml 0xF4 0xF1 0xEA, paper := Ir.Color.ofHtml 0x1B 0x24 0x30,
      accent := Ir.Color.ofHtml 0xF2 0xA5 0x41 })]

/-- A share binds a deck's derived text tones in each scheme where it binds at all, and nothing
else: no share, a hidden one or a medium that never covers asks nothing, seeds ship as given, and
the edge, the mark and the grounds stay. -/
def coverChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let orange := seeds.head?.map (·.2) |>.getD SeedPalette.classSeeds
  t "cover: a deck's targets carry the share it declares, and none when it declares none or hides"
    ((orange.targets .decks).cover.isNone && (orange.targetsAt .decks (some 15)).cover == some 15 &&
      (orange.targetsAt .decks (some 0)).cover.isNone && (orange.targetsAt .decks none).cover.isNone &&
      (orange.targetsAt .documents (some 15)).cover.isNone &&
      (orange.targetsAt .posters (some 15)).cover.isNone)
  t "cover: half binds every seed here, and three fifths none, black's covered form under 3:1 there"
    (seeds.all (binds 50 ·.2) && seeds.all (!binds 60 ·.2))
  t "cover: no bundle declares a share, so a deck covers as its document declares, else hides"
    (Theme.builtin.all (·.palette.coveredFraction.isNone))
  for (label, s) in seeds do
    for share in [15, 31, 38, 50, 60] do
      for (sname, base) in [("", s.targets .decks), (" asking more", (s.targets .decks).more)] do
        let at_ := s!"cover, {label}, {share}%{sname}"
        let tg := { base with cover := some share }
        match SeedPalette.generate s tg, SeedPalette.generate s base with
        | .ok g, .ok plain =>
          let c := g.colors
          let tones := [c.accentText, c.alert] ++ c.exampleText.toList
          let plainTones := [plain.colors.accentText, plain.colors.alert] ++ plain.colors.exampleText.toList
          t s!"{at_}: each seed set as text ships as given"
            ((plainTones.zip tones).all fun (p, x) => !isSeed s p || x == p)
          if binds share s then
            t s!"{at_}: each derived text tone keeps the covered-state contract"
              (tones.all fun x => isSeed s x || kept share s.paper x)
            t s!"{at_}: each derived text tone keeps 3:1 from its covered form under a browser's 8-bit alpha"
              (tones.all fun x => isSeed s x ||
                decide (Contrast.aaNonText ≤ Contrast.contrastMilli x (alphaOver share s.paper x)))
          else
            t s!"{at_}: a share that does not bind generates as no share does" (c == plain.colors)
          t s!"{at_}: the accent's edge, its mark and the grounds stand where they stood"
            (c.accentEdge == plain.colors.accentEdge && c.alertMark == plain.colors.alertMark &&
              c.surface == plain.colors.surface && c.accentWash == plain.colors.accentWash)
        | .error f, _ => t s!"{at_}: generates, not fail at {reprStr f.role}" false
        | _, .error f => t s!"{at_}: generates without a share, not fail at {reprStr f.role}" false
  let amber := (seeds.find? (·.1 == "an amber too light for text on white")).map (·.2)
    |>.getD SeedPalette.classSeeds
  t "cover: the light amber's text is derived, and a share darkens it"
    ((SeedPalette.generate amber (amber.targets .decks)).toOption.any fun p =>
      p.colors.accentText != amber.accent &&
        (SeedPalette.generate amber (amber.targetsAt .decks (some 15))).toOption.any fun q =>
          q.colors.accentText != p.colors.accentText)
  let th : Theme := { Theme.daylightWith amber with
    palette := { (Theme.daylightWith amber).palette with coveredFraction := some 15 } }
  let real := th.realize .decks
  t "cover: a bundle generates its derived tones at its own share"
    (real.seeded.any (·.targets.cover == some 15) && Ir.Design.declared? real .alert ==
      (SeedPalette.generate amber (amber.targetsAt .decks (some 15))).toOption.map (·.colors.alert))

/-- The palettes a body sets, in order. -/
private def bodyPalettes (doc : Ir.Doc) : Array Ir.Palette :=
  doc.body.filterMap fun b => match b with
    | .setPalette p => some p
    | _ => none

/-- Whether a palette's seeds generate at the share its medium covers at, the palette's own. -/
private def seededAtShare (pal : Ir.Palette) : Bool :=
  pal.seeded.all fun st =>
    st.targets.cover == (st.seeds.targetsAt pal.classColors.depth pal.coveredFraction).cover

/-- The covered-state losses a document reports, by subject. -/
private def coverLosses (doc : Ir.Doc) : Array (Option String) :=
  ((Contrast.docDiags doc).filter (·.code == "W0345")).map (·.subject)

/-- A deck reports a seed its declared share covers under 3:1 once and ships it as given, a derived
tone keeps the contract at that share, a deck declaring none hides and judges nothing, and a share
its body declares, declarations after the seeds and the medium of a document change nothing. -/
def deckChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let accent := Ir.Color.ofHtml 0xF0 0x6E 0x00
  let pre := "\\palette[seeds]{ ink = #1C1917, paper = #FFFFFF, accent = #F06E00 }\n"
  let light := "\\palette[seeds]{ ink = #1C1917, paper = #FFFFFF, accent = #F2A541 }\n"
  let frame := "\\begin{frame}\nFirst.\n\n\\uncover<2>{A \\alert{covered} word.}\n\\end{frame}"
  let (none_, _) := elabStr (dvDeck pre frame)
  t s!"cover deck, no share declared: hidden, nothing judged ({coverLosses none_})"
    ((Ir.Design.ofDoc none_).cover.hidden && (coverLosses none_).isEmpty &&
      Ir.Design.declared? none_.palette .alert == some accent)
  for (label, src) in [("beamer's transparent share", dvDeck ("\\setbeamercovered{transparent}\n" ++ pre) frame),
      ("a share declared after the seeds", dvDeck (pre ++ "\\palette{ covered = 15\\% }\n") frame)] do
    let (doc, _) := elabStr src
    t s!"cover deck, {label}: the accent ships as the alert, as given"
      (Ir.Design.declared? doc.palette .accent == some accent &&
        Ir.Design.declared? doc.palette .alert == some accent)
    t s!"cover deck, {label}: the seed's covered form is reported once ({coverLosses doc})"
      (coverLosses doc == #[some "covered:alert"])
  let (decor, _) := elabStr (dvDeck ("\\setbeamercovered{transparent}\n" ++ pre ++
    "\\palette[decorative]{ covered = 15\\% }\n") frame)
  t s!"cover deck, covered steps declared decorative: the seed ships as given and nothing is reported ({coverLosses decor})"
    ((coverLosses decor).isEmpty && Ir.Design.declared? decor.palette .alert == some accent &&
      decor.palette.coveredFraction == some 15)
  for (label, src) in [("a light accent at beamer's transparent share",
        dvDeck ("\\setbeamercovered{transparent}\n" ++ light) frame),
      ("a light accent at a share declared after its seeds",
        dvDeck (light ++ "\\palette{ covered = 15\\% }\n") frame)] do
    let (doc, _) := elabStr src
    t s!"cover deck, {label}: the derived alert keeps the contract, so nothing is reported ({coverLosses doc})"
      ((coverLosses doc).isEmpty && Contrast.coveredContract doc.palette && seededAtShare doc.palette &&
        (Ir.Design.declared? doc.palette .alert).any (kept 15 Ir.Color.white))
  let (lightNone, _) := elabStr (dvDeck light frame)
  let (lightWide, _) := elabStr (dvDeck ("\\setbeamercovered{transparent}\n" ++ light) frame)
  t "cover deck: a declared share moves the derived alert and no seed"
    (Ir.Design.declared? lightWide.palette .alert != Ir.Design.declared? lightNone.palette .alert &&
      Ir.Design.declared? lightWide.palette .accent == Ir.Design.declared? lightNone.palette .accent &&
      Ir.Design.declared? lightWide.palette .ink == Ir.Design.declared? lightNone.palette .ink)
  let (day, _) := elabStr (dvDeck "\\theme{daylight}\n\\palette{ covered = 50\\% }\n" frame)
  t s!"cover deck, a bundle at a declared share: its seeds ship as given, each reported once ({coverLosses day})"
    (coverLosses day == #[some "covered:alert"] &&
      Ir.Design.declared? day.palette .accent == some Theme.daylightSeeds.accent)
  let (before, _) := elabStr (dvDeck "\\setbeamercovered{transparent}\n\\theme{daylight}\n" frame)
  t "cover deck: a share declared before a theme binds the bundle it installs"
    (before.palette.coveredFraction == some 15 && seededAtShare before.palette &&
      before.palette.seeded.any (·.targets.cover == some 15))
  let blue := Ir.Color.ofHtml 0x0F 0x5F 0xA8
  let (declared, _) := elabStr (dvDeck (light ++ "\\palette{ accent = #0F5FA8 }\n" ++
    "\\setbeamercovered{transparent}\n") frame)
  t "cover deck: a share leaves an accent declared after the seeds as declared"
    (Ir.Design.declared? declared.palette .accent == some blue)
  let (body, _) := elabStr (dvDeck ("\\setbeamercovered{transparent}\n" ++ light)
    (frame ++ "\n\\palette{ covered = 40\\% }\n" ++ frame))
  t "cover deck: a body's share covers the frames after it and leaves the tones the preamble's share generated"
    (!(bodyPalettes body).isEmpty && (bodyPalettes body).all fun p =>
      Ir.Design.declared? p .alert == Ir.Design.declared? lightWide.palette .alert &&
        p.coveredFraction == some 40 && p.seeded.all fun st => st.targets.cover == some Ir.transparentShare)
  let (bodyAccent, _) := elabStr (dvDeck "\\setbeamercovered{transparent}\n"
    (frame ++ "\n\\palette{ covered = 40\\% }\n\\palette{ accent = #F2A541 }\n" ++ frame))
  t "cover deck: a bundle the body regenerates for an accent keeps the share its preamble binds"
    (!(bodyPalettes bodyAccent).isEmpty && (bodyPalettes bodyAccent).all fun p =>
      p.seeded.all fun st => st.targets.cover == some Ir.transparentShare)
  let (bodyCovers, bodyDiags) := elabStr (dvDeck pre ("\\setbeamercovered{transparent}\n" ++ frame))
  t s!"cover deck, a share in the body: the frames after it cover at it, judged there ({coverLosses bodyCovers})"
    (!(bodyDiags.any (·.code == "W0340")) && (Ir.Design.ofDoc bodyCovers).cover.hidden &&
      (bodyPalettes bodyCovers).any (fun p => p.coveredFraction == some 15) &&
      coverLosses bodyCovers == #[some "covered:alert"])
  let (bodyHides, hideDiags) := elabStr (dvDeck ("\\setbeamercovered{transparent}\n" ++ pre)
    ("\\setbeamercovered{invisible}\n" ++ frame))
  t s!"cover deck, a body share of none over the preamble's: the frames after it hide, nothing judged ({coverLosses bodyHides})"
    (!(hideDiags.any (·.code == "W0340")) &&
      (bodyPalettes bodyHides).any (fun p => p.coveredFraction == some 0) &&
      (coverLosses bodyHides).isEmpty)
  let (bodyColour, colourDiags) := elabStr (dvDeck pre ("\\palette{ covered = #000000 }\n" ++ frame))
  t s!"cover deck, a covered colour in the body: the frames after it cover in it, judged there ({coverLosses bodyColour})"
    (!(colourDiags.any (·.code == "W0340")) &&
      coverLosses bodyColour == #[some "covered:covered", some "covered:alert"] &&
      (bodyPalettes bodyColour).any fun p => (Ir.Design.declared? p .covered).isSome)
  let (bodyColourT, colourTDiags) := elabStr (dvDeck ("\\setbeamercovered{transparent}\n" ++ pre)
    ("\\palette{ covered = #000000 }\n" ++ frame))
  t s!"cover deck, a covered colour in the body over a share: judged at the share ({coverLosses bodyColourT})"
    (!(colourTDiags.any (·.code == "W0340")) &&
      coverLosses bodyColourT == #[some "covered:covered", some "covered:alert"])
  let (bodySeq, seqDiags) := elabStr (dvDeck pre ("\\palette{ covered = #777777 }\n" ++
    "\\palette{ covered = 0\\% }\n\\setbeamercovered{transparent}\n" ++ frame))
  t "cover deck, covers declared in the body in turn: the last share and the colour stand"
    (!(seqDiags.any (·.code == "W0340")) &&
      (bodyPalettes bodySeq).back?.any fun p => p.coveredFraction == some 15 &&
        Ir.Design.declared? p .covered == some (Ir.Color.ofHtml 0x77 0x77 0x77))
  let (bodySame, sameDiags) := elabStr (dvDeck ("\\setbeamercovered{transparent}\n" ++ pre)
    ("\\setbeamercovered{transparent}\n" ++ frame))
  t "cover deck, a body share agreeing with the preamble's names nothing"
    ((sameDiags.filter (·.code == "W0340")).isEmpty && (bodyPalettes bodySame).all (·.coveredFraction == some 15))
  let art := "\\documentclass{article}\n" ++ light ++ "\\palette{ covered = 15\\% }\n" ++
    "\\begin{document}\nA word.\n\\end{document}"
  let (doc, _) := elabStr art
  let s : SeedPalette.Seeds :=
    { ink := Ir.Color.ofHtml 0x1C 0x19 0x17, paper := Ir.Color.white, accent := Ir.Color.ofHtml 0xF2 0xA5 0x41 }
  t "cover: a document, which never covers, generates its seeds as no share binds them"
    (doc.palette.seeded.all (·.targets.cover.isNone) &&
      Ir.Design.declared? doc.palette .alert ==
        (SeedPalette.generate s (s.targets .documents)).toOption.map (·.colors.alert))

/-- A deck declaring no share hides a pending step, its place kept, as beamer's default `invisible`
does, and covers it at beamer's transparent share, a given share or none as declared, in the PDF's
covered ink and the web page's covered opacity. -/
def hiddenChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← serifFacesSet | failures ref "hidden: the serif faces load"
  let frame := "\\begin{frame}\nFirst words.\n\n\\uncover<2>{Kilo words.}\n\nLast words.\n\\end{frame}"
  let cases : List (String × String × Option Nat) := [
    ("no share declared", "", none),
    ("beamer's invisible", "\\setbeamercovered{invisible}\n", none),
    ("beamer's transparent", "\\setbeamercovered{transparent}\n", some 15),
    ("beamer's transparent at 40", "\\setbeamercovered{transparent=40}\n", some 40),
    ("a declared share", "\\palette{ covered = 25\\% }\n", some 25)]
  for (label, more, share) in cases do
    let (doc, _) := elabStr (dvDeck more frame)
    let d := Ir.Design.ofDoc doc
    let ink := d.fg
    let out := layoutOf fonts doc
    let lastAt (p : Nat) : Option Dim.Sp :=
      (out.pages[p]?.bind fun pg => pg.lines.find? fun l => (wordRun #[l] "Last").isSome).map (·.y)
    t s!"hidden, {label}: the second step ships the word in the ink" (wordOn out 1 "Kilo" == some ink)
    t s!"hidden, {label}: the step after it stands where it stands once the word shows"
      (lastAt 0 == lastAt 1 && (lastAt 0).isSome)
    match share with
    | none =>
      t s!"hidden, {label}: the first step ships none of the pending word" (wordOn out 0 "Kilo").isNone
    | some n =>
      t s!"hidden, {label}: the first step ships the word in its {n}% cover"
        (wordOn out 0 "Kilo" == some (Oklab.cover n d.bg ink))
    let (html, _) := HtmlDoc.emit {} doc
    t s!"hidden, {label}: the web page covers the pending step at the share, none hidden"
      (hasStr (stepCssResolved html) s!"from \{ opacity: {share.getD 0}%;")
  -- What a hidden step ships: no ink on a pending item's line, its marker's, image's and link's
  -- included, whatever its marker, and no ground of a block it holds, nothing in the hidden paint.
  let items := "\\item<2> Kilo words \\includegraphics[height=0.3cm]{absent.png} " ++
    "\\href{https://example.org}{linked words}.\n\\item<2> Lima words.\n"
  let markers : List (String × String × String) := [
    ("a bullet", "", "itemize"),
    ("a numbered item", "", "enumerate"),
    ("a coloured marker", "\\style{itemize}{ marker = {\\textcolor{red}{*}} }\n", "itemize"),
    ("an image marker", "\\style{itemize}{ marker = {\\includegraphics[height=0.2cm]{absent.png}} }\n",
      "itemize")]
  for (label, pre, env) in markers do
    let src := dvDeck pre (s!"\\begin\{frame}\n\\begin\{{env}}\n\\item First words.\n" ++ items ++
      s!"\\end\{{env}}\n\\end\{frame}")
    let out := layoutOf fonts (elabStr src).1
    let lineOf (w : String) := out.pages[1]?.bind fun p => p.lines.find? fun l => (wordRun #[l] w).isSome
    let ys := [lineOf "Kilo", lineOf "Lima"].filterMap (·.map (·.y))
    let red := Ir.Color.ofHtml 0xFF 0x00 0x00
    t s!"hidden item, {label}: the step showing it inks its lines, its marker, image and link"
      (ys.length == 2 && (lineOf "Kilo").any (fun l => l.segs.any (· matches .image _ _ _ true) &&
        l.segs.any fun sg => match sg with
          | .run _ _ link .. => link == some "https://example.org"
          | _ => false) &&
        [lineOf "Kilo", lineOf "Lima"].all fun l? => l?.any fun l => (l.segs[0]?.any (·.inks)) &&
          (label != "a coloured marker" || l.segs.any fun sg => match sg with
            | .run _ c .. => c == red
            | _ => false))
    t s!"hidden item, {label}: the step hiding them inks nothing on their lines, marker, image and link included"
      (out.pages[0]?.any fun p =>
        let at_ := p.lines.filter fun l => ys.contains l.y
        at_.size ≥ 2 && at_.all fun l => l.segs.all (!·.inks))
    let (_, tree, _) := HtmlDoc.emitTree {} (elabStr src).1
    let stepped := (elemAttrsList (· == "li") #[] tree.toList).filter fun (_, attrs) =>
      (((HtmlDoc.attrOf? attrs "class").getD "").splitOn " ").contains "step" &&
        attrs.contains ("data-step", "2")
    t s!"hidden item, {label}: the web page steps each pending item whole, its marker with it"
      (stepped.size == 2)
  let shapes := "\\begin{frame}\n\\begin{itemize}\n\\item First words.\n\\item<2> Kilo words.\n" ++
    "\\item<2-> Lima words.\n\\item<1,3> Mike words.\n\\item<2-3> Nova words.\n\\end{itemize}\n" ++
    "\\begin{enumerate}\n\\item<2> One words.\n\\item Two words.\n\\end{enumerate}\n" ++
    "\\begin{description}\n\\item<3>[Term] Defining words.\n\\end{description}\n\\end{frame}"
  let (_, shapeTree, _) := HtmlDoc.emitTree {} (elabStr (dvDeck "" shapes)).1
  let liNodes := elemNodesList (· == "li") #[] shapeTree.toList
  let liAttrs := elemAttrsList (· == "li") #[] shapeTree.toList
  let carries (cls step : String) (last : Option String) : Bool :=
    liAttrs.any fun (_, attrs) => attrs.contains ("class", cls) && attrs.contains ("data-step", step) &&
      last.all fun u => attrs.contains ("data-step-last", u)
  t "hidden item shapes: no list item stands inside another"
    (liNodes.size == 8 && liNodes.all fun n => match n with
      | .elem _ _ kids => kids.all fun k => !(k matches .elem "li" _ _)
      | .text _ | .style _ | .script .. => true)
  t "hidden item shapes: each stepped item carries its selector on its own element"
    (carries "step step-end" "2" (some "2") && carries "step" "2" none &&
      carries "step step-end" "2" (some "3") && carries "step step-end" "2" (some "2") &&
      carries "step step-end" "3" (some "3") &&
      liAttrs.any fun (_, attrs) => attrs.contains ("class", "step-set") &&
        attrs.contains ("data-steps", "1 3"))
  let block := "\\begin{frame}\nFirst words.\n\n\\pause\n\n" ++
    "\\begin{block}{Block title}Block words.\\end{block}\n\\end{frame}"
  let out := layoutOf fonts (elabStr (dvDeck "\\theme{daylight}\n" block)).1
  let fills (k : Nat) : Array Layout.Fill := (out.pages[k]?.map (·.fills)).getD #[]
  t "hidden block: the step showing it paints its grounds"
    (out.pages.size == 2 && (fills 0).size < (fills 1).size)
  t "hidden block: the step hiding it paints none of them, nothing in the hidden paint"
    ((fills 0).all (·.color != Layout.hiddenPaint) &&
      (fills 0).all fun f => (fills 1).any fun g => reprStr g == reprStr f)

end Tests.PaletteCover
