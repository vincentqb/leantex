module

public import LeanTex.Cli.FontDiscovery
public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- The margin number column of a page census: furniture lines standing
left of the measure. The plain foot's page number is furniture too, but
it centres inside the measure, so the x test tells them apart. -/
def marginNumbers (geom : Layout.Geom) (c : Array CensusPage) :
    Array (Array CensusLine) :=
  c.map fun p => p.lines.filter fun l =>
    l.furniture && l.x + l.width ≤ geom.hmargin

/-- The shipped-page rule for `\page{ linenumbers = on }`: on a numbered
page every counted body line carries exactly one margin number at its own
baseline, and the numbers run consecutively across pages from 1. -/
def linenoCensus (geom : Layout.Geom) (c : Array CensusPage) :
    List (String × Bool) :=
  let margin := marginNumbers geom c
  let counted := c.map fun p => p.lines.filter (·.counted)
  [("the article spans two pages", c.size ≥ 2),
   ("every counted body line carries exactly one margin number at its \
baseline, consecutively from 1 across pages",
     Id.run do
       let mut k := 0
       let mut ok := true
       for (cl, ml) in counted.zip margin do
         ok := ok && ml.size == cl.size
         for l in cl do
           k := k + 1
           ok := ok && (ml.filter fun m =>
             m.y == l.y && m.text.trimAscii.toString == toString k).size == 1
       return ok && k > 0),
   ("the heading line is counted",
     ((c[0]?.bind fun p => p.lines.find? fun l =>
       hasStr l.text "Numbered galley").map (·.counted)).getD false),
   ("the display formula's line is counted — numbered like every line \
here, where lineno's default is not (the recorded divergence)",
     ((c[0]?.bind fun p => p.lines.find? fun l =>
       hasStr l.text "=").map (·.counted)).getD false),
   ("the float's body and caption are box content, not counted",
     c.toList.all fun p => p.lines.all fun l =>
       !(hasStr l.text "floated caption" && l.counted) &&
       !(hasStr l.text "float body" && l.counted)),
   ("the footnote is an insertion, not counted",
     c.toList.all fun p => p.lines.all fun l =>
       !(hasStr l.text "insertion" && l.counted)),
   ("the numbers set at the footnotesize step, right-aligned with the \
undeclared column hanging from half the margin",
     (margin.toList.all fun ml => ml.toList.all fun m =>
       m.size == Ir.scaleStep geom.fontSize "footnotesize" &&
       m.x + m.width == geom.hmargin / 2) &&
     margin.toList.any (!·.isEmpty))]

/-- The modulo half of the rule: the count advances on every counted
line, and the modulus filters what prints — multiples only, in order,
each at a counted line's own baseline. -/
def linenoModuloCensus (geom : Layout.Geom) (c : Array CensusPage) :
    List (String × Bool) :=
  let margin := (marginNumbers geom c).foldl (· ++ ·) #[]
  let countedLines := c.foldl (fun a p => a ++ p.lines.filter (·.counted)) #[]
  [("one page", c.size == 1),
   ("the count crosses the second modulus", countedLines.size ≥ 10),
   ("only multiples of five print, in order — the count still advances \
on every counted line",
     margin.map (·.text.trimAscii.toString) ==
       (Array.range (countedLines.size / 5)).map fun i => toString ((i + 1) * 5)),
   ("each printed number stands at a counted line's own baseline",
     margin.all fun m => countedLines.any fun l => l.y == m.y)]

/-- A conditional fixture's census: one page, every kept branch ships and
no hidden branch does. The branch TeX takes is the claim, read off the page
(lualatex ships exactly the kept branches of each). -/
def condBranchRow (kept hidden : List String) :
    Layout.Geom → Array CensusPage → List (String × Bool) := fun _ c =>
  [("one page", c.size == 1)] ++
  kept.map (fun k => (s!"the branch TeX keeps ships: {k}", hasStr (censusText c) k)) ++
  hidden.map (fun h => (s!"the branch TeX skips does not: {h}", !hasStr (censusText c) h))

/-- Census assertions, one row per golden fixture: what each fixture's
shipped pages must show, judged from `Layout.Out` — never from the IR dump,
which witnesses elaboration only. `censusChecks` fails when a fixture in
`goldenNames` has no row here, so a fixture cannot enter the suite
witnessed by its golden alone. Facts are observable page claims: text
shipped (or deliberately not, for a note), covered-coloured runs on step
pages, rules and fills drawn, line positions for centring and columns. -/
def censusRows0 :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  ("affine-lengths", fun _ c => [
    ("one page", c.size == 1),
    ("every unequal measure ships its labelled content",
      ["Top measure", "Minipage measure", "Column measure", "Paragraph cell",
        "Target-width cell"].all (hasStr (censusText c) ·)),
    ("every affine rule reaches the shipped page",
      (c[0]?.map (·.rules)).getD 0 == 5)]),
  ("listings", fun geom c => [
    ("one page", c.size == 1),
    -- a no-break space ships as a glyphless box, so the census text of a
    -- code line reads glued ("1defprobe(n):"), exactly as "Equation(1)"
    ("the caption ships numbered with the locale's listing word, above the code",
      hasStr (censusText c) "Listing 1: An invented probe." &&
      ((lineYOf c 0 "An invented probe").bind fun cy =>
        (lineYOf c 0 "defprobe(n):").map fun ly => decide (cy < ly)).getD false),
    ("the declared line numbers ship as furniture beside their lines",
      pageHas c 0 "1defprobe(n):" && pageHas c 0 "2returnn+1"),
    ("the minted body ships its code and never its language argument",
      pageHas c 0 "print(\"synthetic\")" && !hasStr (censusText c) "python"),
    ("the reference resolves to the listing's number",
      hasStr (censusText c) "adds one"),
    ("the quantity ships its unit symbols",
      hasStr (censusText c) "345.6" && hasStr (censusText c) "kg"),
    ("the code inherits the surrounding size when none is declared",
      lineSizeOf c 0 "defprobe(n):" == some geom.fontSize)]),
  ("footnotes", fun geom c => [
    ("the article spans two pages", c.size ≥ 2),
    ("the first note ships at the foot of page one",
      pageHas c 0 "first" && pageHas c 0 "foot of page one" &&
      ((lineYOf c 0 "invented survey").bind fun sy =>
        (lineYOf c 0 "foot of page one").map fun ny => decide (sy < ny)).getD false),
    ("the note ink stands above bodyBottom, in the text block",
      ((lineYOf c 0 "foot of page one").map fun ny =>
        decide (ny ≤ geom.pageH - geom.vmargin)).getD false),
    ("the mark's digit ships raised beside its word",
      pageHas c 0 "here1"),
    ("the boundary note shares its mark's page, wherever the break fell",
      (List.range c.size).any fun i =>
        pageHas c i "boundary claim" && pageHas c i "boundary note"),
    ("no page carries a note whose mark is elsewhere",
      (List.range c.size).all fun i =>
        (!pageHas c i "boundary note" || pageHas c i "boundary claim") &&
        (!pageHas c i "foot of page one" || pageHas c i "invented survey")),
    ("the override mark ships as 12, unstepped",
      hasStr (censusText c) "number12" && hasStr (censusText c) "chosen note"),
    ("the footnote rule ships at its declared weight above the notes",
      ((lineYOf c 0 "foot of page one").map fun ny =>
        (pageRuleSegs c 0).any fun rt =>
          decide (rt.1 < ny) && rt.2 == geom.fontSize * 4 / 100).getD false),
    ("the notes set at footnotesize",
      lineSizeOf c 0 "foot of page one" ==
        some (geom.fontSize * ((Ir.sizeScale.lookup "footnotesize").getD 1000) / 1000))]),
  ("eqnum", fun geom c => [
    ("one page", c.size == 1),
    ("the first equation ships its number", hasStr (censusText c) "(1)"),
    ("the opted-out display frees its number for the next",
      hasStr (censusText c) "(2)" && !hasStr (censusText c) "(3)"),
    ("the number is right-aligned on the measure",
      -- to the sp integer division owes the fil pair, as pad_center does
      (lineRightOf c 0 "(1)").any fun r =>
        decide (r ≤ geom.hmargin + geom.textWidth ∧
          geom.hmargin + geom.textWidth - r ≤ 2)),
    ("eqref resolves to the parenthesised number",
      hasStr (censusText c) "Equation(1)")]),
  ("crossref", fun _ c => [
    ("one page", c.size == 1),
    ("a resolved reference ships its number on the page",
      hasStr (censusText c) "Section1 opened"),
    ("eqref ships its parenthesised number", hasStr (censusText c) "(2)"),
    ("an unresolved reference ships LaTeX's ??",
      hasStr (censusText c) "see??"),
    ("an appendix reference letters itself",
      hasStr (censusText c) "AppendixA letters"),
    ("the heading line carries its number beside its title",
      ((c[0]?.bind fun p => p.lines.find? fun l => hasStr l.text "Alpha").map
        fun l => hasStr l.text "1").getD false),
    ("float references ship the numbers their captions carry",
      hasStr (censusText c) "Figure1 and Table1 are referenced"),
    ("the captions ship those same numbers as their prefixes",
      hasStr (censusText c) "Figure 1: An invented crossref panel."
        && hasStr (censusText c) "Table 1: An invented data strip.")]),
  ("abstract", fun geom c => [
    ("one page", c.size == 1),
    ("the class furniture heading ships", hasStr (censusText c) "Abstract"),
    ("the abstract body ships", hasStr (censusText c) "Entirely synthetic findings"),
    ("the abstract body is set off the margin",
      (lineXOf c 0 "Entirely synthetic findings").any fun x => decide (x > geom.hmargin)),
    ("the following body returns to the margin",
      lineXOf c 0 "Body text follows the abstract" == some geom.hmargin),
    -- The abstract heading follows the styled section heading
    -- (`Ir.abstract_heading_follows_section`): same font on the shipped
    -- page — \large is 1.2x, no engine default (the small-bold abstract
    -- line, the body size) reaches it.
    ("the abstract heading ships in the styled section's font",
      lineSizeOf c 0 "Abstract" == some (geom.fontSize * 1200 / 1000) &&
      lineSizeOf c 0 "Abstract" == lineSizeOf c 0 "Introduction"),
    ("the abstract heading centres in the measure",
      ((lineXOf c 0 "Abstract").map fun x =>
        decide (x > geom.hmargin)).getD false)]),
  ("algorithm", fun _ c => [
    ("the caption ships numbered with the locale word",
      hasStr (censusText c) "Algorithm 1: Exchange sort of an invented list."),
    ("the second algorithm takes the next number",
      hasStr (censusText c) "Algorithm 2: The same exchange sort, algorithmicx spelling."),
    ("the io lines ship their generated labels",
      hasStr (censusText c) "Input:" && hasStr (censusText c) "Output:"),
    ("the generated keywords ship around the declared content",
      hasStr (censusText c) "for" && hasStr (censusText c) "do"
        && hasStr (censusText c) "end"),
    ("the declared statement ships", hasStr (censusText c) "swap"),
    ("the comment ships between its fences",
      hasStr (censusText c) "/* one pass floats the heaviest weight to the end */"),
    ("the else branch ships its keyword and body",
      hasStr (censusText c) "else" && hasStr (censusText c) "keep the pair as it stands"),
    ("the reference resolves to the float's number",
      hasStr (censusText c) "Algorithm1 is restated"),
    ("the line numbers keep one left column whatever the depth",
      ((lineXOf c 0 "swap").bind fun sx =>
        (lineXOf c 0 "keep the pair").bind fun kx =>
        (lineXOf c 0 "Input:").map fun ix =>
          decide (sx = kx ∧ kx = ix)).getD false)]),
  ("paragraphs", fun _ c => [
    ("one page", c.size == 1),
    ("the opening sentence ships", hasStr (censusText c) "Typesetting is the arrangement of type"),
    ("it wraps to at least four lines", (c[0]?.map fun p => decide (p.lines.size ≥ 4)).getD false),
    ("the plain page number ships, the page's last-laid line",
      ((c[0]?.bind fun p => p.lines.back?).map (·.text.trimAscii.toString)) == some "1")]),
  ("layout", fun _ c => [
    ("one page", c.size == 1),
    ("the heading ships", hasStr (censusText c) "The first section"),
    ("a list marker ships beside its item", hasStr (censusText c) "• One concise point")]),
  ("bibliography", fun _ c => [
    ("the numeric citation marks ship in first-citation order",
      hasStr (censusText c) "[1]") ,
    ("a textual citation ships its author names before the mark",
      hasStr (censusText c) "Doe and van der Berg [2]"),
    ("a grouped citation keeps one bracket", hasStr (censusText c) "[3, 1]"),
    ("the unknown key ships its ? mark", hasStr (censusText c) "[?]"),
    ("the References heading ships", hasStr (censusText c) "References"),
    ("the last entry ships with its position's marker",
      hasStr (censusText c) "[7] Casey Ray"),
    ("the accent composes on the shipped page", hasStr (censusText c) "Künzel"),
    ("the corporate author ships unsplit",
      hasStr (censusText c) "Example Press Editorial Group"),
    ("the elided list ships as et al", hasStr (censusText c) "Ariel Fox"),
    ("the howpublished group ships with its year", hasStr (censusText c) "Online, 2020")]),
  ("declared", fun _ c => [
    ("one page, as the fixture asserts", c.size == 1),
    ("the heading ships", hasStr (censusText c) "Declared geometry")])]

def censusRows1 :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  ("redefine", fun _ c => [
    ("one page", c.size == 1),
    ("the refused redefinition leaves the built-in title shipping",
      hasStr (censusText c) "Fallback Title Probe"),
    ("the author ships under it", hasStr (censusText c) "An Invented Author"),
    ("the refused body's internals never ship as text",
      !hasStr (censusText c) "venuetitlebox"),
    ("the runnable redefinition ships its own body",
      hasStr (censusText c) "The runnable body wins.")]),
  ("blocks", fun geom c => [
    ("one page", c.size == 1),
    ("each block ships its title",
      hasStr (censusText c) "A Plain Statement" &&
      hasStr (censusText c) "A Loud Statement" &&
      hasStr (censusText c) "A Worked Instance"),
    ("each body ships under its title",
      ((lineYOf c 0 "A Plain Statement").bind fun ty =>
        (lineYOf c 0 "The body of the plain block").map fun by_ =>
          decide (ty < by_)).getD false &&
      hasStr (censusText c) "The alert body stands under its own title." &&
      hasStr (censusText c) "The example body stands under its own title."),
    ("the untitled block ships its body alone",
      hasStr (censusText c) "An untitled block keeps its body and draws no bar."),
    -- Only `blocktitlebg` is declared, so exactly the plain titled
    -- block draws a bar: alert and example take their content colours
    -- barless, and the untitled block and the bare default theme add
    -- no fill.
    ("the one declared title bar ships as a fill",
      (c[0]?.map (·.fills)).getD 0 == 1),
    ("a filled title uses the shared surface inset",
      lineXOf c 0 "A Plain Statement" ==
        some (geom.hmargin + Ir.titledPadding.resolve geom.fontSize 0)),
    ("unfilled titles stand on the measure",
      lineXOf c 0 "A Loud Statement" == some geom.hmargin &&
      lineXOf c 0 "A Worked Instance" == some geom.hmargin)]),
  ("poster", fun geom c => [
    -- The class's implied faces bound: the one declared frame is one
    -- face, and every glyph ships on it.
    ("one face ships as one page", c.size == 1),
    ("the board is the record's A0 landscape trim",
      geom.pageW == Dim.mm 1189 && geom.pageH == Dim.mm 841),
    ("the margins are the record's 1cm safe zone",
      geom.hmargin == Dim.mm 10 && geom.vmargin == Dim.mm 10),
    ("the body sets at beamerposter's 24.88pt normalsize",
      lineSizeOf c 0 "Body text in the first column" == some (Dim.pt 2488 / 100)),
    ("the poster title ships", hasStr (censusText c) "An Invented Poster Probe"),
    ("both panels ship their titles and bodies",
      hasStr (censusText c) "First Invented Panel" &&
      hasStr (censusText c) "Second Invented Panel" &&
      hasStr (censusText c) "entirely synthetic" &&
      hasStr (censusText c) "likewise synthetic"),
    ("the columns stand side by side",
      ((lineXOf c 0 "Body text in the first column").bind fun x1 =>
        (lineXOf c 0 "Body text in the second column").map fun x2 =>
          decide (x1 < x2)).getD false),
    ("no page number ships on a poster",
      ((c[0]?.bind fun p => p.lines.back?).map
        (·.text.trimAscii.toString != "1")).getD false)]),
  ("poster-headline", fun geom c => [
    -- The band: the title family ships as page-top furniture, its bar
    -- painted from the page top at full width (distinct from the page
    -- ground, which spans the whole face), the title matter centred (the
    -- gemini bundle's declared titlepage alignment), the body below it.
    ("one face ships as one page", c.size == 1),
    ("the band ships the title family",
      hasStr (censusText c) "An Invented Band Title" &&
      hasStr (censusText c) "Alex Placeholder" &&
      hasStr (censusText c) "Sam Example" &&
      hasStr (censusText c) "An Invented Institute"),
    ("the band bar paints from the page top, full width, above the ground",
      ((c[0]?.map (·.fillRects)).getD #[]).any fun r =>
        r.1 == 0 && r.2.1 == 0 && r.2.2.1 == geom.pageW && r.2.2.2 < geom.pageH),
    ("the title matter centres on the declared alignment",
      ((c[0]?.bind fun p => p.lines.find? fun l =>
        hasStr l.text "An Invented Band Title").map fun l =>
          decide ((2 * l.x + l.width - geom.pageW).natAbs ≤ 1)).getD false),
    ("the body columns start below the band",
      (((c[0]?.bind fun p => p.lines.find? fun l =>
          hasStr l.text "An Invented Band Title").map (·.y)).bind fun ty =>
        ((c[0]?.bind fun p => p.lines.find? fun l =>
          hasStr l.text "First Invented Panel").map (·.y)).map fun by_ =>
            decide (ty < by_)).getD false),
    ("the themed alert panel ships its title on a bar",
      hasStr (censusText c) "Second Invented Panel" &&
      (c[0]?.map (·.fills)).getD 0 ≥ 3),
    ("the footercontent line ships as foot furniture",
      ((c[0]?.bind fun p => p.lines.find? fun l =>
        hasStr l.text "An Invented Workshop 2099").map (·.furniture)).getD false),
    ("the corner logo stands as furniture on the band's right",
      (c[0]?.map fun p => p.lines.any fun l =>
        l.furniture && l.text.trimAscii.toString.isEmpty &&
          l.x > geom.pageW / 2).getD false)]),
  ("titleground", fun geom c => [
    ("two pages", c.size == 2),
    ("the title page ships its matter",
      pageHas c 0 "A Placeholder Deck" && pageHas c 0 "P. Placeholder" &&
        pageHas c 0 "example.org"),
    -- The declared ground is a fill the width and height of the page, and
    -- it is the first thing painted: `finishPage` prepends it, so nothing
    -- placed on the page can end up under it.
    ("the title page's ground covers the page and is painted first",
      (c[0]?.bind fun p => p.fillRects[0]?).map
        (fun r => decide (r.1 == (0 : Dim.Sp) ∧ r.2.1 == (0 : Dim.Sp) ∧
          r.2.2.1 == geom.pageW ∧ r.2.2.2 == geom.pageH)) == some true),
    -- Whether that ground is the page's own or the document's is a claim
    -- about its colour, which no census carries: `artGroundParityChecks`
    -- reads the fill's colour off `Layout.Out` and holds the two artifacts
    -- to it. Here: the page after it is a page like any other.
    ("the frame after it ships its own page",
      pageHas c 1 "On the document" &&
        pageHas c 1 "on the ground every other page carries"),
    -- Each datum stands where its slot pins it: the title's anchor 1.6cm
    -- in, its text one inner sep plus pgf's outer anchor clearance inside,
    -- at the slot's own size; the author above the page foot, the
    -- institute set flush right at the foot's other corner.
    ("the title starts inside its pinned node separations",
      lineXOf c 0 "A Placeholder Deck" ==
        some (Dim.mm 16 + Ir.pgfInnerSep geom.fontSize + Ir.pgfOuterSep)),
    ("the title sets at its slot's declared size",
      lineSizeOf c 0 "A Placeholder Deck" == some (Dim.pt 18)),
    ("the author's slot is pinned above the page foot, not under the title",
      ((lineYOf c 0 "P. Placeholder").map fun y =>
        decide (y ≤ geom.pageH - Dim.mm 14 ∧ y ≥ geom.pageH - Dim.mm 14 - Dim.pt 14)).getD false),
    ("the institute stands in the foot's other corner, right of the middle",
      ((lineXOf c 0 "example.org").map fun x => decide (x > geom.pageW / 2)).getD false &&
        ((lineYOf c 0 "example.org").map fun y =>
          decide (y ≤ geom.pageH - Dim.mm 14 ∧ y ≥ geom.pageH - Dim.mm 14 - Dim.pt 14)).getD false),
    ("a title page with slots ships no lineage separator",
      (c[0]?.map (·.rules)) == some 0)]),
  ("titlebars", fun geom c =>
    let bars := pageRuleSegs c 0
    let titleY := (lineYOf c 0 "Bars Probe Title").getD 0
    [("one page", c.size == 1),
     ("the styled built-in ships the title", hasStr (censusText c) "Bars Probe Title"),
     ("the author ships under it", hasStr (censusText c) "An Invented Author"),
     ("the body text ships after the title block",
       hasStr (censusText c) "Body text follows the styled built-in title."),
     -- 3 pt and 2 pt are the fixture's own numbers: no engine default —
     -- TeX's 0.4 pt \hrule, the 0.5 pt separator, the 0.06 em heading
     -- rule, the booktabs weights — can produce them, so these bars come
     -- from the refused body or the fact fails.
     ("two bars ship at the body's declared weights",
       bars.map (·.2) == #[Dim.pt 3, Dim.pt 2]),
     ("the top bar stands above the title line, the bottom below",
       (bars.map fun s => decide (s.1 < titleY)) == #[true, false]),
     -- The gaps beside the bars are the engine's rhythm, not the venue's
     -- \vskips (the fixture's 0.5in/0.75in are deliberately unread): three
     -- quanta from the bar to the type's body — the cap line above the
     -- title, so the band over the exact gap is under one \Large cap —
     -- and the baseline below it, where the bottom bar lands exactly.
     ("the top bar stands three quanta above the title's cap line",
       (bars[0]?.map fun s => decide (3 * Ir.rhythmQuantum geom.fontSize ≤ titleY - s.1 ∧
         titleY - s.1 ≤ 3 * Ir.rhythmQuantum geom.fontSize + geom.fontSize * 1440 / 1000)).getD false),
     ("the bottom bar stands exactly three quanta below the title's baseline",
       (bars[1]?.map fun s => decide (s.1 - titleY ==
         3 * Ir.rhythmQuantum geom.fontSize + Dim.pt 2)).getD false),
     ("the title is centred in the measure",
       ((lineXOf c 0 "Bars Probe Title").map fun x =>
         decide (x > geom.hmargin)).getD false),
     -- \Large is the body's declaration; the engine's own default is the
     -- scale's LARGE step, so a default-styled title fails this fact.
     ("the title sets at the body's declared \\Large, not the LARGE default",
       lineSizeOf c 0 "Bars Probe Title" ==
         some (geom.fontSize * 1440 / 1000)),
     -- The author line's 2u strut (`Ir.titleAuthorStrut`): its baseline
     -- stands the strut's 24pt plus the engine's one-quantum bar skip
     -- under the bottom bar (the venue's 0.1in is unread); unstrutted,
     -- the skip plus a bare cap height (under 14pt) never reaches the
     -- floor.
     ("the author line carries its 2u strut under the bottom bar",
       ((pageRuleSegs c 0)[1]?.map fun s =>
         let d := (lineYOf c 0 "An Invented Author").getD 0 - s.1
         decide (Dim.pt 24 + Ir.rhythmQuantum geom.fontSize ≤ d ∧
           d ≤ Dim.pt 24 + Ir.rhythmQuantum geom.fontSize + 2 * geom.fontSize)).getD false),
     -- The rhythm gap after the block (`Ir.titleBlockAfter`, 2u at the
     -- body size): the body text stands the gap plus its interline under
     -- the author line; without the gap the default (parskip + leading,
     -- under 20pt) never reaches the floor.
     ("the 2u gap after the title block stands before the body text",
       let d := (lineYOf c 0 "Body text follows").getD 0 -
         (lineYOf c 0 "An Invented Author").getD 0
       decide (Dim.pt 36 ≤ d ∧ d ≤ Dim.pt 36 + 3 * geom.fontSize))]),
  ("fonts", fun _ c => [
    ("one page", c.size == 1),
    ("the heading ships", hasStr (censusText c) "Faces"),
    ("the body claim ships", hasStr (censusText c) "Body text is set in the serif family")]),
  ("palette", fun _ c => [
    ("one page", c.size == 1),
    ("the coloured heading ships", hasStr (censusText c) "A coloured heading")]),
  ("tokens", fun _ c => [
    ("one page", c.size == 1),
    ("the heading ships", hasStr (censusText c) "Declared spacing")]),
  ("fill", fun _ c => [
    ("one page", c.size == 1),
    ("hfill sets both edges on one line",
      ((c[0]?.bind fun p => p.lines.find? fun l => hasStr l.text "Left edge").map
        fun l => hasStr l.text "right edge").getD false)]),
  ("links", fun _ c => [
    ("one page", c.size == 1),
    ("the running foot resolves page number and count", hasStr (censusText c) "page 1 of 1"),
    ("link underlines ship as rules", (c[0]?.map fun p => decide (p.rules ≥ 1)).getD false)])]

def censusRows2 :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  ("resume", fun _ c => [
    ("one page", c.size == 1),
    ("the name ships", hasStr (censusText c) "Alex Doe"),
    ("the contact line ships", hasStr (censusText c) "alex@example.org")]),
  ("resume-data", fun _ c => [
    ("one page", c.size == 1),
    ("the first record's company ships", hasStr (censusText c) "Example Corp"),
    ("the record without an end ships the else branch",
      hasStr (censusText c) "2021–present"),
    ("a bounded record ships both years", hasStr (censusText c) "2017–2021"),
    ("an achievements item ships with a marker",
      hasStr (censusText c) "• Measured the widgets"),
    ("the tie inside a value holds its words on one line",
      (c[0]?.map fun p => p.lines.any fun l =>
        hasStr l.text "widget" && hasStr l.text "pipeline,").getD false),
    ("the records ship in file order",
      ((censusText c).splitOn "Example Corp").length > 1 &&
        hasStr (((censusText c).splitOn "Example Corp").getLast? |>.getD "")
          "Widgets Ltd")]),
  ("talk", fun _ c => [
    ("a page per overlay step plus one per remaining frame", c.size == 6),
    ("the first step page dims the pending lines in place",
      pageCovered c 0 "Metrics are queryable"),
    ("the dimmed text still ships", pageHas c 0 "Metrics are queryable"),
    ("the final step page has nothing covered", pageAllRevealed c 2)]),
  ("deck", fun _ c => [
    ("a page per frame, divider, and step", c.size == 8),
    ("the title frame ships the title", pageHas c 0 "A Certified Deck"),
    ("the standout frame fills its background", (c[7]?.map (·.fills == 1)).getD false),
    ("the standout content ships", pageHas c 7 "Questions?")]),
  ("tables-deck", fun _ c => [
    ("the title page, then a page per step of the table frame: no continuation page",
      c.size == 3 && pageHas c 0 "An Invented Table Deck"),
    ("the table frame's first page ships its head, first and last row",
      pageHas c 1 "Count" && pageHas c 1 "A placeholder row with a longer label" &&
        pageHas c 1 "Last row"),
    ("the text column's cells start at one left edge under the centred scope",
      (lineXOf c 1 "Short label").isSome &&
        lineXOf c 1 "Short label" == lineXOf c 1 "A placeholder row with a longer label"),
    ("the count column's cells end at one right edge",
      (lineRightOf c 1 "1,204").isSome && lineRightOf c 1 "1,204" == lineRightOf c 1 "2,274"),
    ("the later columns ship covered on the first step and revealed on the second",
      pageCovered c 1 "15.97" && pageHas c 2 "15.97" && pageAllRevealed c 2)]),
  ("deck1610", fun geom c => [
    ("one page, the frame", c.size == 1),
    -- The stage a class option declares is the stage the pages ship on:
    -- aspectratio=1610 is beamer's 160×100 mm row (user guide §8.1),
    -- selected through Ir.slidesStages, never a string match.
    ("the pages ship on the declared 16:10 stage",
      geom.pageW == Dim.mm 160 && geom.pageH == Dim.mm 100),
    ("the frame title ships", pageHas c 0 "One declared key"),
    ("the frame body ships", pageHas c 0 "160 by 100 millimetres")]),
  ("themed", fun geom c => [
    ("pages", c.size == 8),
    ("the section page carries its progress-bar fills", (c[1]?.map fun p => decide (p.fills ≥ 2)).getD false),
    ("the frame-title bar fills", (c[2]?.map fun p => decide (p.fills ≥ 1)).getD false),
    -- moloch's frametitle box, on the page: the bar is a full-width fill
    -- from the page top, exactly `2·pad + strut` tall at the bundle's
    -- `\large` title step (`Layout.frameBar_exact`; the pad is the
    -- lineage's `frametitlepadding` token resolved at the title size,
    -- `Ir.frameTitlePadding_exact`) — never the body's vmargin plus a
    -- half-body pad, which was 1.5× the reference.
    ("the frame-title bar is moloch's box: 2·pad + strut at the title step",
      let titleSize := Ir.scaleStep geom.fontSize "large"
      let pad := Ir.frameTitlePadding.width.resolve titleSize 0
      let strut := Ir.frameTitleStrut titleSize
      let h := Layout.frameBarHeight pad (pad + strut) 0
      (c[2]?.map fun p => p.fillRects.any fun (x, y, w, fh) =>
        x == 0 && y == 0 && w == geom.pageW && fh == h).getD false),
    ("the frame title's baseline stands one pad and one strut below the page top",
      let titleSize := Ir.scaleStep geom.fontSize "large"
      lineYOf c 2 "A theme is data" ==
        some (Ir.frameTitlePadding.width.resolve titleSize 0 + Ir.frameTitleStrut titleSize)),
    ("the covered step dims the alert and example beats in place",
      pageCovered c 3 "alert beat" && pageCovered c 3 "teal example beat"),
    ("the covered beats still ship", pageHas c 3 "alert beat"),
    ("the second step reveals them", pageAllRevealed c 4),
    -- The census form of "every frame page carries its title bar unless
    -- plain/standout": the tall frame spills, and its continuation page
    -- repeats the title line and the bar fill (page bg + bar ≥ 2 fills),
    -- exactly as beamer keeps the frametitle on every page of a frame.
    ("the tall frame spills onto a continuation page",
      pageHas c 5 "Overflow beat one" && pageHas c 6 "eighteen"),
    ("every page of the frame carries its title",
      pageHas c 5 "A frame that continues" && pageHas c 6 "A frame that continues"),
    ("the continuation page repeats the title bar",
      (c[6]?.map fun p => decide (p.fills ≥ 2)).getD false),
    ("the continuation body sets below the repeated title, never over it",
      ((lineYOf c 6 "A frame that continues").bind fun ty =>
        (lineYOf c 6 "eighteen").map fun by' => decide (by' > ty)).getD false),
    ("the standout frame fills its background", (c[7]?.map fun p => decide (p.fills ≥ 1)).getD false)]),
  ("daylight", fun _ c => [
    ("pages", c.size == 4),
    -- The default bundle declares a page colour: every page paints.
    ("every page paints the warm paper", c.all fun p => decide (p.fills ≥ 1)),
    -- Variant A: no frame-title bar — the frame page carries the page
    -- fill and nothing else behind its title.
    ("the frame page carries no title bar", (c[2]?.map (·.fills == 1)).getD false),
    ("the frame title ships as a plain heading", pageHas c 2 "A default bundle"),
    ("the section page draws its progress track",
      (c[1]?.map fun p => decide (p.fills ≥ 2)).getD false),
    ("the standout page fills its azure room", (c[3]?.map fun p => decide (p.fills ≥ 1)).getD false),
    ("the accent beats ship", pageHas c 2 "azure emphasis" && pageHas c 2 "green example")]),
  ("latex-idioms", fun _ c => [
    ("one page", c.size == 1),
    ("the running head ships", hasStr (censusText c) "Alex Doe"),
    ("the section rules draw", c.any fun p => decide (p.rules ≥ 1)),
    ("thispagestyle empty keeps the opening page bare of the page number",
      (c[0]?.map fun p => p.lines.all (·.text.trimAscii.toString != "1")).getD false),
    -- The hand-aligned pair, through the whole driver: a phantom props a
    -- descender-less word's depth so it shares its neighbour's baseline. The
    -- argument is sizing, never ink — this fixture is the corpus's witness
    -- that no page ships it.
    ("the hand-aligned pair ships both its words",
      hasStr (censusText c) "Awards" && hasStr (censusText c) "Judged"),
    ("and the phantom's argument reaches no page",
      !hasStr (censusText c) "qy")]),
  ("headroom", fun geom c => [
    ("one page", c.size == 1),
    ("the head ships with its page number", hasStr (censusText c) "Invented Field Notes"),
    ("the body ships under it", hasStr (censusText c) "reserves a band below the margin"),
    ("the head keeps its own line: no body text beside it",
      ((c[0]?.bind fun p => p.lines.find? fun l => hasStr l.text "Invented Field Notes").map
        fun l => !hasStr l.text "tight margin").getD false),
    ("body lines sit at the margin, not in the band",
      lineXOf c 0 "The running head above this page" == some geom.hmargin)]),
  ("wrapper", fun _ c => [
    ("both wrapper halves ship around the body",
      hasStr (censusText c) "First: body one (end First)"),
    ("the renewed environment ships its new half", hasStr (censusText c) "Aside. body two")]),
  ("centering", fun geom c => [
    ("the lead line sits at the margin",
      lineXOf c 0 "Left-aligned lead." == some geom.hmargin),
    ("the centred line sits past the margin",
      (lineXOf c 0 "One centred line.").any fun x => decide (x > geom.hmargin)),
    ("the standout line is centred",
      (lineXOf c 1 "Questions?").any fun x => decide (x > geom.hmargin))])]

def censusRows3 :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  ("columns", fun geom c => [
    ("three frames, three pages", c.size == 3),
    ("the narrow column sets right of the wide one",
      (lineXOf c 0 "A narrow aside.").any fun x => decide (x > geom.hmargin)),
    ("both equal shares ship", pageHas c 1 "left half" && pageHas c 1 "right half"),
    -- The command form: three `\column`s in one body ship as three
    -- side-by-side columns, level at the top (`[T]`), never stacked.
    ("the three command-form columns stand side by side",
      ((lineXOf c 2 "First third").bind fun x1 =>
        (lineXOf c 2 "Second third").bind fun x2 =>
          (lineXOf c 2 "Third third").map fun x3 =>
            decide (x1 < x2 && x2 < x3)).getD false),
    ("the three command-form columns share their top line",
      ((lineYOf c 2 "First third").bind fun y1 =>
        (lineYOf c 2 "Second third").bind fun y2 =>
          (lineYOf c 2 "Third third").map fun y3 =>
            decide (y1 == y2 && y2 == y3)).getD false)]),
  ("overlays-blocks", fun _ c => [
    ("a page per step across all frames", c.size == 12),
    ("a list revealed whole is covered whole",
      pageCovered c 0 "Placeholder point one." && pageCovered c 0 "Placeholder point two."),
    ("the covered list still ships its markers", pageHas c 0 "• Placeholder point one."),
    ("alt inks its first beat alone on the first step",
      pageOccurs c 9 "The first beat." == 1 && !pageHas c 9 "The second beat."),
    ("alt replaces it with the second beat on the later step",
      pageOccurs c 10 "The second beat." == 1 && !pageHas c 10 "The first beat."),
    ("an alternative is inked at full colour, never covered",
      !pageCovered c 9 "The first beat." && !pageCovered c 10 "The second beat."),
    ("a pause inside a column dims below it", pageCovered c 7 "Below the pause.")]),
  ("chrome", fun geom c => [
    ("pages", c.size == 5),
    -- The title page is `\frame[plain,noframenumbering]` (moloch): no chrome,
    -- and it does not advance the count — so the first content frame is 1, not
    -- 2, and nothing on page 1 carries the section title or a number.
    ("the title page carries no footer",
      !pageHas c 0 "Footers" &&
        ((c[0]?.map fun p => p.lines.all (·.text != "1")).getD false)),
    ("numbering starts at the first countable frame",
      pageHas c 2 "Footers" && lineRightOf c 2 "1" == some (geom.pageW - Ir.footline.right)),
    ("a framefoot note takes the left slot", pageHas c 3 "source: example.org/data"),
    ("the default footer returns when the wrapper ends",
      pageHas c 4 "Footers" && lineRightOf c 4 "3" == some (geom.pageW - Ir.footline.right))]),
  -- The footline's slots have fixed positions (FINDINGS F5 correction): a
  -- slot's box is a function of the declared layout and the paper's edge
  -- alone (`Layout.bandSlotX`, moloch's insets), so the number holds the
  -- right edge whatever the left slot holds — an empty left slot is not a
  -- case.
  ("footer-left", fun geom c => [
    ("pages", c.size == 4),
    ("the sectionless frame still numbers at the right edge",
      lineRightOf c 1 "1" == some (geom.pageW - Ir.footline.right)),
    ("the number is a line of its own, whole and unmoved",
      ((c[1]?.bind fun p => p.lines.find? fun l => hasStr l.text "1").map
        fun l => l.text == "1").getD false),
    ("the section title takes the left slot flush left",
      lineXOf c 3 "Placement" == some Ir.footline.left),
    ("the sectioned frame numbers at the same right edge",
      lineRightOf c 3 "2" == some (geom.pageW - Ir.footline.right))]),
  -- FINDINGS F4: the two sequences share a band only by declaration. The
  -- stepped frame is where they visibly disagree: its pages advance the
  -- physical number and hold the frame number — one counter could never
  -- ship these pages.
  ("footer-mixed", fun _ c => [
    ("pages", c.size == 5),
    ("the step pages advance the physical number",
      pageHas c 2 "p. 3" && pageHas c 3 "p. 4"),
    ("and hold the frame number across the step",
      (lineRightOf c 2 "p. 3").isSome && pageHas c 2 "1" && pageHas c 3 "1"),
    ("the plain frame carries the next of both",
      pageHas c 4 "p. 5" && pageHas c 4 "2")]),
  -- The F5 correction's collision half: the boxes overlap and the number —
  -- lower priority — yields IN PLACE: still at its right inset, painted
  -- first so the note paints over it. The yield's diagnostic (W0333) and
  -- the paint order are asserted in bandChecks; the census states the
  -- boxes.
  ("footer-collide", fun geom c => [
    ("pages", c.size == 2),
    ("the number still ends at its right inset",
      lineRightOf c 1 "1" == some (geom.pageW - Ir.footline.right)),
    ("the overlong note still ships flush left",
      lineXOf c 1 "0123456789" == some Ir.footline.left)]),
  ("lists", fun _ c => [
    ("one page", c.size == 1),
    ("four itemize levels ship their four marks",
      ["• Outer point one", "– Second level", "* Third level", "· Fourth level"].all
        fun m => hasStr (censusText c) m),
    ("enumerate marks per level", ["1. First", "(a) Nested resets to one",
      "i. Third level", "A. Fourth level"].all fun m => hasStr (censusText c) m),
    ("the enclosing counter resumes", hasStr (censusText c) "3. Third")]),
  ("lists-styled", fun _ c => [
    ("one page", c.size == 1),
    ("the base override ships", hasStr (censusText c) "– The base override"),
    ("the level override ships", hasStr (censusText c) "• The level override")]),
  -- The two marker fixtures carry FINDINGS F1: a declared marker either
  -- reaches a backend as declared or the substitution has a name (W0331).
  -- The PDF side is judged here; the HTML side and the agreement between
  -- them are judged in agreeChecks.
  ("marker-styled", fun _ c => [
    ("one page", c.size == 1),
    ("the declared en-dash marker ships beside each item",
      pageHas c 0 "– First invented point" && pageHas c 0 "– Second invented point")]),
  ("marker-content", fun _ c => [
    ("one page", c.size == 1),
    ("the items ship", pageHas c 0 "An item marked by a picture"),
    ("no default text marker substitutes for the image",
      !pageHas c 0 "• An item" && !pageHas c 0 "– An item")]),
  ("lists-deck", fun _ c => [
    ("pages", c.size == 4),
    ("nesting shows through the theme", pageHas c 1 "– Nested under the stepped item"),
    ("ordered marks on a slide", pageHas c 3 "1. First placeholder")])]

def censusRows4 :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  -- the census carries x and text, not y; the [t]/[c]/[b] geometry itself
  -- is pinned by vdistChecks over Layout.LineOut
  ("valign", fun _ c => [
    ("five frames, the overflow spilling once", c.size == 6),
    ("each declared frame ships its body",
      pageHas c 0 "A short body sits midway" && pageHas c 1 "This body hugs its title"
        && pageHas c 2 "This body sits on the bottom margin"),
    ("the spill page carries the overflow", pageHas c 5 "resolved to enumerate")]),
  ("images", fun _ c => [
    ("one page", c.size == 1),
    ("the sentence around the inline image ships",
      hasStr (censusText c) "sits in the line"),
    ("the figure caption ships with its number", hasStr (censusText c) "Figure 1: Three rectangles, fitted")]),
  ("figures", fun _ c => [
    ("one page", c.size == 1),
    ("the prose around the embedded PDF ships",
      hasStr (censusText c) "Before the figure"),
    ("the inline sentence ships around its embedded page",
      hasStr (censusText c) "And extensionless")]),
  ("webpage", fun _ c => [
    ("one page", c.size == 1),
    ("the name ships", hasStr (censusText c) "Doe"),
    ("the section headings ship",
      hasStr (censusText c) "Experience" && hasStr (censusText c) "Education")]),
  ("webnav", fun _ c => [
    ("one page", c.size == 1),
    ("the shared content ships", hasStr (censusText c) "appears on every surface"),
    ("the print-only conditional ships on the page",
      hasStr (censusText c) "This sentence is set only on the printed page."),
    ("the unwrapped menu nav ships no body ink",
      !hasStr (censusText c) "Back to top")]),
  ("nav-directory", fun _ c => [
    ("one page", c.size == 1),
    ("the title, its author line and the paragraph ship",
      hasStr (censusText c) "An Invented Directory" && hasStr (censusText c) "Alex Doe" &&
        hasStr (censusText c) "An invented page"),
    ("the three-hundred-entry menu ships no body ink: it is the outline",
      !hasStr (censusText c) "Entry")]),
  ("icons", fun _ c => [
    ("one page", c.size == 1),
    ("the contact words ship", hasStr (censusText c) "Email"),
    ("the icon glyphs ship as ink",
      hasStr (censusText c) "\uF09B" && hasStr (censusText c) "\uF0E0" &&
      hasStr (censusText c) "\uF08C" && hasStr (censusText c) "\uF19D" &&
      hasStr (censusText c) "\uF062")]),
  ("diagram", fun geom c => [
    ("one page", c.size == 1),
    ("the 4×4 grid ships its sixteen fills",
      (c[0]?.map (·.fills == 16)).getD false),
    ("every diagonal label ships",
      ["aa", "bb", "cc", "dd"].all fun l => hasStr (censusText c) l),
    ("the labels step up the diagonal",
      (((lineXOf c 0 "aa").bind fun xa => (lineXOf c 0 "dd").map fun xd =>
        decide (xa < xd)).getD false)),
    ("the centred picture stands past the margin",
      ((lineXOf c 0 "aa").map fun x => decide (x > geom.hmargin)).getD false),
    ("the prose around the diagram ships",
      hasStr (censusText c) "Before the diagram" &&
        hasStr (censusText c) "After the diagram")]),
  ("diagram-overflow", fun _ c => [
    ("one page", c.size == 1),
    ("the band ships as a fill", (c[0]?.map (·.fills == 1)).getD false),
    ("its label ships", hasStr (censusText c) "wide band")]),
  ("diagram-boundary", fun _ c => [
    ("one page", c.size == 1),
    ("the boundary request ships as one image box where the picture stood",
      (c[0]?.map (·.images == 1)).getD false),
    ("the prose around the requested picture ships",
      hasStr (censusText c) "routes to the" &&
        hasStr (censusText c) "Text follows the requested picture")]),
  ("diagram-refused", fun _ c => [    ("one page", c.size == 1),
    ("the placeholder outline ships as four fills",
      (c[0]?.map (·.fills == 4)).getD false),
    ("the diagnostic code ships inside the box", hasStr (censusText c) "W0362"),
    ("the prose around the placeholder ships",
      hasStr (censusText c) "constructs outside the rendered subset" &&
        hasStr (censusText c) "Text resumes after the placeholder")]),
  ("diagram-scm", fun _ c => [
    ("one page", c.size == 1),
    -- three outlines + four edges + one arrow-tip triangle
    ("the node outlines, edges, and tip ship as page paths",
      (c[0]?.map (·.paths == 8)).getD false),
    ("the text node body ships", hasStr (censusText c) "out"),
    ("the curve's mid-path label ships", hasStr (censusText c) "lift"),
    -- A label's alphabet resolves as a paragraph's: upright letters, never
    -- the source italic an unresolved alphabet node set (𝑟𝑑).
    ("the alphabet edge label ships upright",
      hasStr (censusText c) "rd" && !hasStr (censusText c) "𝑟𝑑"),
    ("every node ships a glyph line",
      (c[0]?.map fun p => decide (p.lines.size ≥ 3)).getD false)])]

def censusRows5 :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  -- **A style reaches its picture wherever it was declared.** `ball` comes
  -- from the preamble, `slab` from a `\tikzset` beside the picture inside
  -- the document body; both are applied by name, and their keys are what
  -- draws the outlines this row counts. Before the native reading, the
  -- style names were keys outside the subset (W0334) and the nodes shipped
  -- bare labels: three fewer paths on the page, and the fixture's own
  -- declaration silently doing nothing. `images == 0` is the other half of
  -- the claim — the ink is the engine's own, with no tool asked to draw.
  -- The second picture carries `wire` on its own bracket, which is the
  -- inheritance half: see the stroke rows below.
  ("diagram-tikzset", fun _ c => [
    ("one page", c.size == 1),
    -- two circle outlines + one rectangle outline + one edge, then the
    -- second picture's two inheriting edges
    ("the styled node outlines and the edges ship as page paths",
      (c[0]?.map (·.paths == 6)).getD false),
    ("no boundary box stands where the picture is",
      (c[0]?.map (·.images == 0)).getD false),
    -- **A style applied to the picture reaches the picture's contents, and
    -- the inner setting wins.** `wire` sets a stroke colour and `thick` on
    -- the second picture; its first edge declares nothing of its own and
    -- must ship both, its second re-declares the colour and must ship its
    -- own there and the picture's width still. Before picture-level keys,
    -- `wire` was a key outside the subset and both edges shipped thin and
    -- black. Read off the shipped strokes, because only the page can say
    -- which value survived.
    ("the edge that declared nothing inherits the picture's colour and width",
      ((c[0]?.bind (·.pathStrokes[4]?)).map fun (col, w) =>
        col == { r := 0, g := 0, b := 255 } && w == Ir.Pic.thickWidth).getD false),
    ("the edge that re-declared the colour keeps its own, and the picture's width",
      ((c[0]?.bind (·.pathStrokes[5]?)).map fun (col, w) =>
        col == { r := 255, g := 0, b := 0 } && w == Ir.Pic.thickWidth).getD false),
    ("every styled node's body ships",
      hasStr (censusText c) "P" && hasStr (censusText c) "Q" &&
        hasStr (censusText c) "out"),
    ("the prose around the diagram ships",
      hasStr (censusText c) "Before the diagram" &&
        hasStr (censusText c) "After the diagram")]),
  ("tables", fun geom c => [
    ("one page", c.size == 1),
    ("the header row ships", hasStr (censusText c) "Construct"
      && hasStr (censusText c) "Meaning"),
    ("every body cell ships", hasStr (censusText c) "invented row"
      && hasStr (censusText c) "alpha" && hasStr (censusText c) "beta"),
    ("both table captions ship, each with its number in front",
      hasStr (censusText c) "Table 1: A booktabs table with declared spacing."
        && hasStr (censusText c) "Table 2: The caption above: the table convention."),
    ("the figure caption ships, numbered on its own counter",
      hasStr (censusText c) "Figure 1: A figure’s caption, bound below what it captions."),
    -- top + mid + bottom, then top + cmid + bottom: six drawn rules.
    ("the booktabs rules draw", ((c[0]?.map (·.rules)).getD 0) == 6),
    ("cells sit in their declared columns: the second column right of the first",
      ((lineXOf c 0 "Construct").bind fun a =>
        (lineXOf c 0 "Meaning").map fun b => decide (a < b)).getD false),
    ("the floated table centres: its first cell sits past the margin",
      (lineXOf c 0 "invented row").any fun x => decide (x > geom.hmargin)),
    -- a `\multicolumn` head: one line, standing over the columns it covers,
    -- right of the first column's cell
    ("the spanned head ships once, right of the first column",
      pageOccurs c 0 "a spanned head" == 1 &&
      ((lineXOf c 0 "a spanned head").bind fun h =>
        (lineXOf c 0 "left").map fun l => decide (h > l)).getD false)]),
  ("tables-ragged", fun _ c => [
    ("one page", c.size == 1),
    ("every declared cell ships, the ragged row's included",
      hasStr (censusText c) "alpha" && hasStr (censusText c) "gamma"
        && hasStr (censusText c) "delta" && hasStr (censusText c) "epsilon"),
    ("the rules draw", ((c[0]?.map (·.rules)).getD 0) == 2)]),
  ("subfigures", fun _ c => [
    ("one page", c.size == 1),
    ("both panels ship their diagram labels",
      hasStr (censusText c) "left box" && hasStr (censusText c) "right box"),
    ("the lettered subcaptions ship",
      hasStr (censusText c) "(a) The first invented panel."
        && hasStr (censusText c) "(b) The second invented panel."),
    ("the parent caption ships its figure number",
      hasStr (censusText c) "Figure 1: Two invented panels side by side."),
    ("the second figure keeps the document-order counter",
      hasStr (censusText c) "Figure 2: The plain figure, numbered second."),
    ("the panels stand side by side: the right label right of the left",
      ((lineXOf c 0 "left box").bind fun xl => (lineXOf c 0 "right box").map
        fun xr => decide (xl < xr)).getD false)]),
  ("box-sides", fun geom c =>
    let near (a b : Dim.Sp) : Bool := decide ((a - b).natAbs ≤ (Dim.pt 1).natAbs)
    let right := geom.hmargin + geom.textWidth
    [("one page", c.size == 1),
     ("the document title stands centred in the measure",
       ((lineXOf c 0 "An Invented Box Study").bind fun x =>
         (lineRightOf c 0 "An Invented Box Study").map fun r =>
           near (x - geom.hmargin) (right - r)).getD false),
     ("the tabular title stands centred in the measure",
       ((lineXOf c 0 "An Invented Tabular Title").bind fun x =>
         (lineRightOf c 0 "An Invented Tabular Title").map fun r =>
           near (x - geom.hmargin) (right - r)).getD false),
     ("the lone minipage stands centred, a quarter of the measure each side",
       ((lineXOf c 0 "An invented lone minipage").map
         (near · (geom.hmargin + geom.textWidth / 4))).getD false),
     ("the parbox stands centred, three tenths of the measure each side",
       ((lineXOf c 0 "An invented parbox").map
         (near · (geom.hmargin + geom.textWidth * 3 / 10))).getD false),
     ("the right-set table ends a tabcolsep before the measure's right edge",
       ((lineRightOf c 0 "second row").map (near · (right - Dim.pt 6))).getD false)]),
  ("float-center", fun _ c => [
    ("one page", c.size == 1),
    ("the figure caption ships with its number",
      hasStr (censusText c) "Figure 1: An invented centred panel."),
    ("the grouped body ships as float content",
      hasStr (censusText c) "An invented stand-in for a centred panel body."),
    ("the table caption ships with its number after its tabular",
      hasStr (censusText c) "Table 1: An invented centred strip."),
    ("the tabular content ships",
      hasStr (censusText c) "alpha" && hasStr (censusText c) "delta"),
    ("the references resolve to the numbers the captions carry",
      hasStr (censusText c) "Figure1 and Table1 are referenced")]),
  ("math", fun _ c => [
    ("one page", c.size == 1),
    ("prose around the display ships",
      hasStr (censusText c) "The paragraph continues after the display"),
    ("the display-size sum ships as a glyph", hasStr (censusText c) "∑"),
    ("an align row ships aligned glyphs", hasStr (censusText c) "=(𝑥−1)(𝑥+1)"),
    ("every fraction bar, overbar, and overline ships as a rule",
      ((c[0]?.map (·.rules)).getD 0) == 10),
    ("the accent marks ship as glyphs",
      hasStr (censusText c) "\u0302" && hasStr (censusText c) "\u20D7"),
    ("the out-of-scope construct degrades to its text content, never its markup",
      hasStr (censusText c) "?=" && !hasStr (censusText c) "overset"),
    ("\\mathbb takes its Letterlike scalars", hasStr (censusText c) "ℝ"
      && hasStr (censusText c) "ℂ"),
    ("the bold alphabet ships, boldsymbol keeps the variable italic",
      hasStr (censusText c) "v" && !hasStr (censusText c) "𝐯"
        && hasStr (censusText c) "𝛽"),
    ("\\mathrm sets upright", hasStr (censusText c) "Err"),
    ("a document macro's expansion ships",
      hasStr (censusText c) "w" && !hasStr (censusText c) "𝐰"),
    ("a word stands as a script's argument", hasStr (censusText c) "null")]),
  -- Colour and text in math; a font change inside one word still names
  -- its loss. cancelReportChecks holds the shipped colours and scope.
  ("math-text", fun _ c => [
    ("one page", c.size == 1),
    ("\\textbf and \\textit ship the alphabets \\mathbf and \\mathit mean",
      !hasStr (censusText c) "𝐮" && !hasStr (censusText c) "𝑣"
        && hasStr (censusText c) "u"),
    ("a coloured letter ships its glyph", hasStr (censusText c) "𝑤"),
    ("\\text sets its words upright",
      hasStr (censusText c) "gain" && hasStr (censusText c) "loss"),
    ("a brace group inside \\text is grouping alone",
      hasStr (censusText c) "abc"),
    ("a symbol inside \\text ships its scalar",
      hasStr (censusText c) "first…last"),
    ("the coloured styled alignment ships its operator and its word",
      hasStr (censusText c) "∑" && hasStr (censusText c) "bound above"),
    ("the unmodelled construct ships its content", hasStr (censusText c) "?="),
    ("no page of this fixture ships a control sequence",
      !hasStr (censusText c) "overset" && !hasStr (censusText c) "textcolor"
        && !hasStr (censusText c) "textbf")]),
  -- The text-sourced alphabets whose MathML projection rides on real CSS:
  -- the PDF ships the plain base letter set in a text family, never a
  -- Mathematical Alphanumeric scalar (which is the loss this projection
  -- avoids). The unstyled variables stay italic Alphanumeric, as always.
  ("math-alpha", fun _ c =>
    let has (n : Nat) := hasStr (censusText c) (String.ofList [Char.ofNat n])
    [
    ("one page", c.size == 1),
    ("the styled letters ship their plain base glyphs",
      hasStr (censusText c) "B" && hasStr (censusText c) "C"
        && hasStr (censusText c) "D" && hasStr (censusText c) "E"),
    ("a styled scalar never ships a Mathematical Alphanumeric codepoint",
      !has 0x1D401 && !has 0x1D436 && !has 0x1D5A3 && !has 0x1D674),
    ("a styled digit ships its digit", hasStr (censusText c) "7"),
    ("a nested styled scalar ships its letter in a script",
      hasStr (censusText c) "k"),
    ("the unstyled variables ship as italic Alphanumeric scalars",
      has 0x1D465 && has 0x1D466),
    ("no page of this fixture ships a control sequence",
      !hasStr (censusText c) "mathsf" && !hasStr (censusText c) "mathbf"
        && !hasStr (censusText c) "mathrm")]),
  ("math-cancel", fun _ c => [
    ("one page", c.size == 1),
    ("the document title ships", hasStr (censusText c) "Annotated Formulas"),
    ("the four commands ship their strikes and arrowheads",
      ((c[0]?.map (·.polys.size)).getD 0) == 8),
    ("both annotation values and the neighbouring superscripts ship",
      ["0", "7", "𝑥", "𝑦", "𝑧", "𝑤", "2"].all (hasStr (censusText c) ·)),
    ("the fraction still ships its bar", ((c[0]?.map (·.rules)).getD 0) > 0),
    ("no cancellation command reaches the page as markup",
      !hasStr (censusText c) "cancel" && !hasStr (censusText c) "textcolor")]),
  ("math-companion", fun _ c => [
    ("one page", c.size == 1),
    ("the inline formula ships italic math glyphs", hasStr (censusText c) "𝑥"),
    ("the display sum ships as a glyph", hasStr (censusText c) "∑"),
    ("the fraction bar ships as a rule", ((c[0]?.map (·.rules)).getD 0) == 1),
    ("prose after the display ships",
      hasStr (censusText c) "The paragraph continues after the display")])]

def censusRows6 :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  ("math-first", fun _ c => [
    ("one page", c.size == 1),
    ("the inline formula ships italic math glyphs", hasStr (censusText c) "𝑥"),
    ("the display fraction bar ships as a rule", ((c[0]?.map (·.rules)).getD 0) == 1)]),
  ("greek-literal", fun _ c => [
    ("one page", c.size == 1),
    ("lowercase literals ship the Mathematical Italic scalars",
      ["𝜆", "𝜃", "𝜑", "𝜀", "𝛼", "𝛽", "𝛾", "𝜔"].all (hasStr (censusText c))),
    ("the symbol slots ship their own scalars",
      hasStr (censusText c) "𝜖" && hasStr (censusText c) "𝜙"),
    ("capitals ship upright", hasStr (censusText c) "Ω" && hasStr (censusText c) "Φ"),
    ("no Greek letter ships as body-face source text",
      ["λ", "θ", "φ", "ε", "ϵ", "ϕ", "α", "β", "γ", "ω"].all fun g =>
        !hasStr (censusText c) g),
    ("the function name stays upright", hasStr (censusText c) "cos")]),
  ("quotes", fun geom c => [
    ("one page", c.size == 1),
    ("the quotation's text ships", hasStr (censusText c) "A short invented epigraph"),
    ("the quotation's second paragraph ships",
      hasStr (censusText c) "The second paragraph of the same quotation"),
    ("prose sits at the margin",
      lineXOf c 0 "A paragraph before the quotation" == some geom.hmargin),
    ("the quotation indents from the margin by \\leftmargini (classes.dtx: 2.5em)",
      lineXOf c 0 "A short invented epigraph"
        == some (geom.hmargin + geom.fontSize * 5 / 2))]),
  ("quote-deck", fun geom c => [
    ("one frame, one page", c.size == 1),
    ("the quotation ships on the slide",
      pageHas c 0 "Typesetting is invisible until it fails"),
    ("the slide's quotation indents from the margin",
      (lineXOf c 0 "Typesetting is invisible").any fun x =>
        decide (x == geom.hmargin + geom.fontSize * 2))]),
  ("outline", fun _ c => [
    ("one page", c.size == 1),
    ("the level-0 title ships as the title furniture",
      hasStr (censusText c) "An Invented Field Guide"),
    ("the author line ships under it", hasStr (censusText c) "Alex Doe"),
    ("every rung of the heading ladder ships",
      ["Habitats", "Wetlands", "Reed Beds", "Migration"].all
        fun h => hasStr (censusText c) h)]),
  ("outline-gap", fun _ c => [
    ("one page", c.size == 1),
    ("the diagnosed document still ships every heading",
      hasStr (censusText c) "Field Notes" &&
        hasStr (censusText c) "A Detail Too Deep")]),
  ("overlays", fun _ c => [
    ("one handout page per step", c.size == 5),
    ("step one dims the later beats in place",
      pageCovered c 0 "Second beat." && pageCovered c 0 "Third beat."),
    ("the dimmed beats still ship", pageHas c 0 "Second beat."),
    ("the last step reveals everything", pageAllRevealed c 2),
    ("pause dims what follows it", pageCovered c 3 "After the pause.")]),
  -- `{overprint}` is alternation, and alternation is replacement: the row
  -- that names the defect is the ABSENCE of the other readings on a step
  -- page, since keeping the body stacked all of them on every page and no
  -- page claim could tell. Covering is the other mechanism and stays out
  -- of it — nothing here is ever dimmed.
  ("overprint", fun _ c => [
    ("a page per step across the three frames: three, two, one", c.size == 6),
    ("the opening step inks its one reading and neither of the others",
      pageOccurs c 0 "The lone opening reading." == 1 &&
        !pageHas c 0 "A listed point on the middle step." &&
        !pageHas c 0 "The closing reading opens a paragraph."),
    ("an item holding a list steps whole, markers and all, alone on its step",
      pageHas c 1 "• A listed point on the middle step." &&
        pageHas c 1 "• A second listed point beside it." &&
        !pageHas c 1 "The lone opening reading."),
    ("an item holding two paragraphs ships both, on two baselines",
      pageHas c 2 "The closing reading opens a paragraph." &&
        pageHas c 2 "And ends on a second paragraph." &&
        ((lineYOf c 2 "opens a paragraph").bind fun y1 =>
          (lineYOf c 2 "second paragraph").map fun y2 => decide (y1 < y2)).getD false),
    ("content before the first item stands on every step of its frame",
      pageOccurs c 3 "Standing above every reading." == 1 &&
        pageOccurs c 4 "Standing above every reading." == 1),
    ("each later reading ships on its own step page only",
      pageOccurs c 3 "Shown on the opening step only." == 1 &&
        !pageHas c 3 "Shown on the later step only." &&
        pageOccurs c 4 "Shown on the later step only." == 1 &&
        !pageHas c 4 "Shown on the opening step only."),
    ("a reading is inked at full colour: an alternative is replaced, never dimmed",
      (List.range 6).all fun i => pageAllRevealed c i),
    ("the reading the rewrite refuses to number ships once, not several",
      pageOccurs c 5 "A reading kept as written." == 1),
    ("the readings are steps of one frame, not frames of their own: the \
frame number holds across each frame's step pages",
      (List.range 6).map (fun i =>
        (c[i]?.bind fun p => (p.lines.find? (·.furniture)).map (·.text)).getD "")
        == ["1", "1", "1", "2", "2", "3"])]),
  ("notes", fun _ c => [
    ("one page", c.size == 1),
    ("the note never ships on the handout", !hasStr (censusText c) "Say hello"),
    ("the paragraph flows on unbroken", hasStr (censusText c) "never breaks the flow")]),
  ("furniture", fun _ c => [
    ("pages", c.size == 6),
    ("the title ships", pageHas c 0 "Frame Furniture"),
    ("the centred line ships", hasStr (censusText c) "This line is centred."),
    ("the step page dims its pending beats", pageCovered c 3 "Second beat."),
    ("the narrow column ships", hasStr (censusText c) "The narrow column.")]),
  ("trio-page", fun _ c => [
    ("one page", c.size == 1),
    ("the studio name ships", hasStr (censusText c) "Cardamom Press"),
    ("the shared section style draws its rules", (c[0]?.map (·.rules == 2)).getD false)])]

def censusRows7 :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  ("trio-deck", fun _ c => [
    ("pages", c.size == 4),
    ("the title ships", pageHas c 0 "Cardamom Press"),
    ("the divider draws the section rule", (c[2]?.map (·.rules == 1)).getD false)]),
  ("trio-card", fun geom c => [
    ("two faces, two pages", c.size == 2),
    ("the front ships the name", pageHas c 0 "Pat Placeholder"),
    ("the back ships the contact", pageHas c 1 "press@example.org"),
    -- The declared cut marks, judged from the shipped fills: ink exactly
    -- on the eight marks and none in the gap or on the trim corner —
    -- the print-shop check, now the engine's.
    ("each face ships exactly the eight cut marks and no other fill",
      c.all fun p => p.fills == 8),
    ("every mark stands in the bleed strip: outside the trim, inside the medium",
      c.all fun p => p.fillRects.all fun r =>
        decide (-geom.bleed ≤ r.1 ∧ r.1 + r.2.2.1 ≤ geom.pageW + geom.bleed ∧
          -geom.bleed ≤ r.2.1 ∧ r.2.1 + r.2.2.2 ≤ geom.pageH + geom.bleed) &&
        decide (r.1 + r.2.2.1 ≤ 0 ∨ geom.pageW ≤ r.1 ∨
          r.2.1 + r.2.2.2 ≤ 0 ∨ geom.pageH ≤ r.2.1)),
    ("no mark ink within the declared gap of a trim corner",
      c.all fun p => p.fillRects.all fun r =>
        ([(0, 0), (geom.pageW, 0), (0, geom.pageH), (geom.pageW, geom.pageH)] :
            List (Dim.Sp × Dim.Sp)).all fun cc =>
          decide ¬(r.1 < cc.1 + geom.markGap ∧ cc.1 - geom.markGap < r.1 + r.2.2.1 ∧
            r.2.1 < cc.2 + geom.markGap ∧ cc.2 - geom.markGap < r.2.1 + r.2.2.2)),
    ("the marks are duplex-symmetric: the horizontal flip maps each onto a mark",
      c.all fun p => p.fillRects.all fun r =>
        p.fillRects.contains (geom.pageW - r.1 - r.2.2.1, r.2.1, r.2.2.1, r.2.2.2))]),
  ("lineno", linenoCensus),
  ("lineno-modulo", linenoModuloCensus),
  ("cond-newif", condBranchRow ["Setter branch ships.", "Initial branch ships."]
    ["Setter branch hidden.", "Initial branch hidden."]),
  ("cond-ifdefined", condBranchRow ["Defined branch ships.", "Absent branch ships."]
    ["Defined branch hidden.", "Absent branch hidden."]),
  ("cond-ifx", condBranchRow ["Equal branch ships.", "Unequal branch ships."]
    ["Equal branch hidden.", "Unequal branch hidden."]),
  ("cond-ifnum", condBranchRow ["Holding branch ships.", "Failing branch ships."]
    ["Holding branch hidden.", "Failing branch hidden."]),
  ("cond-loaded", condBranchRow ["Loaded branch ships.", "Unloaded branch ships."]
    ["Loaded branch hidden.", "Unloaded branch hidden."])]

/-- The census rows, in parts of at most `censusPartRows`: one list
literal's elaboration grows faster than its rows (all 86 as one literal
took 23 s, the eight parts together under 5 s), and the suite's build
waits on this module. A new row joins a part with room, or starts one. -/
def censusParts :
    List (List (String × (Layout.Geom → Array CensusPage → List (String × Bool)))) :=
  [censusRows0, censusRows1, censusRows2, censusRows3, censusRows4, censusRows5,
    censusRows6, censusRows7]

def censusPartRows : Nat := 16

def censusTable :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) :=
  censusParts.flatten

/-- The outline tier of the census: the PDF document outline is backend
emission (an unpinned nav's paged rendering, ISO 32000-2 §12.3.3), so a
fixture whose layout carries one owes the assertion that it appeared —
the same obligation every emission carries. `censusChecks` holds every
fixture with a non-empty outline to a row here. -/
def censusOutlineTable :
    List (String × (Array Layout.OutlineEntry → List (String × Bool))) := [
  ("webnav", fun o => [
    ("one entry per menu link, in order",
      o.map (·.title) == #["First Light", "Gathered Notes", "Back to top"]),
    ("the section targets resolve to the page their headings land on",
      (o.filter (·.title != "Back to top")).all (·.page == some 0)),
    ("the #top target stands bare: no heading anchors it",
      (o.find? (·.title == "Back to top")).map
        (fun e => e.page.isNone && e.url.isNone) == some true)]),
  ("nav-directory", fun o => [
    ("one entry per menu link, in order",
      o.map (·.title) == (Array.range 300).map fun i => s!"Entry {i + 1}"),
    ("every entry rides its own address, with no page",
      o.zipIdx.all fun (e, i) =>
        e.page.isNone && e.url == some s!"https://example.org/entries/{i + 1}")])]

/-- The phrase a corpus file writes in its own header to declare itself out
of the golden set: the convention PLAN records for a design sketch whose
commands do not exist yet. The declaration lives in the file it applies to,
not in a second list beside `goldenNames` — a list of exclusions here would
drift from the directory exactly the way `goldenNames` itself did. -/
def corpusExcludeMarker : String := "excluded from the golden set"

/-- Does this corpus file's header declare it out of the golden set? Only the
opening lines count, so a fixture whose body discusses the golden set does
not thereby excuse itself. The header is read as one run of prose — comment
markers dropped, lines joined — so the declaration may wrap the way a
sentence does. -/
def declaresExcluded (text : String) : Bool :=
  let header := ((text.splitOn "\n").take 16).map fun line =>
    let l := line.trimAscii.toString
    if l.startsWith "%" then (l.drop 1).toString.trimAscii.toString else l
  hasStr (" ".intercalate header) corpusExcludeMarker

/-- The corpus entries a golden run could draw from: the top-level `.tex` and
`.md` files under `testdata/corpus`. The subdirectories hold `\input` targets,
`.sty` files and the shipped fonts — never fixtures — so the scan does not
descend. `.md` is in scope because markdown is a shipped surface: a markdown
fixture dropped here must face the same question a `.tex` one does. -/
def corpusDocs : IO (Array String) := do
  let dir : System.FilePath := "testdata/corpus"
  let mut out := #[]
  for entry in (← dir.readDir).map (·.fileName) |>.qsort (· < ·) do
    unless entry.endsWith ".tex" || entry.endsWith ".md" do continue
    unless (← (dir / entry).isDir) do
      out := out.push entry
  return out

/-- The coverage loop's missing half: `goldenNames` against the corpus
directory. `censusChecks` holds the golden set and `censusTable` to each
other, which says nothing about what is on disk — so a fixture added to
`testdata/corpus` and forgotten from the list owed no golden and no census row,
and nothing noticed; two files sat in that state. The directory is the
authority for what exists, and whether a file is a fixture is a decision, so
the decision is written where it applies (`corpusExcludeMarker`) and both
directions are loud. A declared exclusion may not rot either: a `.tex` that
excuses itself must still refuse to elaborate, or the sketch's commands have
landed and it belongs in the golden set. -/
def corpusCoverageChecks (ref : IO.Ref (List String)) : IO Unit := do
  let dir : System.FilePath := "testdata/corpus"
  for entry in ← corpusDocs do
    let some stem := (System.FilePath.mk entry).fileStem | continue
    let listed := goldenNames.contains stem
    let text ← IO.FS.readFile (dir / entry)
    let excluded := declaresExcluded text
    check ref s!"corpus {entry}: in the directory but not in the golden set, \
and its header does not say why not"
      (listed || excluded)
    check ref s!"corpus {entry}: declares itself out of the golden set yet is listed in it"
      (!(listed && excluded))
    if excluded && !listed && entry.endsWith ".tex" then
      let (_, diags) ← elabFixture stem text
      check ref s!"corpus {entry}: excuses itself from the golden set but now \
elaborates without complaint — promote it"
        (diags.any fun d =>
          d.severity == .error || d.code == "W0301" || d.code == "W0302")
  for n in goldenNames do
    check ref s!"golden {n}: in the golden set but no testdata/corpus/{n}.tex"
      (← (dir / s!"{n}.tex").pathExists)

/-- The characters the ink watch bans, narrower than `Ir.markupChars` on
purpose. The floor filters `$`, `&`, `^`, `_` and `~` too, because in a
*math* source those are always markup; in ordinary prose they are content —
a price, an ampersand in a name — and the corpus ships one. A backslash or
a brace is the unambiguous signature of a page showing its source, and no
fixture ships one as content. -/
def inkMarkupWatch : List Char := ['\\', '{', '}']

/-- Fixtures allowed to ship a named markup character as ink, per
character, each with the reason it is content there. Per character and not
per fixture: `\{` is the author asking for a brace glyph and a formula that
uses it ships one legitimately, but that says nothing about a backslash on
the same page, and a whole-fixture exemption would have excused both.

Empty: nothing in the corpus renders one today. Adding a row is a
deliberate decision, visible in review; a recovery path that starts leaking
markup cannot quietly join it. -/
def inkMarkupExempt : List (String × List Char) := []

/-- The channel that watches the recovery floor on the artifact: no page of
any golden fixture ships a LaTeX markup character as ink. This is the
page-facing half of `Ir.floorInk_mem` — the IR states that a degraded
formula's ink is markup-free and drawn from its source or the declared
placeholder, and this reads the shipped glyph runs of every fixture to say
the page honours it. It is deliberately wider than math: any future
diagnostic whose recovery sets its own source as body text fails here, not
only where it was introduced. The corpus had exactly one offender when this
went in, the W0012 math recovery. -/
def inkMarkupChecks (ref : IO.Ref (List String)) (n : String)
    (c : Array CensusPage) : IO Unit := do
  let allowed := ((inkMarkupExempt.find? (·.1 == n)).map (·.2)).getD []
  let text := censusText c
  for ch in inkMarkupWatch do
    unless allowed.contains ch do
      check ref s!"census {n}: ships the markup character '{ch}' as ink"
        (!text.any (· == ch))

/-- The census tier: every golden fixture also appears in `censusTable`,
and each row's facts hold on the pages the engine actually ships. A
fixture that declares a math face renders its census with the shipped
Fira Math in the math slot — the assertions over fraction bars and grown
glyphs are exactly what `oneFace` alone could never witness. -/
def censusChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let mathSet ← mathSetOf oneFace
  for (part, i) in censusParts.zipIdx do
    check ref s!"census part {i} holds {part.length} rows, at most {censusPartRows}"
      (part.length ≤ censusPartRows)
  for n in goldenNames do
    check ref s!"census covers {n}" (censusTable.any (·.1 == n))
  for (n, _) in censusTable do
    check ref s!"census row {n} names a golden fixture" (goldenNames.contains n)
  -- A fixture that reaches math without declaring a face resolves it the
  -- way the driver does (FontDiscovery.pickMathFace over the shipped faces), so
  -- the census exercises the same decision a build runs.
  let shipped ← FontDiscovery.scanRoots [testFonts]
  for (n, facts) in censusTable do
    let src ← IO.FS.readFile s!"testdata/corpus/{n}.tex"
    let (doc, _) ← elabFixture n src
    let geom := Layout.Geom.ofPage doc.page
    let fs ← fixtureFontSet oneFace mathSet shipped doc
    let out := layoutOf fs doc geom (some pats)
    let c := censusOf (coveredColorsOf doc) out
    inkMarkupChecks ref n c
    for (label, ok) in facts geom c do
      check ref s!"census {n}: {label}" ok
    -- The outline tier: emission owes its appearance, so a fixture whose
    -- layout ships an outline must assert it, and the asserted facts hold.
    if !out.outline.isEmpty then
      check ref s!"census {n}: a shipped outline has its outline row"
        ((censusOutlineTable.lookup n).isSome)
    for (label, ok) in ((censusOutlineTable.lookup n).map (· out.outline)).getD [] do
      check ref s!"census {n} outline: {label}" ok


/-- The rendered half of `Ir.refs_agree_with_numbering`: the table's float
rows are read off the numbered IR (`Ir.floatLabelRows` — one numbering,
no predictor), and this check witnesses the wiring over every golden
fixture: a resolved reference to a key standing inside a captioned figure
or table shows exactly the number the numbered node carries. Keys inside
a nested subfloat are the nested float's own — their shipped form is the
subfigures census row — so `.sub` stays outside this watch. This is
IR-level agreement between resolution and the numbered nodes, not a page
claim; the page-facing halves live in censusTable's crossref and
subfigures rows. -/
def floatRefAgreementChecks (ref : IO.Ref (List String)) : IO Unit := do
  let labelsIn (body : Array Ir.Block) (caption : Array Ir.Inline) : Array String :=
    let fi := fun (out : Array String) (x : Ir.Inline) => match x with
      | .label k => out.push k
      | _ => out
    Ir.foldBlocks (fun out _ => out) fi (Ir.foldInlines fi #[] caption) body
  let floatsIn (body : Array Ir.Block) :
      Array (Ir.FloatKind × Option Nat × Array Ir.Block × Array Ir.Inline) :=
    Ir.foldBlocks (fun out b => match b with
      | .float kind num _ fbody fcaption => out.push (kind, num, fbody, fcaption)
      | _ => out) (fun out _ => out) #[] body
  for n in goldenNames do
    let src ← IO.FS.readFile s!"testdata/corpus/{n}.tex"
    let (doc, _) ← elabFixture n src
    let refs := Ir.foldBlocks (fun out _ => out)
      (fun out x => match x with
        | .ref key form text _ => out.push (key, form, text)
        | _ => out) #[] doc.body
    for (kind, num, body, caption) in floatsIn doc.body do
      if kind != Ir.FloatKind.sub then
        if let some nnum := num then
          let nested := (floatsIn body).flatMap fun (_, _, nb, nc) => labelsIn nb nc
          let direct := (labelsIn body caption).filter (!nested.contains ·)
          for key in direct do
            for (k, form, text) in refs do
              if k == key then
                let expect := if form == Ir.RefForm.paren then s!"({nnum})"
                  else toString nnum
                check ref
                  s!"float ref agreement {n}: '{key}' resolves to the number its float carries"
                  (text == expect)
