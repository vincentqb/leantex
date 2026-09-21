import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- Census assertions, one row per golden fixture: what each fixture's
shipped pages must show, judged from `Layout.Out` — never from the IR dump,
which witnesses elaboration only. `censusChecks` fails when a fixture in
`goldenNames` has no row here, so a fixture cannot enter the suite
witnessed by its golden alone. Facts are observable page claims: text
shipped (or deliberately not, for a note), covered-coloured runs on step
pages, rules and fills drawn, line positions for centring and columns. -/
def censusTable :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
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
    ("the code sets at the scale's footnotesize",
      lineSizeOf c 0 "defprobe(n):" ==
        some (geom.fontSize * ((Ir.sizeScale.lookup "footnotesize").getD 1000) / 1000))]),
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
    ("the heading ships", hasStr (censusText c) "Declared geometry")]),
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
    ("a title stands on the measure",
      lineXOf c 0 "A Plain Statement" == some geom.hmargin)]),
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
    ("link underlines ship as rules", (c[0]?.map fun p => decide (p.rules ≥ 1)).getD false)]),
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
  ("deck1610", fun geom c => [
    ("one page, the frame", c.size == 1),
    -- The stage a class option declares is the stage the pages ship on:
    -- aspectratio=1610 is beamer's 160×100 mm row (user guide §8.1),
    -- selected through Ir.slidesStages, never a string match.
    ("the pages ship on the declared 16:10 stage",
      geom.pageW == Dim.mm 160 && geom.pageH == Dim.mm 100),
    ("the frame title ships", pageHas c 0 "One declared key"),
    ("the frame body ships", pageHas c 0 "160 by 100 millimetres")]),
  ("themed", fun _ c => [
    ("pages", c.size == 8),
    ("the section page carries its progress-bar fills", (c[1]?.map fun p => decide (p.fills ≥ 2)).getD false),
    ("the frame-title bar fills", (c[2]?.map fun p => decide (p.fills ≥ 1)).getD false),
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
      (c[0]?.map fun p => p.lines.all (·.text.trimAscii.toString != "1")).getD false)]),
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
      (lineXOf c 1 "Questions?").any fun x => decide (x > geom.hmargin))]),
  ("columns", fun geom c => [
    ("two frames, two pages", c.size == 2),
    ("the narrow column sets right of the wide one",
      (lineXOf c 0 "A narrow aside.").any fun x => decide (x > geom.hmargin)),
    ("both equal shares ship", pageHas c 1 "left half" && pageHas c 1 "right half")]),
  ("overlays-blocks", fun _ c => [
    ("a page per step across all frames", c.size == 12),
    ("a list revealed whole is covered whole",
      pageCovered c 0 "Placeholder point one." && pageCovered c 0 "Placeholder point two."),
    ("the covered list still ships its markers", pageHas c 0 "• Placeholder point one."),
    ("alt shows its second beat covered first", pageCovered c 9 "The second beat."),
    ("alt covers the first beat on the later step", pageCovered c 10 "The first beat."),
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
      pageHas c 2 "Footers" && lineRightOf c 2 "1" == some (geom.pageW - geom.hmargin)),
    ("a framefoot note takes the left slot", pageHas c 3 "source: example.org/data"),
    ("the default footer returns when the wrapper ends",
      pageHas c 4 "Footers" && lineRightOf c 4 "3" == some (geom.pageW - geom.hmargin))]),
  -- The footline's slots have fixed positions (FINDINGS F5 correction): a
  -- slot's box is a function of the declared layout and the geometry alone
  -- (`Layout.bandSlotX`), so the number holds the right edge whatever the
  -- left slot holds — an empty left slot is not a case.
  ("footer-left", fun geom c => [
    ("pages", c.size == 4),
    ("the sectionless frame still numbers at the right edge",
      lineRightOf c 1 "1" == some (geom.pageW - geom.hmargin)),
    ("the number is a line of its own, whole and unmoved",
      ((c[1]?.bind fun p => p.lines.find? fun l => hasStr l.text "1").map
        fun l => l.text == "1").getD false),
    ("the section title takes the left slot flush left",
      lineXOf c 3 "Placement" == some geom.hmargin),
    ("the sectioned frame numbers at the same right edge",
      lineRightOf c 3 "2" == some (geom.pageW - geom.hmargin))]),
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
  -- lower priority — yields IN PLACE: still at the right margin, painted
  -- first so the note paints over it. The yield's diagnostic (W0333) and
  -- the paint order are asserted in bandChecks; the census states the
  -- boxes.
  ("footer-collide", fun geom c => [
    ("pages", c.size == 2),
    ("the number still ends at the right margin",
      lineRightOf c 1 "1" == some (geom.pageW - geom.hmargin)),
    ("the overlong note still ships flush left",
      lineXOf c 1 "0123456789" == some geom.hmargin)]),
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
    ("ordered marks on a slide", pageHas c 3 "1. First placeholder")]),
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
  ("diagram-refused", fun _ c => [
    ("one page", c.size == 1),
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
    ("every node ships a glyph line",
      (c[0]?.map fun p => decide (p.lines.size ≥ 3)).getD false)]),
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
      (lineXOf c 0 "invented row").any fun x => decide (x > geom.hmargin))]),
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
    ("the out-of-scope construct keeps its source", hasStr (censusText c) "\\overset"),
    ("\\mathbb takes its Letterlike scalars", hasStr (censusText c) "ℝ"
      && hasStr (censusText c) "ℂ"),
    ("the bold alphabets ship, variables kept italic",
      hasStr (censusText c) "𝐯" && hasStr (censusText c) "𝜷"),
    ("\\mathrm sets upright", hasStr (censusText c) "Err"),
    ("a document macro's expansion ships", hasStr (censusText c) "𝐰"),
    ("a word stands as a script's argument", hasStr (censusText c) "null")]),
  ("math-companion", fun _ c => [
    ("one page", c.size == 1),
    ("the inline formula ships italic math glyphs", hasStr (censusText c) "𝑥"),
    ("the display sum ships as a glyph", hasStr (censusText c) "∑"),
    ("the fraction bar ships as a rule", ((c[0]?.map (·.rules)).getD 0) == 1),
    ("prose after the display ships",
      hasStr (censusText c) "The paragraph continues after the display")]),
  ("math-first", fun _ c => [
    ("one page", c.size == 1),
    ("the inline formula ships italic math glyphs", hasStr (censusText c) "𝑥"),
    ("the display fraction bar ships as a rule", ((c[0]?.map (·.rules)).getD 0) == 1)]),
  ("quotes", fun geom c => [
    ("one page", c.size == 1),
    ("the quotation's text ships", hasStr (censusText c) "A short invented epigraph"),
    ("the quotation's second paragraph ships",
      hasStr (censusText c) "The second paragraph of the same quotation"),
    ("prose sits at the margin",
      lineXOf c 0 "A paragraph before the quotation" == some geom.hmargin),
    ("the quotation indents from the margin by the list indent",
      lineXOf c 0 "A short invented epigraph"
        == some (geom.hmargin + geom.listIndent))]),
  ("quote-deck", fun geom c => [
    ("one frame, one page", c.size == 1),
    ("the quotation ships on the slide",
      pageHas c 0 "Typesetting is invisible until it fails"),
    ("the slide's quotation indents from the margin",
      (lineXOf c 0 "Typesetting is invisible").any fun x =>
        decide (x == geom.hmargin + geom.listIndent))]),
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
    ("the shared section style draws its rules", (c[0]?.map (·.rules == 2)).getD false)]),
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
        p.fillRects.contains (geom.pageW - r.1 - r.2.2.1, r.2.1, r.2.2.1, r.2.2.2))])]

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
        (fun e => e.page.isNone && e.url.isNone) == some true)])]

/-- The census tier: every golden fixture also appears in `censusTable`,
and each row's facts hold on the pages the engine actually ships. A
fixture that declares a math face renders its census with the shipped
Fira Math in the math slot — the assertions over fraction bars and grown
glyphs are exactly what `oneFace` alone could never witness. -/
def censusChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let fira ← match Font.parse (← IO.FS.readBinFile (testFonts ++ "/FiraMath-Regular.otf")) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"census: FiraMath unparsable: {e}")
  let mathSet : Font.FontSet := { oneFace with
    fonts := oneFace.fonts.push fira
    math := some oneFace.fonts.size }
  for n in goldenNames do
    check ref s!"census covers {n}" (censusTable.any (·.1 == n))
  for (n, _) in censusTable do
    check ref s!"census row {n} names a golden fixture" (goldenNames.contains n)
  -- A fixture that reaches math without declaring a face resolves it the
  -- way the driver does (FontDb.pickMathFace over the shipped faces), so
  -- the census exercises the same decision a build runs.
  let shipped ← FontDb.scanRoots [testFonts]
  for (n, facts) in censusTable do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc, _) ← elabFixture n src
    let geom := Layout.Geom.ofPage doc.page
    let fs ← if doc.fonts.math.isSome then pure mathSet
      else if (Layout.docMathScalars doc).isEmpty then pure oneFace
      else do
        match ← FontDb.pickMathFace shipped (doc.fonts.body.getD "") with
        | some (face, _) =>
          match Font.parse (← IO.FS.readBinFile face.path) with
          | .ok f => pure { oneFace with
              fonts := oneFace.fonts.push f
              math := some oneFace.fonts.size }
          | .error _ => pure oneFace
        | none => pure oneFace
    -- The driver's per-scalar precompute, mirrored for the Private Use
    -- Area only: an icon glyph has no stand-in and no meaning outside its
    -- face, so the census finds its face the way a build does (the scan
    -- over the shipped corpus). Everything else keeps the deliberately
    -- minimal census set — the stand-in degradations are themselves under
    -- test (`listChecks`), and a broader map would silently upgrade them.
    let uncovered := (Layout.docScalars doc).filter fun ch =>
      0xE000 ≤ ch.toNat && ch.toNat ≤ 0xF8FF &&
        fs.fonts.all fun f => (f.gid ch).isNone
    let fs ← do
      if uncovered.isEmpty then pure fs
      else do
        let mut fs := fs
        for (ch, path) in ← FontDb.fallbackPicks shipped uncovered do
          match Font.parse (← IO.FS.readBinFile path) with
          | .ok f =>
            let idx := match fs.fonts.zipIdx.find? (fun p => p.1.family == f.family) with
              | some (_, i) => i
              | none => fs.fonts.size
            let fs' := if idx == fs.fonts.size then
                { fs with fonts := fs.fonts.push f } else fs
            fs := { fs' with fallback := fs'.fallback.push (ch, idx) }
          | .error _ => pure ()
        pure fs
    let out := layoutOf fs doc geom (some pats)
    let c := censusOf (coveredColorsOf doc) out
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
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
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
