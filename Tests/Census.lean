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
        fun l => hasStr l.text "1").getD false)]),
  ("abstract", fun geom c => [
    ("one page", c.size == 1),
    ("the class furniture heading ships", hasStr (censusText c) "Abstract"),
    ("the abstract body ships", hasStr (censusText c) "Entirely synthetic findings"),
    ("the abstract body is set off the margin",
      (lineXOf c 0 "Entirely synthetic findings").any fun x => decide (x > geom.hmargin)),
    ("the following body returns to the margin",
      lineXOf c 0 "Body text follows the abstract" == some geom.hmargin)]),
  ("paragraphs", fun _ c => [
    ("one page", c.size == 1),
    ("the opening sentence ships", hasStr (censusText c) "Typesetting is the arrangement of type"),
    ("it wraps to at least four lines", (c[0]?.map fun p => decide (p.lines.size ≥ 4)).getD false)]),
  ("layout", fun _ c => [
    ("one page", c.size == 1),
    ("the heading ships", hasStr (censusText c) "The first section"),
    ("a list marker ships beside its item", hasStr (censusText c) "• One concise point")]),
  ("declared", fun _ c => [
    ("one page, as the fixture asserts", c.size == 1),
    ("the heading ships", hasStr (censusText c) "Declared geometry")]),
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
  ("themed", fun _ c => [
    ("pages", c.size == 6),
    ("the section page carries its progress-bar fills", (c[1]?.map fun p => decide (p.fills ≥ 2)).getD false),
    ("the frame-title bar fills", (c[2]?.map fun p => decide (p.fills ≥ 1)).getD false),
    ("the covered step dims the alert and example beats in place",
      pageCovered c 3 "alert beat" && pageCovered c 3 "teal example beat"),
    ("the covered beats still ship", pageHas c 3 "alert beat"),
    ("the second step reveals them", pageAllRevealed c 4),
    ("the standout frame fills its background", (c[5]?.map fun p => decide (p.fills ≥ 1)).getD false)]),
  ("latex-idioms", fun _ c => [
    ("one page", c.size == 1),
    ("the running head ships", hasStr (censusText c) "Alex Doe"),
    ("the section rules draw", c.any fun p => decide (p.rules ≥ 1))]),
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
    ("the web-only nav never reaches the page",
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
  ("math", fun _ c => [
    ("one page", c.size == 1),
    ("prose around the display ships",
      hasStr (censusText c) "The paragraph continues after the display"),
    ("the display-size sum ships as a glyph", hasStr (censusText c) "∑"),
    ("an align row ships aligned glyphs", hasStr (censusText c) "=(𝑥−1)(𝑥+1)"),
    ("every fraction bar and overbar ships as a rule",
      ((c[0]?.map (·.rules)).getD 0) == 9),
    ("the out-of-scope accent keeps its source", hasStr (censusText c) "\\hat"),
    ("\\mathbb takes its Letterlike scalars", hasStr (censusText c) "ℝ"
      && hasStr (censusText c) "ℂ"),
    ("the bold alphabets ship, variables kept italic",
      hasStr (censusText c) "𝐯" && hasStr (censusText c) "𝜷"),
    ("\\mathrm sets upright", hasStr (censusText c) "Err"),
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
  ("trio-card", fun _ c => [
    ("two faces, two pages", c.size == 2),
    ("the front ships the name", pageHas c 0 "Pat Placeholder"),
    ("the back ships the contact", pageHas c 1 "press@example.org")])]

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
    let (doc, _) := Elab.run s!"{n}.tex" src
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
    let out := Layout.run geom fs (some pats) doc
    let c := censusOf (coveredColorsOf doc) out
    for (label, ok) in facts geom c do
      check ref s!"census {n}: {label}" ok

