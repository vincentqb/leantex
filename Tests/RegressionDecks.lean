import Tests.RegressionSupport

open LeanTex.Core

namespace Tests.RegressionDecks

open Regression

-- Pins to the invented local theme, independent of the elaborated palette.
private def ink : Ir.Color := { r := 0x24, g := 0x33, b := 0x47 }
private def paper : Ir.Color := { r := 0xfa, g := 0xfc, b := 0xff }
private def gold : Ir.Color := { r := 0xf4, g := 0xce, b := 0x84 }
private def blue : Ir.Color := { r := 0x1c, g := 0x50, b := 0x70 }
private def rust : Ir.Color := { r := 0x7a, g := 0x32, b := 0x1d }

private def deckAttr (n : Html.Node) (key : String) : Option String :=
  match n with
  | .elem _ attrs _ => (attrs.find? (·.1 == key)).map (·.2)
  | _ => none

private def cls (n : Html.Node) (name : String) : Bool :=
  ((deckAttr n "class").getD "" |>.splitOn " ").contains name

private def elements (a : Artifact) : Array Html.Node :=
  elemNodesList (fun _ => true) #[] a.body.toList

private def linesAt (a : Artifact) (page : Nat) : Array Layout.LineOut :=
  ((a.out.pages[page]?.map (·.lines)).getD #[]).filter (!·.furniture)

private def textAt (a : Artifact) (page : Nat) : Array String :=
  (linesAt a page).filter hasGlyphRun |>.map lineInk

private def glyphsAt (a : Artifact) (page : Nat) (text : String) : Array ShippedGlyph :=
  (shippedBodyGlyphs a.out).filter fun g =>
    g.page == page && ((linesAt a page)[g.line]?.map lineInk) == some text

private def painted (ref : IO.Ref (List String)) (name : String) (a : Artifact)
    (page : Nat) (text : String) (color : Ir.Color) : IO Unit := do
  let gs := glyphsAt a page text
  check ref s!"{name}: page {page + 1} paint of {text}"
    (!gs.isEmpty && gs.all (·.color == color))

private def ground (a : Artifact) (page : Nat) (color : Ir.Color) : Bool :=
  (a.out.pages[page]?).any fun p => p.fills.any fun f =>
    f.color == color && f.x ≤ 0 && f.y ≤ 0 &&
      f.x + f.w ≥ a.geom.pageW && f.y + f.h ≥ a.geom.pageH

private def styled (nodes : List Html.Node) (text css : String) : Bool :=
  (elemStylesList #[] nodes).any fun (t, s) => t == text && hasStr s css

private def stages (ref : IO.Ref (List String)) (name : String) (a : Artifact)
    (frames : Array (Option Nat)) (labels : Array String)
    (ids : Array (String × String)) (foots : Array (String × String)) : IO Unit := do
  let es := elements a
  check ref s!"{name}: shipped page/frame identities" (a.out.pages.map (·.frame) == frames)
  check ref s!"{name}: HTML snap identities"
    ((es.filter (fun n => (deckAttr n "data-snap").isSome)).map (deckAttr · "data-slide-label") ==
      labels.map some)
  check ref s!"{name}: HTML frame anchors and numbers"
    ((es.filter (fun n => (deckAttr n "data-frame-number").isSome)).map
      (fun n => ((deckAttr n "id").getD "", (deckAttr n "data-frame-number").getD "")) == ids)
  check ref s!"{name}: shipped footer slots" (pdfFoots a.out == foots)
  check ref s!"{name}: physical footer glyphs"
    ((a.out.pages.filter (·.foot.isSome)).map
      (fun p => p.lines.filter (fun l => l.furniture && hasGlyphRun l) |>.map lineInk) ==
      foots.map (fun (l, r) => #[r, l].filter (!·.isEmpty)))
  check ref s!"{name}: HTML footer slots"
    (slideFootsList #[] a.body.toList == dedupConsecutive foots)

private def title (ref : IO.Ref (List String)) (name : String) (a : Artifact)
    (heading byline : String) : IO Unit := do
  check ref s!"{name}: composed title page text"
    (textAt a 0 == #[heading, byline, "Paper Lab"])
  painted ref name a 0 heading paper
  painted ref name a 0 byline gold
  painted ref name a 0 "Paper Lab" gold
  check ref s!"{name}: custom title ground" (ground a 0 ink)
  let ts := (elements a).filter (cls · "title-page")
  check ref s!"{name}: HTML title text and decoration"
    (ts.size == 1 && #[heading, byline, "Paper Lab"].all
      (fun s => treeShownOccurs ts s == 1))
  check ref s!"{name}: HTML title accent"
    (styled ts.toList byline "color: var(--deckGold, #f4ce84)" &&
      styled ts.toList "Paper Lab" "color: var(--deckGold, #f4ce84)")
  let css := treeCssList "" a.head.toList
  check ref s!"{name}: HTML custom title palette"
    (#["--titlepagebg: #243347", "--titlepagefg: #fafcff", "--deckGold: #f4ce84"].all
      (hasStr css))

private def workshop (ref : IO.Ref (List String)) (a : Artifact) : IO Unit := do
  let name := "decks/workshop"
  stages ref name a #[none, none, some 1, none, some 2, some 2, some 3, some 4]
    #["titlepage", "section-0", "1", "section-1", "2.1", "2.2", "3", "4"]
    #[("choose-the-pieces", "1"), ("arrange-then-attach", "2"),
      ("pause-and-compare", "3"), ("pack-the-pieces", "4")]
    #[("Mosaic workshop", "1 / 4"), ("Mosaic workshop", "2 / 4"),
      ("Mosaic workshop", "2 / 4"), ("Workshop reminder", ""), ("", "4 / 4")]
  title ref name a "Paper Mosaic Workshop" "Workshop Facilitators"
  check ref s!"{name}: section inputs ship their pages"
    (textAt a 1 == #["Plan the pattern"] && textAt a 3 == #["Build the pattern"] &&
      ((elements a).filter (cls · "section-page")).map (nodeTextOne "") ==
        #["Plan the pattern", "Build the pattern"])
  check ref s!"{name}: opening frame text"
    (textAt a 2 == #["Choose the pieces", "Use three paper shapes for a small mosaic.",
      "• A square provides the centre.", "• Two triangles complete the border."])
  let late := "Attach each piece after checking the gaps."
  for page in #[4, 5] do
    check ref s!"{name}: pause page {page + 1} retains both paragraphs"
      (textAt a page == #["Arrange then attach", "Place the pieces on a blank card.", late])
    painted ref name a page late (if page == 4 then Oklab.cover 22 paper ink else ink)
  let step := (elements a).filter fun n => cls n "step" && nodeTextOne "" n == late
  check ref s!"{name}: HTML pause coverage"
    (step.size == 1 && step.all (fun n => deckAttr n "data-steps" == some "2" &&
      deckAttr n "data-step" == some "2" && (deckAttr n "hidden").isNone))
  check ref s!"{name}: standout text and ground"
    (textAt a 6 == #["Keep one clear gap."] && ground a 6 ink)
  painted ref name a 6 "Keep one clear gap." paper
  let standout := (elements a).filter (cls · "standout")
  check ref s!"{name}: HTML standout and explicit reminder"
    (standout.size == 1 && treeShownOccurs standout "Keep one clear gap." == 1 &&
      slideFootsList #[] standout.toList == #[("Workshop reminder", "")])
  let css := treeCssList "" a.head.toList
  check ref s!"{name}: HTML standout palette"
    (hasStr css "--standoutbg: #243347" && hasStr css "--standoutfg: #fafcff")
  check ref s!"{name}: numbered closing frame"
    (textAt a 7 == #["Pack the pieces", "Save the unused shapes for another pattern."])
  check ref s!"{name}: HTML opening and closing text"
    (#["Choose the pieces", "Use three paper shapes for a small mosaic.",
      "A square provides the centre.", "Two triangles complete the border.",
      "Pack the pieces", "Save the unused shapes for another pattern."].all
      (fun text => treeShownOccurs a.body text == 1))

private def strike (ref : IO.Ref (List String)) (a : Artifact) (page : Nat)
    (text : String) (on : Bool) : IO Unit := do
  let gs := glyphsAt a page text
  let bases := (linesAt a page).filter (fun l => lineInk l == text)
  -- Decoration riders share the text's origin but contain no glyphs.
  let rules := ((linesAt a page).filter (fun l =>
    bases.any (fun b => l.x == b.x && l.y == b.y))).flatMap fun l =>
    l.segs.filterMap fun s => match s with
      | .decoration .lineThrough w h raise color => some (w, h, raise, color)
      | _ => none
  check ref s!"decks/overlays: page {page + 1} strike on {text}"
    (!gs.isEmpty && gs.all (fun g => g.decorations.lineThrough.isSome == on) &&
      (if on then !rules.isEmpty &&
        rules.all (fun (w, h, raise, c) => w > 0 && h > 0 && raise > 0 && c == ink)
       else rules.isEmpty))

private def struck (n : Html.Node) : Bool :=
  !(elemNodesList (· == "s") #[] [n]).isEmpty

private def overlays (ref : IO.Ref (List String)) (a : Artifact) : IO Unit := do
  let name := "decks/overlays"
  stages ref name a #[none, none, some 1, some 1, some 1, some 1]
    #["titlepage", "section-0", "1.1", "1.2", "1.3", "1.4"]
    #[("keep-the-right-version", "1")] (Array.replicate 4 ("Revision exercise", "1 / 1"))
  title ref name a "Mosaic Revision Exercise" "Practice Group"
  check ref s!"{name}: section page" (textAt a 1 == #["Review sequence"])
  for page in #[2, 3, 4, 5] do
    let corners := page == 2 || page == 5
    check ref s!"{name}: exact text at step {page - 1}"
      (textAt a page == #["Keep the right version",
        "A four-pass review alternates corner and centre checks.",
        "Corner marker", "Centre marker", "Loose piece", "Crowded border",
        if corners then "Check the corners." else "Check the centre."])
    painted ref name a page "Corner marker" (if corners then blue else Oklab.cover 22 paper blue)
    painted ref name a page "Centre marker" (if corners then Oklab.cover 22 paper rust else rust)
    strike ref a page "Loose piece" corners
    strike ref a page "Crowded border" (!corners)
  let es := elements a
  let cover (text : String) := es.filter fun n =>
    (cls n "step" || cls n "step-set") && nodeTextOne "" n == text
  let corner := cover "Corner marker"
  let centre := cover "Centre marker"
  check ref s!"{name}: HTML sparse cover preserves the hole"
    (corner.size == 1 && corner.all (fun n => cls n "step-set" &&
      deckAttr n "data-steps" == some "1 4" && (deckAttr n "hidden").isNone))
  check ref s!"{name}: HTML range cover retains both bounds"
    (centre.size == 1 && centre.all (fun n => cls n "step" &&
      deckAttr n "data-steps" == some "2 3" && deckAttr n "data-step" == some "2" &&
      deckAttr n "data-step-last" == some "3" && (deckAttr n "hidden").isNone))
  check ref s!"{name}: HTML cover colours"
    (styled corner.toList "Corner marker" "color: var(--deckBlue, #1c5070)" &&
      styled centre.toList "Centre marker" "color: var(--deckRust, #7a321d)")
  let css := treeCssList "" a.head.toList
  check ref s!"{name}: HTML cover palette and fraction"
    (hasStr css "--deckBlue: #1c5070" && hasStr css "--deckRust: #7a321d" &&
      (cssRuleOf css
        "html[data-deck-script] [data-snapped=\"2\"] .step-set:not([data-steps~=\"2\"])").any
        (hasStr · "opacity: 22%"))
  let alts (text : String) := es.filter fun n => cls n "alt" && nodeTextOne "" n == text
  let loose := alts "Loose piece"
  let crowded := alts "Crowded border"
  check ref s!"{name}: HTML sparse strike and plain complement"
    (loose.map (deckAttr · "data-steps") == #[some "1 4", some "2 3"] &&
      loose.map struck == #[true, false] &&
      loose.map (deckAttr · "hidden") == #[none, some "hidden"])
  check ref s!"{name}: HTML range strike and plain complement"
    (crowded.map (deckAttr · "class") == #[some "alt alt-pending", some "alt alt-crisp"] &&
      crowded.all (fun n => deckAttr n "data-step" == some "2" &&
        deckAttr n "data-step-last" == some "3") &&
      crowded.map struck == #[false, true] &&
      crowded.map (deckAttr · "hidden") == #[none, some "hidden"])
  for (text, mask) in #[("Check the corners.", "1 4"), ("Check the centre.", "2 3")] do
    check ref s!"{name}: HTML alternate mask for {text}"
      ((alts text).map (deckAttr · "data-steps") == #[some mask])
  check ref s!"{name}: HTML initial alternates show exactly one version"
    (#["Loose piece", "Crowded border", "Check the corners."].all
      (fun text => treeShownOccurs a.body text == 1) &&
      treeShownOccurs a.body "Check the centre." == 0)

private def leanLines : Array String := #[
  "def tileCount (xs : List Nat) : Nat := min xs.length 3",
  "#eval tileCount [2, 4, 6]", "#check \"square\"", "-- Keep <shapes> & spacing"]

private def pythonLines : Array String := #[
  "def tile_count(shapes):", "    return min(len(shapes), 3)",
  "print(tile_count([\"square\", \"triangle\"]))", "# Keep <shapes> & spacing"]

private def tokenPaint (a : Artifact) (page : Nat) (line word : String)
    (color : Ir.Color) : Bool :=
  let gs := glyphsAt a page line
  let chars := word.toList.toArray
  (List.range gs.size).any fun start =>
    let part := gs.extract start (start + chars.size)
    part.map (·.scalar) == chars && part.all (·.color == color)

private def deckListings (ref : IO.Ref (List String)) (a : Artifact) : IO Unit := do
  let name := "decks/listings"
  stages ref name a #[none, none, some 1, some 2] #["titlepage", "section-0", "1", "2"]
    #[("a-lean-helper", "1"), ("a-python-helper", "2")]
    #[("Counting tools", "1 / 2"), ("Counting tools", "2 / 2")]
  title ref name a "Small Tools for Paper Shapes" "Practice Group"
  check ref s!"{name}: section page" (textAt a 1 == #["Small counting tools"])
  let codes := elemNodesList (· == "code") #[] a.body.toList
  check ref s!"{name}: both native listing languages"
    (codes.map (deckAttr · "class") == #[some "language-lean4", some "language-python"])
  for (lang, page, source, heading, intro) in #[
      ("lean4", 2, leanLines, "A Lean helper",
        "Count at most three pieces before starting a pattern."),
      ("python", 3, pythonLines, "A Python helper",
        "The same limit works for a list of shape names.")] do
    let code := codes.filter (fun n => deckAttr n "class" == some s!"language-{lang}")
    let comment := source.back!
    check ref s!"{name}: {lang} exact shipped code including final comment"
      (textAt a page == #[heading, intro] ++ source)
    check ref s!"{name}: {lang} exact HTML source, indentation and terminal comment"
      (code.map (nodeTextOne "") == #[String.intercalate "\n" source.toList] &&
        treeShownOccurs code comment == 1)
    painted ref name a page comment { r := 0x3d, g := 0x7b, b := 0x7b }
    check ref s!"{name}: {lang} native keyword and string ink"
      (tokenPaint a page source[0]! "def" { r := 0, g := 0x80, b := 0 } &&
        tokenPaint a page source[2]! "\"square\"" { r := 0xba, g := 0x21, b := 0x21 })
    check ref s!"{name}: {lang} HTML token colours"
      (styled code.toList "def" "color: var(--codekeyword, #008000)" &&
        styled code.toList "\"square\"" "color: var(--codestring, #ba2121)" &&
        styled code.toList comment "color: var(--codecomment, #3d7b7b)")

end Tests.RegressionDecks

/-- Standalone TeX entries; local style and section files are dependencies.
The common harness owns publication validity and diagnostics. -/
def Tests.RegressionDecks.cases : Array Tests.Regression.Case := #[
  { path := "testdata/regression/decks/workshop.tex", check := Tests.RegressionDecks.workshop },
  { path := "testdata/regression/decks/overlays.tex", check := Tests.RegressionDecks.overlays },
  { path := "testdata/regression/decks/listings.tex", check := Tests.RegressionDecks.deckListings }]
