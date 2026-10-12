module

public import Tests.Support
public import LeanTex.Core.ContrastSolve

public section

open LeanTex.Core

namespace Tests.Schemes

/-- ΔEOK between two colours, thousandths. -/
private def deltaEMilli (a b : Ir.Color) : Nat :=
  (Nat.sqrt (ContrastSolve.deltaEOkSq a b).toNat) / 10 ^ 15

/-- **The dark screen is the class's seeds carried to a dark page**: the
undeclared document's dark colours — page, ink, muted ink, rule, accent and
code ground — are what the class's default seeds generate there
(`SeedPalette.classSeedsIn`), each within ΔEOK 0.03 of the constants the
stylesheet shipped before (a zinc-900 page and zinc-400 muted ink,
stone-50 ink, a zinc-700 rule, a blue-400 accent and a zinc-800 code
ground, Tailwind v4's), so deleting them moved no colour visibly. -/
def checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let web : Ir.Palette := { classColors := { row := .web, depth := .documents } }
  let former : List (Ir.Role × Ir.Color) :=
    [(.page, { r := 0x18, g := 0x18, b := 0x1B }), (.ink, { r := 0xFA, g := 0xFA, b := 0xF9 }),
     (.muted, { r := 0xA1, g := 0xA1, b := 0xAA }), (.rule, { r := 0x3F, g := 0x3F, b := 0x46 }),
     (.accent, { r := 0x60, g := 0xA5, b := 0xFA }),
     (.codeSurface, { r := 0x27, g := 0x27, b := 0x2A })]
  for (r, c) in former do
    match Ir.Design.at web .dark r with
    | some d =>
      t s!"the dark {(Ir.ColorRef.role r).key} {d.css} stands within ΔEOK 0.03 of the former {c.css}"
        (deltaEMilli d c ≤ 30)
    | none => t s!"the dark {(Ir.ColorRef.role r).key} resolves" false

/-- **A scheme that cannot carry a colour is dropped, named once**: on a
mid-grey page a black ink and a white alert both read past AA on the light
screen, which ships them as declared, but no tone of either reaches SC
1.4.6's 7:1 there, and the page moved to serve the ink (`Ir.Palette.view`)
leaves the alert further off, so the page ships without its more-contrast
light screen and names the alert once (W0308, `lightMore:alert@bg`); every
dropped scheme is paid for (`Contrast.scheme_drop_accounts`). Black alone
on that page takes a lighter page there. A deck offers its own screen and
its more contrast; a document every scheme. Invented content. -/
def dropChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, _) := elabStr (dvDoc "\\palette{ bg = #767676, fg = #000000, alert = #FFFFFF }\n" "x")
  let j := Contrast.schemeJudge doc
  t s!"a mid-grey page under two inks ships every scheme but its more-contrast light one \
({j.shipped.map (·.name)})"
    (j.shipped == [.print, .light, .dark, .darkMore] && j.dropped.map (·.1) == [.lightMore])
  let named := j.diags.filter (·.code == "W0308")
  t "the colour the dropped scheme could not carry is named once, under its subject"
    (named.size == 1 && named.all (·.subject == some "lightMore:alert@bg"))
  let (inked, _) := elabStr (dvDoc "\\palette{ bg = #767676, fg = #000000 }\n" "x")
  let ij := Contrast.schemeJudge inked
  let moreBg := ((ij.views.head?.map (·.2)).getD []).zip ij.frames |>.findSome? fun (v, f) =>
    if f.scheme == .lightMore then Ir.Design.at v .lightMore .page else none
  t s!"black alone on that page ships every scheme, on a page moved to the gate there: \
{moreBg.map (·.css)}"
    (ij.shipped == Ir.Scheme.all && moreBg.any fun g =>
      g != { r := 0x76, g := 0x76, b := 0x76 } &&
        Contrast.aaaText ≤ Contrast.contrastMilli Ir.Color.black g)
  t "the page's HTML names it too"
    ((HtmlDoc.emit {} doc).2.any fun d => d.code == "W0308")
  let (plain, _) := elabStr (dvDoc "" "x")
  t "an undeclared document ships every scheme"
    ((Contrast.schemeJudge plain).shipped == Ir.Scheme.all)
  let (deck, _) := elabStr (dvDeck "" "\\begin{frame}{T}\nx\n\\end{frame}")
  t "a deck ships its print, its own screen and that screen's more contrast"
    ((Contrast.schemeJudge deck).shipped == [.print, .light, .lightMore])


mutual

/-- Each listing box of a typed tree, with the custom properties in scope at
it — its own declarations first, then its ancestors' — and its own style. -/
def preBoxesOne (vars : List (String × String))
    (acc : Array (List (String × String) × String × Array Html.Node)) :
    Html.Node → Array (List (String × String) × String × Array Html.Node)
  | .elem t attrs kids =>
    let style := ((attrs.find? (·.1 == "style")).map (·.2)).getD ""
    let vars := styleVars style ++ vars
    if t == "pre" then acc.push (vars, style, kids) else preBoxesList vars acc kids.toList
  | .text _ | .style _ | .script _ _ => acc

def preBoxesList (vars : List (String × String))
    (acc : Array (List (String × String) × String × Array Html.Node)) :
    List Html.Node → Array (List (String × String) × String × Array Html.Node)
  | [] => acc
  | n :: rest => preBoxesList vars (preBoxesOne vars acc n) rest

end

/-- A colour a CSS value spells, `#rrggbb`. -/
def hexColor? (v : String) : Option Ir.Color :=
  if v.length == 7 && v.startsWith "#" then
    (({} : Ir.Palette).resolveSource none v).toOption.join
  else none

/-- Whether a colour reads as a dark ground: more against white than black. -/
def darkGround (c : Ir.Color) : Bool :=
  decide (Contrast.contrastMilli c Ir.Color.black < Contrast.contrastMilli c Ir.Color.white)

/-- **Every listing a page ships stands on its scheme's ground with every
token legible there**, as one scheme's cascade reads the typed tree
(`schemeRoot`, `schemeRead`): each listing box's ground — its own
declaration, else the page's `pre` rule, else the page — and each token's
colour, its class's rule (`tokenClassColors`) through the properties in
scope at the box, with the box's own text colour, each at `req` or more on
that ground, which `darkOnly` asks to be dark. The offences, each naming the
box. -/
def listingOffences (head body : Array Html.Node) (s : Ir.Scheme) (req : Nat)
    (darkOnly : Bool := false) : Array String := Id.run do
  let css := treeCssList "" head.toList
  let (root, dark) := schemeRoot css s
  let classes := tokenClassColors css
  let preRule := ((sheetRules css).toList.find? fun (conds, sel, _) => conds.isEmpty && sel == "pre").map
    fun (_, _, decls) => cssDecls decls
  let bodyRule := ((sheetRules css).toList.find? fun (conds, sel, _) => conds.isEmpty && sel == "body").map
    fun (_, _, decls) => cssDecls decls
  let mut out : Array String := #[]
  let boxes := preBoxesList root #[] body.toList
  for h : i in [0:boxes.size] do
    let (vars, style, kids) := boxes[i]
    let decls := cssDecls style
    let read (v : String) : Option Ir.Color := hexColor? (schemeRead dark vars v)
    let ground := ((decls.lookup "background").orElse fun _ =>
        (preRule.bind (·.lookup "background")).filter (· != "none")).orElse fun _ =>
      bodyRule.bind (·.lookup "background")
    let ink := (decls.lookup "color").orElse fun _ => bodyRule.bind (·.lookup "color")
    match ground.bind read, ink.bind read with
    | some g, some fg =>
      if darkOnly && !darkGround g then
        out := out.push s!"listing {i + 1}: a light ground {g.css}"
      if Contrast.contrastMilli fg g < req then
        out := out.push s!"listing {i + 1}: text {fg.css} on {g.css}"
      for span in elemNodesList (· == "span") #[] kids.toList do
        if let .elem _ attrs sk := span then
          let cls := ((attrs.find? (·.1 == "class")).map (·.2)).getD ""
          if let some v := classes.lookup cls then
            match read v with
            | some c =>
              if Contrast.contrastMilli c g < req then
                out := out.push s!"listing {i + 1}: {cls} '{nodeTextList "" sk.toList}' {c.css} on {g.css}"
            | none => out := out.push s!"listing {i + 1}: {cls} reads no colour ({v})"
    | g, fg => out := out.push s!"listing {i + 1}: ground {g.map (·.css)}, text {fg.map (·.css)}"
  return out

/-- **Under the dark screen every corpus listing stands on a dark ground,
every token at 4.5:1 or more on it**, by the dark scheme's cascade over the
typed tree (`listingOffences`): the light code slab is gone. Each corpus page
that ships the dark scheme and holds a listing. -/
def darkListingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let mut pages := 0
  for (path, doc) in ← corpusTwinDocs do
    if !(Contrast.schemeJudge doc).shipped.contains .dark then continue
    let (head, body, _) := HtmlDoc.emitTree {} doc
    let css := treeCssList "" head.toList
    let (root, _) := schemeRoot css .dark
    let boxes := preBoxesList root #[] body.toList
    if boxes.isEmpty then continue
    pages := pages + 1
    let offences := listingOffences head body .dark Contrast.aaText (darkOnly := true)
    t s!"dark listings: {path} stands every listing on a dark ground, every token legible: \
{offences.toList}" offences.isEmpty
  t s!"dark listings: the corpus holds pages with listings that ship the dark screen ({pages})"
    (pages ≥ 3)

mutual

/-- What a typed tree paints, element by element: each element's own ground
(its `background`), and each text's colour — the nearest colour an element
around it states, its own `color` or its token class's (`classes`) — each
beside the custom properties in scope there. -/
def paintedOne (classes : List (String × String)) (vars : List (String × String))
    (color : Option String) (acc : Array (List (String × String) × String × Bool × String)) :
    Html.Node → Array (List (String × String) × String × Bool × String)
  | .elem _ attrs kids =>
    let style := ((attrs.find? (·.1 == "style")).map (·.2)).getD ""
    let cls := ((attrs.find? (·.1 == "class")).map (·.2)).getD ""
    let vars := styleVars style ++ vars
    let decls := cssDecls style
    let color := ((cls.splitOn " ").findSome? (classes.lookup ·)).orElse fun _ =>
      (decls.lookup "color").orElse fun _ => color
    let acc := match decls.lookup "background" with
      | some g => acc.push (vars, g, false, nodeTextList "" kids.toList)
      | none => acc
    paintedList classes vars color acc kids.toList
  | .text x =>
    match color with
    | some c => if x.trimAscii.isEmpty then acc else acc.push (vars, c, true, x)
    | none => acc
  | .style _ | .script _ _ => acc

def paintedList (classes : List (String × String)) (vars : List (String × String))
    (color : Option String) (acc : Array (List (String × String) × String × Bool × String)) :
    List Html.Node → Array (List (String × String) × String × Bool × String)
  | [] => acc
  | n :: rest => paintedList classes vars color (paintedOne classes vars color acc n) rest

end

/-- The colours a shipped page paints text in and fills with: every run's
ink, and every fill's, rule's, decoration's and polygon's colour
(`Layout.Out`). -/
def shippedColors (out : Layout.Out) : Array Ir.Color × Array Ir.Color :=
  let add (acc : Array Ir.Color) (c : Ir.Color) := if acc.contains c then acc else acc.push c
  let segs := out.pages.flatMap fun p => p.lines.flatMap (·.segs)
  let inks := segs.foldl (fun acc s => match s with
    | .run _ c _ _ glyphs .. => if glyphs.isEmpty then acc else add acc c
    | .gap .. | .decoratedGap .. | .decoration .. | .rule .. | .image .. | .poly .. => acc) #[]
  let marks := segs.foldl (fun acc s => match s with
    | .decoration _ _ _ _ c | .rule _ _ _ c | .poly _ c => add acc c
    | .run .. | .gap .. | .decoratedGap .. | .image .. => acc) #[]
  (inks, out.pages.foldl (fun acc p => p.fills.foldl (fun acc f => add acc f.color) acc) marks)

/-- **What the printed web page paints, the PDF paints**: every colour the
typed tree states for a text (`paintedList`: the nearest element's own
`color` or token class colour, `tokenClassColors`), as the print cascade
reads it (`schemeRoot`, `schemeRead`), is one the shipped page sets a run
in, and every ground an element states is one the page fills or marks, or
its own page (`Layout.Out`). The offences. -/
def printOffences (fonts : Font.FontSet) (doc : Ir.Doc) : Array String := Id.run do
  let (inks, fills) := shippedColors (layoutOf fonts doc (Layout.Geom.ofPage doc.page))
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  let (root, dark) := schemeRoot css .print
  let page := (Ir.Design.at doc.palette .print .page).getD Ir.Color.white
  let mut out : Array String := #[]
  for (vars, v, text, shown) in paintedList (tokenClassColors css) root none #[] body.toList do
    let some c := hexColor? (schemeRead dark vars v) | continue
    let what := (shown.trimAscii.toString.take 24).toString
    if text then
      unless inks.contains c do out := out.push s!"text {c.css} ('{what}') is no run's ink"
    else unless c == page || fills.contains c do
      out := out.push s!"ground {c.css} ('{what}') is no fill"
  return out

/-- **On every corpus page that ships print, the printed web page's colours
are the PDF's** (`printOffences`): `@media print` restates each colour the
print column holds, and a listing's, an epoch's and a coloured run's own
declarations read their print values there. -/
def printChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let mathSet ← mathSetOf fonts
  let shipped ← LeanTex.Cli.FontDiscovery.scanRoots [testFonts]
  let mut pages := 0
  for (path, doc) in ← corpusTwinDocs do
    if !(Contrast.schemeJudge doc).shipped.contains .print then continue
    pages := pages + 1
    -- The faces the document names, as the driver resolves them: a formula
    -- set in a face with no math sets its colour as the PDF's own.
    let fs ← fixtureFontSet fonts mathSet shipped doc
    let offences := printOffences fs doc
    t s!"print colours: {path} paints what its PDF paints: {offences.toList}" offences.isEmpty
  t s!"print colours: the corpus's pages ship print ({pages})" (pages ≥ 50)

/-- **High-contrast mode draws the bars the colours drew**: under
`forced-colors: active` the page's frame-title bars, standout frames and
block title bands carry a `CanvasText` border, a rule whose selectors stand
on elements the deck's typed tree holds. -/
def forcedColorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, _) := elabStr (dvDeck "" ("\\begin{frame}{Bar}\\begin{block}{Band}x\\end{block}\\end{frame}" ++
    "\\begin{frame}[standout]Out\\end{frame}"))
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  let forced := (sheetRules css).toList.filter fun (conds, _, decls) =>
    conds == ["@media (forced-colors: active)"] && hasStr decls "CanvasText"
  let sels := forced.flatMap fun (_, sel, _) => cssSelParts sel
  t s!"forced colours: the bars carry a CanvasText border: {sels}"
    (["section.slide > header", "section.slide.standout", "section.block > header"].all sels.contains)
  let stages := elemNodesList (· == "section") #[] body.toList
  let classes (n : Html.Node) : List String := match n with
    | .elem _ attrs _ => (((attrs.find? (·.1 == "class")).map (·.2)).getD "").splitOn " "
    | _ => []
  let hasHeader (n : Html.Node) : Bool := match n with
    | .elem _ _ kids => kids.any fun k => match k with
      | .elem "header" _ _ => true
      | _ => false
    | _ => false
  t "forced colours: the deck holds a titled frame, a standout frame and a titled block"
    (stages.any (fun n => (classes n).contains "slide" && hasHeader n) &&
     stages.any (fun n => (classes n).contains "standout") &&
     stages.any (fun n => (classes n).contains "block" && hasHeader n))

end Tests.Schemes
