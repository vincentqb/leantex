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

/-- **A scheme that cannot carry a colour is dropped, named once**: a
mid-grey ink on a mid-grey page reads at 1.0:1, which print and the light
screen ship as declared (the document's report names it), and neither a
tone of the ink nor one of the page reaches SC 1.4.6's 7:1 against the
other, so the page ships without its more-contrast light screen and names
the ink once (W0308, `lightMore:fg@bg`); the dark screens turn the page over
and carry the ink there. Where the colours ship as declared, the report
that judges declared colours names the pair (W0315), and no W0308 does. Every dropped scheme is paid for
(`Contrast.scheme_drop_accounts`). A black ink and a white alert the page
paints on that page ship every scheme: the page moves to serve the ink and
the alert is carried again on the moved page (`Ir.Palette.view`); an alert
the page never paints is never judged. A deck offers its own screen and its
more contrast; a document every scheme. Invented content. -/
def dropChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, said) := elabStr (dvDoc "\\palette{ bg = #767676, fg = #777777 }\n" "x")
  let j := Contrast.schemeJudge doc
  t s!"a mid-grey ink on a mid-grey page ships every scheme but its more-contrast light one \
({j.shipped.map (·.name)})"
    (j.shipped == [.print, .light, .dark, .darkMore] && j.dropped.map (·.1) == [.lightMore])
  let named := j.diags.filter (·.code == "W0308")
  t "the colour the dropped scheme could not carry is named once, under its subject"
    (named.size == 1 && named.all (·.subject == some "lightMore:fg@bg"))
  t "the page's HTML names it too"
    ((HtmlDoc.emit {} doc).2.any fun d => d.code == "W0308")
  t "where the colours ship as declared, the document's report names the ink, and no W0308 does"
    (said.any (·.code == "W0315") &&
     !(named.any fun d => d.subject.any fun k => k.startsWith "print:" || k.startsWith "light:"))
  let (two, _) := elabStr (dvDoc "\\palette{ bg = #767676, fg = #000000, alert = #FFFFFF }\n"
    "x \\textcolor{alert}{y}")
  t s!"a moved page carries both inks it holds ({(Contrast.schemeJudge two).shipped.map (·.name)})"
    ((Contrast.schemeJudge two).shipped == Ir.Scheme.all)
  let (unpainted, _) := elabStr (dvDoc "\\palette{ bg = #767676, fg = #777777, alert = #FFFFFF }\n"
    "x")
  t "an alert the page never paints is never named"
    (!((Contrast.schemeJudge unpainted).diags.any fun d => d.subject.any (hasStr · "alert")))
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
    let ground := ((lastDecl decls "background").orElse fun _ =>
        (preRule.bind (lastDecl · "background")).filter (· != "none")).orElse fun _ =>
      bodyRule.bind (lastDecl · "background")
    let ink := (lastDecl decls "color").orElse fun _ => bodyRule.bind (lastDecl · "color")
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

/-- A colour value that takes the colour around the element: `inherit`, and
`currentColor` on the `color` property itself. -/
def inherits (v : String) : Bool := v == "inherit" || v.toLower == "currentcolor"

mutual

/-- What a typed tree paints, element by element: each element's own ground
(its `background`), and each text's colour — the nearest colour an element
around it states, its own `color` or its token class's (`classes`) — each
beside the custom properties in scope there and whether an element around
it states a ground or is a picture, which stands on a plate of its own. -/
def paintedOne (classes : List (String × String)) (vars : List (String × String))
    (color : Option String) (grounded : Bool)
    (acc : Array (List (String × String) × String × Bool × String × Bool)) :
    Html.Node → Array (List (String × String) × String × Bool × String × Bool)
  | .elem tag attrs kids =>
    let style := ((attrs.find? (·.1 == "style")).map (·.2)).getD ""
    let cls := ((attrs.find? (·.1 == "class")).map (·.2)).getD ""
    let vars := styleVars style ++ vars
    let decls := cssDecls style
    let color := ((cls.splitOn " ").findSome? (classes.lookup ·)).orElse fun _ =>
      ((lastDecl decls "color").filter (!inherits ·)).orElse fun _ => color
    -- A picture stands on its own plate on a dark screen (the stylesheet's
    -- `svg.picture` rule), its labels with it.
    let grounded := grounded || (tag == "svg" && (cls.splitOn " ").contains "picture")
    let (acc, grounded) := match lastDecl decls "background" with
      | some g => (acc.push (vars, g, false, nodeTextList "" kids.toList, grounded), true)
      | none => (acc, grounded)
    paintedList classes vars color grounded acc kids.toList
  | .text x =>
    match color with
    | some c => if x.trimAscii.isEmpty then acc else acc.push (vars, c, true, x, grounded)
    | none => acc
  | .style _ | .script _ _ => acc

def paintedList (classes : List (String × String)) (vars : List (String × String))
    (color : Option String) (grounded : Bool)
    (acc : Array (List (String × String) × String × Bool × String × Bool)) :
    List Html.Node → Array (List (String × String) × String × Bool × String × Bool)
  | [] => acc
  | n :: rest => paintedList classes vars color grounded (paintedOne classes vars color grounded acc n) rest

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

/-- **What the printed web page paints, the PDF paints**: the printed page is
the PDF's page, and every colour the typed tree paints a text in
(`paintedList`: the nearest element's own `color` or token class colour,
`tokenClassColors`, else the body rule's ink), as the print cascade reads
it (`schemeRoot`, `schemeRead`) — with the more-contrast block in force
where `more` says, as a reader who asks more contrast prints — is one the
shipped page sets a run in, and every ground an element or the listing rule
states is one the page fills or marks, or its own page (`Layout.Out`). The
offences. -/
def printOffences (fonts : Font.FontSet) (doc : Ir.Doc) (more : Bool := false) :
    Array String := Id.run do
  let (inks, fills) := shippedColors (layoutOf fonts doc (Layout.Geom.ofPage doc.page))
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  let (root, dark) := schemeRoot css .print more
  let rules := sheetRules css
  -- The sheet's own paint, as print reads it: the body's ground and ink,
  -- and a listing box's ground, each where its rule holds in print.
  let ruleDecl (sel prop : String) : Option String :=
    (rules.toList.filter fun (conds, sl, _) => sl == sel && conds.all (holdsIn .print · more)).foldl
      (fun acc (_, _, decls) => (lastDecl (cssDecls decls) prop).orElse fun _ => acc) none
  let page := (Ir.Design.at doc.palette .print .page).getD Ir.Color.white
  let read (vars : List (String × String)) (v : String) : Option Ir.Color :=
    hexColor? (schemeRead dark vars v)
  let mut out : Array String := #[]
  let bodyInk := ruleDecl "body" "color"
  let bodyGround := (ruleDecl "body" "background").bind (read root)
  if bodyGround != some page then
    out := out.push s!"the printed page {bodyGround.map (·.css)} is not the PDF's {page.css}"
  let listings := (elemNodesList (· == "pre") #[] body.toList).size
  if let some g := (ruleDecl "pre" "background").bind (read root) then
    unless listings == 0 || g == page || fills.contains g do
      out := out.push s!"the listing ground {g.css} is no fill"
  for (vars, v, text, shown, _) in paintedList (tokenClassColors css) root bodyInk false #[]
      body.toList do
    let some c := read vars v | continue
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
    -- A reader who asks more contrast prints with that block in force.
    let more := printOffences fs doc (more := true)
    t s!"print colours: {path} paints what its PDF paints under more contrast: {more.toList}"
      more.isEmpty
  t s!"print colours: the corpus's pages ship print ({pages})" (pages ≥ 50)

/-- **On the dark screen every colour a text states reads on the page**: on
every corpus page that ships the dark scheme, each text whose colour an
element states (`paintedList`: its own `color`, a token class's) and that
stands on no ground an element states reads at 4.5:1 or more on the page,
as the dark scheme's cascade reads both (`schemeRoot`, `schemeRead`): a
colour no palette names rides its carrying in its one declaration
(`HtmlDoc.Config.literal`), a formula's as a paragraph's. The offences. -/
def darkTextOffences (doc : Ir.Doc) : Array String := Id.run do
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  let (root, dark) := schemeRoot css .dark
  let page := (root.lookup "--ltx-bg").bind fun v => hexColor? (schemeRead dark root v)
  let some page := page | return #["the dark page reads no colour"]
  let mut out : Array String := #[]
  for (vars, v, text, shown, grounded) in paintedList (tokenClassColors css) root none false #[]
      body.toList do
    if !text || grounded then continue
    let some c := hexColor? (schemeRead dark vars v) | continue
    if Contrast.contrastMilli c page < Contrast.aaText then
      out := out.push s!"'{(shown.trimAscii.toString.take 24).toString}' {c.css} on {page.css}"
  return out

def darkTextChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let mut pages := 0
  for (path, doc) in ← corpusTwinDocs do
    if !(Contrast.schemeJudge doc).shipped.contains .dark then continue
    pages := pages + 1
    let offences := darkTextOffences doc
    t s!"dark text: {path} sets every stated colour legibly on its page: {offences.toList}"
      offences.isEmpty
  t s!"dark text: the corpus's pages ship the dark screen ({pages})" (pages ≥ 50)

/-- **Each scheme a reader asks for reads what the page ships for it**: for a
document whose ink every scheme carries differently, under every declared
list of schemes — print and the light screen with each subset of the dark
screen and the two more-contrast schemes — and for a page whose judge drops
one, the static cascade a reader's preferences select (`schemeRoot`,
`schemeRead`) gives the page's ink and ground as the shipped scheme's view
holds them; where the scheme is not shipped, as its polarity's plain screen
does, and where the page offers that polarity nothing, as the light screen
does — or its more scheme, for a reader asking more contrast: neither
polarity reads the other's values, and a more-contrast scheme ships whether
or not the other polarity's does. -/
def subsetChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let extra : List Ir.Scheme := [.dark, .lightMore, .darkMore]
  let subsets : List (List Ir.Scheme) := (List.range 8).map fun m =>
    (List.range 3).filterMap fun i => if m / 2 ^ i % 2 == 1 then extra[i]? else none
  let docs := (subsets.map fun sub =>
      let list := String.intercalate ", " (([Ir.Scheme.print, .light] ++ sub).map (·.name))
      (list, dvDoc s!"\\palette\{ fg = #6E6E6E, bg = #FBFBFB }\n\\output\{ schemes = {list} }\n" "x")) ++
    -- A scheme the judge drops (W0308, `dropChecks`' witness) reads as one
    -- the document never asked for; a list naming a more scheme and not its
    -- screen holds the more scheme as its floor.
    [("lightMore dropped", dvDoc "\\palette{ bg = #767676, fg = #777777 }\n" "x"),
     ("print, lightMore, dark", dvDoc ("\\palette{ fg = #6E6E6E, bg = #FBFBFB }\n" ++
        "\\output{ schemes = print, lightMore, dark }\n") "x"),
     ("print, dark, lightMore", dvDoc ("\\palette{ fg = #6E6E6E, bg = #FBFBFB }\n" ++
        "\\output{ schemes = print, dark, lightMore }\n") "x")]
  for (list, src) in docs do
    let (doc, _) := elabStr src
    let j := Contrast.schemeJudge doc
    let views := ((j.views.head?.map (·.2)).getD [])
    let viewIn (s : Ir.Scheme) : Option Ir.Palette :=
      ((j.frames.zip views).find? (·.1.scheme == s)).map (·.2)
    let (head, _, _) := HtmlDoc.emitTree {} doc
    let css := treeCssList "" head.toList
    for s in [Ir.Scheme.light, .dark, .lightMore, .darkMore] do
      -- A polarity the page offers no screen of reads the floor
      -- (`HtmlDoc.floorScheme`); under more contrast its more scheme where
      -- that ships.
      let offers := j.shipped.contains s.base || (s.more && j.shipped.contains s)
      let s' := if offers then s else if s.more then Ir.Scheme.lightMore else .light
      let target := if j.shipped.contains s' then s'
        else if j.shipped.contains s'.base then s'.base
        else HtmlDoc.floorScheme j.frames doc.palette.homeScreen
      let (root, dark) := schemeRoot css s
      for r in [Ir.Role.ink, .page] do
        let got := hexColor? (schemeRead dark root s!"var({HtmlDoc.roleVar r})")
        let want := (viewIn target).bind (Ir.Design.at · target r)
        t s!"scheme subsets [{list}]: {s.name} reads {(Ir.ColorRef.role r).key} as {target.name} \
ships it ({got.map (·.css)}, {want.map (·.css)})" (got.isSome && got == want)

/-- **A picture stands on its document's page wherever the screen turns
over**: on a declared light page the dark screen's plate under a picture is
that page, and on a declared dark page the light screen's is that page —
never the page the scheme carries, which a declared page reflects to the
other polarity. Read through the cascade of the turned screen
(`schemeRoot`, `sideOf`). Invented content. -/
def plateChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (name, page, turned) in [("light", "F4F0E6", Ir.Scheme.dark), ("dark", "14181E", .light)] do
    let (doc, _) := elabStr (dvDoc s!"\\usepackage\{tikz}\n\\pagecolor[HTML]\{{page}}\n"
      "\\begin{tikzpicture}\\draw (0,0) -- (1,1);\\end{tikzpicture}")
    let (head, body, _) := HtmlDoc.emitTree {} doc
    let css := treeCssList "" head.toList
    let (_, dark) := schemeRoot css turned
    let plate := (sheetRules css).toList.findSome? fun (conds, sel, decls) =>
      if sel == "img.see-through, svg.picture" && conds.all (holdsIn turned) then
        lastDecl (cssDecls decls) "background" else none
    let pictures := (elemNodesList (· == "svg") #[] body.toList).size
    t s!"plates: a {name} declared page stands its picture on that page on the {turned.name} \
screen ({plate.map (sideOf dark ·)}, {pictures} pictures)"
      (pictures ≥ 1 && plate.map (sideOf dark ·) == some ("#" ++ page.toLower))

/-- A declaration's value with every `var(...)` reference cut out: what it
states as itself. -/
def withoutVars (v : String) : String := Id.run do
  let mut out := ""
  let mut depth := 0
  let mut prev := ""
  for c in v.toList do
    if depth > 0 then
      if c == '(' then depth := depth + 1
      else if c == ')' then depth := depth - 1
    else if c == '(' && prev.endsWith "var" then
      out := (out.dropEnd 3).toString
      depth := 1
    else out := out.push c
    prev := prev.push c
  return out

/-- The `#rrggbb` colours a declaration's value states as itself, outside
any `var()` reference. -/
def bareHexes (v : String) : List String :=
  ((withoutVars v).splitOn "#").drop 1 |>.filterMap fun part =>
    let hex := String.ofList (part.toList.take 6)
    if hex.length == 6 && hex.all (fun d => d.isDigit || ('a' ≤ d && d ≤ 'f')) then
      some ("#" ++ hex) else none

mutual

/-- Every inline style of a typed tree outside its pictures, which stand on a
plate of their own. -/
def stylesOutsidePictures (acc : Array String) : Html.Node → Array String
  | .elem t attrs kids =>
    if t == "svg" then acc else
    let acc := match attrs.find? (·.1 == "style") with
      | some (_, st) => acc.push st
      | none => acc
    stylesOutsidePicturesList acc kids.toList
  | .text _ | .style _ | .script _ _ => acc

def stylesOutsidePicturesList (acc : Array String) : List Html.Node → Array String
  | [] => acc
  | n :: rest => stylesOutsidePicturesList (stylesOutsidePictures acc n) rest

end

/-- The scheme properties (`HtmlDoc.schemeVar`) a CSS value reads. -/
def schemeVarReads (v : String) : List String :=
  (v.splitOn "var(--ltx--").drop 1 |>.map fun rest =>
    "--ltx--" ++ (rest.takeWhile fun c => c != ')' && c != ',').toString

/-- **No colour skips its schemes**: on a page that ships a scheme carrying
its colours, every colour a declaration states as itself — in an element's
own style outside a picture, or in a top-level rule of the sheet — is one
every shipped scheme ships as it is (`Ir.Design.literalIn`): a colour that
differs between schemes rides a property its schemes restate
(`HtmlDoc.schemeVar`), so a literal in the tree is a paint site that
bypassed the scheme-aware spelling; and every such property a declaration
reads is one the page states. The plate a picture stands on is the page as
printed, a literal by design. The offences, and how many colours were
read. -/
def literalOffences (doc : Ir.Doc) : Array String × Nat := Id.run do
  let j := Contrast.schemeJudge doc
  let frames := j.frames.filter (!·.home)
  if frames.isEmpty then return (#[], 0)
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  let (root, _) := schemeRoot css .print
  let sheet := (sheetRules css).toList.filterMap fun (conds, sel, decls) =>
    if conds.isEmpty && sel != ":root" then some (sel, decls) else none
  let inline := (stylesOutsidePicturesList #[] body.toList).toList.map ("element", ·)
  let mut out : Array String := #[]
  let mut seen := 0
  let rows := sheet ++ inline
  for (where_, decls) in rows do
    if where_ == "img.see-through, svg.picture" then continue
    for (prop, v) in cssDecls decls do
      if prop.startsWith "--" && !prop.startsWith "--rule" then continue
      -- A colour its schemes' root property states rides them by name.
      for name in schemeVarReads v do
        seen := seen + 1
        if (root.lookup name).isNone then
          out := out.push s!"{where_} {prop}: {name} is read and stated nowhere"
      for hex in bareHexes v do
        let some c := hexColor? hex | continue
        seen := seen + 1
        for f in frames do
          if Ir.Design.literalIn f c != c then
            out := out.push s!"{where_} {prop}: {hex} differs in {f.scheme.name}"
  return (out, seen)

/-- Every corpus page that ships a scheme carrying its colours states no
colour that skips its schemes (`literalOffences`). -/
def literalChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let mut pages := 0
  for (path, doc) in ← corpusTwinDocs do
    pages := pages + 1
    let (offences, _) := literalOffences doc
    t s!"literals: {path} states no colour that skips its schemes: {offences.toList.take 6}"
      offences.isEmpty
  t s!"literals: the corpus is read ({pages})" (pages ≥ 100)
  -- Each paint site a literal reaches, invented: a run, a list marker, a
  -- heading rule, a link hover (a formula's, which a page sets only with its
  -- math face, is the corpus's: `darkTextChecks`).
  let styled (decl body : String) : String :=
    s!"\\documentclass\{article}{decl}\\begin\{document}{body}\\end\{document}"
  for (name, src) in [
      ("a run", styled "" "x \\textcolor[HTML]{1A2433}{y}"),
      ("a list marker", styled "\\style{itemize}{ marker = {\\textcolor[HTML]{1A2433}{>}} }"
        "\\begin{itemize}\\item a\\end{itemize}"),
      ("a heading rule", styled "\\style{section}{ rule = red!50!black }" "\\section{A}b"),
      ("a link hover", styled "\\style{nav}{ hover = red!50!black }" "x")] do
    let (doc, _) := elabStr src
    let (offences, seen) := literalOffences doc
    t s!"literals: {name} rides its schemes ({seen} colours read): {offences.toList}"
      (offences.isEmpty && seen ≥ 1)
  -- An author colour whose name is a hex word reads its own property in
  -- every scheme the page ships, one or five: a scheme property's spelling
  -- (`HtmlDoc.schemeVarTexts`) never reads that name back as a colour.
  for (kind, decl) in [("a one-scheme", "\\output{ schemes = light }"), ("a five-scheme", "")] do
    let (doc, _) := elabStr (styled (decl ++ "\\definecolor{facade}{HTML}{224466}")
      "A \\textcolor{facade}{stone} wall.")
    let (head, body, _) := emitIn {} doc .light
    let css := treeCssList "" head.toList
    t s!"literals: a colour named by a hex word ships as declared on {kind} page"
      ((elemStylesList #[] body.toList).any (fun (shown, st) =>
          hasStr shown "stone" && !hasStr shown "wall" && hasStr st "color: #224466") &&
       !hasStr css "#facade")

/-- The ground a rule paints an element with (`rules`: those whose conditions
hold in the scheme judged), where one of its selectors is a compound
selector the element matches — its tag or none, and classes the element
holds — or one standing on its parent's, the last such rule's. -/
def ruleGround (rules : List (String × List (String × String))) (tag : String)
    (classes : List String) (parent : String × List String) (prop : String := "background") :
    Option String :=
  let compound (part t : String) (cs : List String) : Bool :=
    !part.contains ' ' && !part.contains ':' && !part.contains '[' &&
    match part.splitOn "." with
    | t' :: need => (t'.isEmpty || t' == t) && (t' == t || !need.isEmpty) && need.all cs.contains
    | [] => false
  rules.foldl (fun acc (sel, decls) =>
    let fits := (cssSelParts sel).any fun part =>
      match part.splitOn " > " with
      | [one] => compound one.trimAscii.toString tag classes && (one.splitOn ".").length > 1
      | [up, one] => compound up.trimAscii.toString parent.1 parent.2 &&
          compound one.trimAscii.toString tag classes
      | _ => false
    if fits then (lastDecl decls prop).orElse fun _ => acc else acc) none

mutual

/-- Each text of a typed tree with what paints it: the custom properties in
scope, the colour value the nearest element states (its own `color` or its
token class's), the nearest ground an element states (its `background`, or
a rule of the sheet's, `ruleGround`; a transparent one reads through), and
whether it stands as large-scale text — in a heading or on a deck's stage —
skipping pictures, which stand on a plate of their own. -/
def textPaintsOne (classes : List (String × String)) (rules : List (String × List (String × String)))
    (parent : String × List String)
    (vars : List (String × String)) (color ground : Option String) (large : Bool)
    (acc : Array (List (String × String) × Option String × Option String × Bool × String)) :
    Html.Node → Array (List (String × String) × Option String × Option String × Bool × String)
  | .elem tag attrs kids =>
    if tag == "svg" then acc else
    let style := ((attrs.find? (·.1 == "style")).map (·.2)).getD ""
    let cls := ((attrs.find? (·.1 == "class")).map (·.2)).getD ""
    let vars := styleVars style ++ vars
    let decls := cssDecls style
    let cs := cls.splitOn " "
    let token := cs.findSome? (classes.lookup ·)
    let ownInk := ((lastDecl decls "color").or (ruleGround rules tag cs parent "color")).filter
      (!inherits ·)
    let color := (token.or ownInk).or color
    let ground := (((lastDecl decls "background").or (ruleGround rules tag cs parent)).filter
      fun v => v != "transparent" && v != "none").or ground
    let large := large || ["h1", "h2", "h3", "h4"].contains tag
    textPaintsList classes rules (tag, cs) vars color ground large acc kids.toList
  | .text x =>
    if x.trimAscii.isEmpty then acc else acc.push (vars, color, ground, large, x)
  | .style _ | .script _ _ => acc

def textPaintsList (classes : List (String × String)) (rules : List (String × List (String × String)))
    (parent : String × List String)
    (vars : List (String × String)) (color ground : Option String) (large : Bool)
    (acc : Array (List (String × String) × Option String × Option String × Bool × String)) :
    List Html.Node → Array (List (String × String) × Option String × Option String × Bool × String)
  | [] => acc
  | n :: rest => textPaintsList classes rules parent vars color ground large
      (textPaintsOne classes rules parent vars color ground large acc n) rest

end

/-- Each text a typed tree paints, as one scheme's cascade reads it: its
words, and either the colour and ground it reads in there — its stated
colour, else the page's ink, on the nearest ground an element states, else
the page (`schemeRoot`, `schemeRead`) — or the value no cascade reads; with
that scheme's gate for its size (`Contrast.requiredIn`: large-scale in a
heading or on a deck's stage). A colour the document declares decorative is
skipped, as the report exempts it. -/
def schemeReadings (doc : Ir.Doc) (css : String) (body : Array Html.Node) (s : Ir.Scheme) :
    Array (String × Except String (Ir.Color × Ir.Color) × Nat) := Id.run do
  let classes := tokenClassColors css
  let decorative := doc.palette.decorative.toList.map (·.property)
  let rules := (sheetRules css).toList.filterMap fun (conds, sel, decls) =>
    if conds.all (holdsIn s ·) then some (sel, cssDecls decls) else none
  let (root, dark) := schemeRoot css s
  let read (vars : List (String × String)) (v : String) : Option Ir.Color :=
    hexColor? (schemeRead dark vars v)
  let some page := read root s!"var({HtmlDoc.roleVar .page})" | return #[]
  let mut out := #[]
  for (vars, color, ground, large, shown) in
      textPaintsList classes rules ("body", []) root none none (Contrast.stageOf doc) #[]
        body.toList do
    let v := color.getD s!"var({HtmlDoc.roleVar .ink})"
    if decorative.any (hasStr v ·) then continue
    let text := (shown.trimAscii.toString.take 20).toString
    let gate := Contrast.requiredIn s (if large then .largeText else .text)
    -- A text the cascade cannot read is an offence, not a pass.
    let reading := match read vars v, ground.map (read vars) with
      | none, _ => .error v
      | _, some none => .error (ground.getD "")
      | some c, g => .ok (c, (g.join).getD page)
    out := out.push (text, reading, gate)
  return out

/-- **The owed contract, over the artifact: a scheme that ships has every
pair it paints at its gate.** For every scheme a page ships other than the
ones its colours were declared for, every text the typed tree paints reads,
as that scheme's cascade gives its colour and ground (`schemeReadings`), at
that scheme's gate for its size, and none is left unread. The offences, by
scheme; `edit` doctors the sheet, so a check can break the page and see the
contract fall, and `also` names schemes the colours were declared for to
judge as well, where they are known to read. -/
def schemeContractOffences (doc : Ir.Doc) (edit : String → String := id)
    (also : List Ir.Scheme := []) : Array String := Id.run do
  let j := Contrast.schemeJudge doc
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let css := edit (treeCssList "" head.toList)
  let mut out : Array String := #[]
  for f in j.frames do
    if f.home && !also.contains f.scheme then continue
    for (text, reading, gate) in schemeReadings doc css body f.scheme do
      match reading with
      | .error v => out := out.push s!"{f.scheme.name}: '{text}' in {v}, which no scheme reads"
      | .ok (c, g) =>
        if Contrast.contrastMilli c g < gate then
          out := out.push s!"{f.scheme.name}: '{text}' {c.css} on {g.css} at \
{Contrast.contrastMilli c g} (gate {gate})"
  return out

/-- **More contrast keeps what already meets it** (spec §6: passing roles
stay): in each more-contrast scheme a page ships beside its plain screen,
every text that already reads at the more-contrast gate on the plain screen
reads at least as high there — a ground moved for one colour once paled a
deck's every frame-title bar, its titles still above the gate. The
offences. -/
def moreKeepsOffences (doc : Ir.Doc) : Array String := Id.run do
  let j := Contrast.schemeJudge doc
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  let mut out : Array String := #[]
  for (more, plain) in [(Ir.Scheme.lightMore, Ir.Scheme.light), (.darkMore, .dark)] do
    unless j.shipped.contains more && j.shipped.contains plain do continue
    let ms := schemeReadings doc css body more
    let ps := schemeReadings doc css body plain
    for ((text, m, gate), (_, p, _)) in ms.zip ps do
      match m, p with
      | .ok (mc, mg), .ok (pc, pg) =>
        let before := Contrast.contrastMilli pc pg
        let after := Contrast.contrastMilli mc mg
        if gate ≤ before && after < before then
          out := out.push s!"{more.name}: '{text}' {after} where {plain.name} reads {before}"
      | _, _ => pure ()
  return out

/-- The sheet without its blocks under one condition (`prelude`), each to its
matching brace. -/
def dropBlocks (prelude css : String) : String :=
  match css.splitOn prelude with
  | [] => css
  | first :: rest => rest.foldl (fun out p =>
      let (_, _, kept) := p.toList.foldl (fun ((phase, depth, kept) : Nat × Nat × String) c =>
        if phase == 2 then (2, depth, kept.push c)
        else if c == '{' then (1, depth + 1, kept)
        else if c == '}' then (if depth == 1 then 2 else 1, depth - 1, kept)
        else (phase, depth, kept)) (0, 0, "")
      out.append kept) first

def contractChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (path, doc) in ← corpusTwinDocs do
    let offences := schemeContractOffences doc
    t s!"scheme contract: {path} paints every pair at its scheme's gate: {offences.toList.take 6}"
      offences.isEmpty
    let lowered := moreKeepsOffences doc
    t s!"scheme contract: {path} keeps under more contrast what already meets it: \
{lowered.toList.take 6}" lowered.isEmpty
  let deck (pre body : String) : Ir.Doc := (elabStr (dvDeck pre body)).1
  -- moloch's ink and its frame-title bar are one colour, so a run on the bar
  -- names its ground by role, not by colour: the alert is judged on the bar.
  -- One tone of it serves the page and another the bar, but none both, so
  -- the more-contrast screen drops, named, and the bar keeps its colour.
  let barAlert := deck "\\theme{moloch}"
    "\\begin{frame}{Tide \\alert{Table}}Words. \\alert{Low water.}\\end{frame}"
  let barJudge := Contrast.schemeJudge barAlert
  t s!"scheme contract: an alert on moloch's bar and page drops the more-contrast screen, \
named: {schemeContractOffences barAlert |>.toList} {barJudge.diags.map (·.subject)}"
    ((schemeContractOffences barAlert).isEmpty && !barJudge.shipped.contains .lightMore &&
     barJudge.diags.any fun d => d.subject.any (·.startsWith "lightMore:alert@"))
  -- A colour one tone serves on a declared bar and another on the page moves
  -- no bar: every other title keeps its contrast.
  let conflict := deck
    "\\setbeamercolor{frametitle}{bg=#2E4A62, fg=white}\\definecolor{moss}{HTML}{3F7A3A}"
    ("\\begin{frame}{Kites and \\textcolor{moss}{moss}}Words. " ++
     "\\textcolor{moss}{Moss.}\\end{frame}\\begin{frame}{Second frame}More words.\\end{frame}")
  t s!"scheme contract: a colour no one tone serves on a bar and the page moves no bar: \
{moreKeepsOffences conflict |>.toList} {schemeContractOffences conflict |>.toList}"
    ((moreKeepsOffences conflict).isEmpty && (schemeContractOffences conflict).isEmpty)
  -- A code colour the rule derives that already meets the more-contrast
  -- gate on a standout frame's ground stays as it is there.
  let standoutCode := deck "\\usepackage{minted}"
    ("\\begin{frame}{Code}\n\\begin{minted}{python}\ndef f(x):\n    return x\n\\end{minted}\n" ++
     "\\end{frame}\n\\begin{frame}[standout]\n\\begin{minted}{python}\nreturn 3\n" ++
     "\\end{minted}\n\\end{frame}")
  t s!"scheme contract: more contrast lowers no derived code colour that meets it: \
{moreKeepsOffences standoutCode |>.toList}"
    ((moreKeepsOffences standoutCode).isEmpty &&
     (Contrast.schemeJudge standoutCode).shipped.contains .lightMore)
  -- A listing on a ground of its own inside an epoch states its code roles
  -- itself: the epoch's restatement stands for the epoch's own code ground.
  let (panel, _) := elabStr ("\\documentclass{article}\\usepackage{minted}" ++
    "\\palette{ codekeyword = #7A2E8E }\\begin{document}Words.\n\n" ++
    "\\palette{ bg = #1C2228, fg = #E4E6E8 }Dark words.\n" ++
    "\\begin{minted}[bgcolor=white]{python}\ndef f(x):\n    return x\n\\end{minted}\n" ++
    "\\end{document}")
  t s!"scheme contract: a listing on its own ground in an epoch reads its own code roles: \
{schemeContractOffences panel |>.toList}"
    ((schemeContractOffences panel).isEmpty &&
     (Contrast.schemeJudge panel).shipped == Ir.Scheme.all)
  -- A palette declared in one frame lasts into the next, whose own ink then
  -- stands on that frame's dark ground: its foot and words are read there.
  let epochs := deck ""
    ("\\begin{frame}{One}Words.\\end{frame}" ++
     "\\begin{frame}{Two}\\palette{ bg = #1E2E36, fg = #E6E6E6 }Pale words.\\end{frame}" ++
     "\\begin{frame}{Three}\\palette{ fg = #686868 }Grey words.\\end{frame}")
  t s!"scheme contract: a later frame's ink on an earlier epoch's ground reads there: \
{schemeContractOffences epochs |>.toList}"
    ((schemeContractOffences epochs).isEmpty &&
     (Contrast.schemeJudge epochs).shipped.contains .lightMore)
  -- A bar declared between frames paints the frames after it in the web
  -- page as on paper, in every scheme: the title it stands under reads on
  -- it. With no bar in the opening palette, the page once painted none.
  let barEpoch := deck ""
    ("\\begin{frame}{One}Words.\\end{frame}" ++
     "\\setbeamercolor{frametitle}{bg=teal!70!black, fg=white}" ++
     "\\begin{frame}{Two}Words.\\end{frame}")
  let barOffences := schemeContractOffences barEpoch (also := [.print, .light])
  t s!"scheme contract: a bar declared between frames stands under the title it carries: \
{barOffences.toList}"
    (barOffences.isEmpty && (Contrast.schemeJudge barEpoch).shipped.contains .lightMore)
  -- An epoch whose seeds generate nothing at the more-contrast gates — a
  -- grey ink no derived tone keeps 7:1 from — is carried as declared
  -- colours are, so the scheme ships, its frames legible.
  let greyEpoch := deck ""
    ("\\begin{frame}{One}Words.\\end{frame}" ++
     "\\setbeamercolor{normal text}{fg=black!65}" ++
     "\\begin{frame}{Two}Grey words. \\alert{An alert.}\\end{frame}")
  let greySeeds := (Contrast.docPalettes greyEpoch).filter fun p => p.seeded.isSome &&
    (p.seeded.bind (Ir.Design.carrySeeds · p.classColors.depth .lightMore false)).isNone
  t s!"scheme contract: an epoch whose seeds generate nothing there is carried as declared \
({greySeeds.length} such): {schemeContractOffences greyEpoch |>.toList}"
    (!greySeeds.isEmpty && (schemeContractOffences greyEpoch).isEmpty &&
     (Contrast.schemeJudge greyEpoch).shipped.contains .lightMore)
  -- The judge breaks once: without its more-contrast blocks, a page's more
  -- schemes read the AA colours, which the 7:1 gate refuses.
  let (aa, _) := elabStr
    "\\documentclass{article}\\palette{ fg = #767676 }\\begin{document}Words.\\end{document}"
  let broken := schemeContractOffences aa (dropBlocks "@media (prefers-contrast: more)")
  t s!"scheme contract: an AA ink shipped as more contrast falls: {broken.toList.take 2}"
    ((schemeContractOffences aa).isEmpty && broken.any (·.startsWith "lightMore:") &&
     broken.any (·.startsWith "darkMore:"))

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
    (["section.slide > header", "section.slide.standout", "section.block > header",
      "section.tcolorbox > header"].all sels.contains)
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
