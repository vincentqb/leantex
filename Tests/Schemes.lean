module

public import Tests.Support
public import LeanTex.Core.ContrastSolve

public section

open LeanTex.Core

namespace Tests.Schemes

/-- ΔEOK between two colours, in thousandths. -/
private def deltaEMilli (a b : Ir.Color) : Nat :=
  (Nat.sqrt (ContrastSolve.deltaEOkSq a b).toNat) / 10 ^ 15

/-- The dark screen is the class's seeds carried to a dark page, each colour within ΔEOK 0.03 of a
fixed reference constant. -/
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
      t s!"the dark {(Ir.ColorRef.role r).key} {d.css} stands within ΔEOK 0.03 of the reference {c.css}"
        (deltaEMilli d c ≤ 30)
    | none => t s!"the dark {(Ir.ColorRef.role r).key} resolves" false

/-- A scheme that cannot carry a colour is dropped and named once (W0308). -/
def dropChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, said) := elabStr (dvDoc "\\palette{ bg = #767676, fg = #777777 }\n" "x")
  let j := Contrast.schemeJudge doc
  t s!"mid-grey ink on a mid-grey page ships every scheme but the more-contrast light one ({j.shipped.map (·.name)})"
    (j.shipped == [.print, .light, .dark, .darkMore] && j.dropped.map (·.1) == [.lightMore])
  let named := j.diags.filter (·.code == "W0308")
  t "the uncarried colour is named once, under its subject"
    (named.size == 1 && named.all (·.subject == some "lightMore:fg@bg"))
  t "the page's HTML names it too"
    ((HtmlDoc.emit {} doc).2.any fun d => d.code == "W0308")
  t "as-declared colours are named by the report, not W0308"
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
  let (boxed, _) := elabStr (dvDoc "\\palette{ alert = #FFFFFF }\n" "x \\colorbox{black}{\\textcolor{alert}{y}}")
  let boxedKeys := (Contrast.schemeJudge boxed).diags.filterMap (·.subject)
  t s!"a palette colour only a box's literal ground carries is judged on that ground ({boxedKeys})"
    (boxedKeys.any (·.endsWith "alert@#000000") &&
      !boxedKeys.any fun k => hasStr k "alert@bg" || hasStr k "alert@fg")
  let (twoGrounds, _) := elabStr (dvDoc "\\palette{ alert = #FFFFFF }\n"
    "x \\colorbox{black}{\\textcolor{alert}{y}} \\colorbox{blue}{\\textcolor{alert}{z}}")
  let twoKeys := (Contrast.schemeJudge twoGrounds).diags.filterMap (·.subject)
  t s!"a palette colour failing on two grounds is named on each ({twoKeys})"
    (twoKeys.any (·.endsWith "dark:alert@#000000") && twoKeys.any (·.endsWith "dark:alert@#0000FF"))
  let (unpaintedGround, _) := elabStr (dvDoc "\\palette{ bg = #767676, fg = #000000, alert = #FFFFFF }\n"
    "x \\colorbox{black}{\\textcolor{alert}{y}}")
  t s!"a palette colour is never judged on a ground no text it colours stands on ({(Contrast.schemeJudge unpaintedGround).diags.filterMap (·.subject)})"
    (!((Contrast.schemeJudge unpaintedGround).diags.any fun d => d.subject.any (hasStr · "alert@bg")))
  let (plain, _) := elabStr (dvDoc "" "x")
  t "an undeclared document ships every scheme"
    ((Contrast.schemeJudge plain).shipped == Ir.Scheme.all)
  let (deck, _) := elabStr (dvDeck "" "\\begin{frame}{T}\nx\n\\end{frame}")
  t "a deck ships its print, its own screen and that screen's more contrast"
    ((Contrast.schemeJudge deck).shipped == [.print, .light, .lightMore])


mutual

/-- Each listing box of a typed tree with the custom properties in scope at it and its own style. -/
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

/-- A colour a CSS value spells `#rrggbb`. -/
def hexColor? (v : String) : Option Ir.Color :=
  if v.length == 7 && v.startsWith "#" then
    (({} : Ir.Palette).resolveSource none v).toOption.join
  else none

/-- Whether a colour reads as a dark ground: more against white than black. -/
def darkGround (c : Ir.Color) : Bool :=
  decide (Contrast.contrastMilli c Ir.Color.black < Contrast.contrastMilli c Ir.Color.white)

/-- The listing boxes whose ground or tokens fall below `req` under scheme `s`'s cascade, or whose
ground is not dark where `darkOnly` asks. -/
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

/-- Under the dark screen every corpus listing stands on a dark ground, every token at 4.5:1 or more
on it. -/
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

/-- A colour value taking the colour around the element: `inherit`, or `currentColor`. -/
def inherits (v : String) : Bool := v == "inherit" || v.toLower == "currentcolor"

mutual

/-- What a typed tree paints: each ground, and each text's colour with its properties in scope and
whether it stands on a stated ground or a picture. -/
def paintedOne (classes : List (String × String)) (vars : List (String × String))
    (color : Option String) (grounded : Bool)
    (acc : Array (List (String × String) × String × Bool × String × Bool)) :
    Html.Node → Array (List (String × String) × String × Bool × String × Bool)
  | .elem tag attrs kids =>
    let style := ((attrs.find? (·.1 == "style")).map (·.2)).getD ""
    let cls := ((attrs.find? (·.1 == "class")).map (·.2)).getD ""
    let vars := styleVars style ++ vars
    let decls := cssDecls style
    -- clipped to nothing, an element paints nothing
    if lastDecl decls "clip-path" == some "inset(50%)" then acc else
    let color := ((cls.splitOn " ").findSome? (classes.lookup ·)).orElse fun _ =>
      ((lastDecl decls "color").filter (!inherits ·)).orElse fun _ => color
    -- A picture stands on its own plate on a dark screen (the stylesheet's `svg.picture` rule), its labels with it.
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

/-- The colours a shipped page paints text in and fills with. -/
def shippedColors (out : Layout.Out) : Array Ir.Color × Array Ir.Color :=
  let add (acc : Array Ir.Color) (c : Ir.Color) := if acc.contains c then acc else acc.push c
  let segs := out.pages.flatMap fun p => p.lines.flatMap (·.segs)
  let inks := segs.foldl (fun acc s => match s with
    | .run _ c _ _ glyphs .. => if glyphs.isEmpty then acc else add acc c
    | .gap .. | .decoratedGap .. | .decoration .. | .rule .. | .image .. | .poly .. => acc) #[]
  let marks := segs.foldl (fun acc s => match s with
    | .decoration _ _ _ _ c _ | .rule _ _ _ c _ | .poly _ c => add acc c
    | .run .. | .gap .. | .decoratedGap .. | .image .. => acc) #[]
  (inks, out.pages.foldl (fun acc p => p.fills.foldl (fun acc f => add acc f.color) acc) marks)

/-- What the printed web page paints that the PDF does not: text colours and grounds under the print
cascade. -/
def printOffences (fonts : Font.FontSet) (doc : Ir.Doc) (more : Bool := false) :
    Array String := Id.run do
  let (inks, fills) := shippedColors (layoutOf fonts doc (Layout.Geom.ofPage doc.page))
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  -- the margin outline is a screen's alone: paper sets it `display: none`
  let body := if hasStr css s!"nav.{HtmlDoc.outlineClass} \{ display: none;" then
      body.filter fun n => match n with
        | .elem "nav" attrs _ => !(HtmlDoc.classTokens attrs).contains HtmlDoc.outlineClass
        | _ => true
    else body
  let (root, dark) := schemeRoot css .print more
  let rules := sheetRules css
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

/-- On every corpus page that ships print, the printed web page's colours are the PDF's. -/
def printChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let mathSet ← mathSetOf fonts
  let shipped ← LeanTex.Cli.FontDiscovery.scanRoots [testFonts]
  let mut pages := 0
  for (path, doc) in ← corpusTwinDocs do
    if !(Contrast.schemeJudge doc).shipped.contains .print then continue
    pages := pages + 1
    -- Faces resolved as the driver resolves them: a formula in a face with no math sets the PDF's colour.
    let fs ← fixtureFontSet fonts mathSet shipped doc
    let offences := printOffences fs doc
    t s!"print colours: {path} paints what its PDF paints: {offences.toList}" offences.isEmpty
    -- A reader who asks more contrast prints with that block in force.
    let more := printOffences fs doc (more := true)
    t s!"print colours: {path} paints what its PDF paints under more contrast: {more.toList}"
      more.isEmpty
  t s!"print colours: the corpus's pages ship print ({pages})" (pages ≥ 50)
  let shown := (paintedList [] [] (some "#123456") false #[]
    [Html.elem "span" #[Html.text "hidden"] #[("style", HtmlDoc.visuallyHidden)],
     Html.elem "span" #[Html.text "shown"]]).map fun (_, _, _, s, _) => s
  t s!"print colours: a box clipped to nothing paints nothing, and its unclipped twin paints: {shown}"
    (shown == #["shown"])

/-- On the dark screen every colour a text states reads at 4.5:1 or more on the page; the
offences. -/
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

/-- Each scheme a reader asks for reads what the page ships for it, under every declared list of
schemes. -/
def subsetChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let extra : List Ir.Scheme := [.dark, .lightMore, .darkMore]
  let subsets : List (List Ir.Scheme) := (List.range 8).map fun m =>
    (List.range 3).filterMap fun i => if m / 2 ^ i % 2 == 1 then extra[i]? else none
  let docs := (subsets.map fun sub =>
      let list := String.intercalate ", " (([Ir.Scheme.print, .light] ++ sub).map (·.name))
      (list, dvDoc s!"\\palette\{ fg = #6E6E6E, bg = #FBFBFB }\n\\output\{ schemes = {list} }\n" "x")) ++
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

/-- A picture stands on its document's page wherever the screen turns over. -/
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

/-- A declaration's value with every `var(...)` reference cut out. -/
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

/-- The `#rrggbb` colours a value states outside any `var()` reference. -/
def bareHexes (v : String) : List String :=
  ((withoutVars v).splitOn "#").drop 1 |>.filterMap fun part =>
    let hex := String.ofList (part.toList.take 6)
    if hex.length == 6 && hex.all (fun d => d.isDigit || ('a' ≤ d && d ≤ 'f')) then
      some ("#" ++ hex) else none

mutual

/-- Every inline style of a typed tree outside its pictures. -/
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

/-- No colour skips its schemes: every literal colour a page states is one every shipped scheme
ships as is; the offences and the count read. -/
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

/-- Every corpus page that ships a scheme carrying its colours states no colour that skips its
schemes. -/
def literalChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let mut pages := 0
  for (path, doc) in ← corpusTwinDocs do
    pages := pages + 1
    let (offences, _) := literalOffences doc
    t s!"literals: {path} states no colour that skips its schemes: {offences.toList.take 6}"
      offences.isEmpty
  t s!"literals: the corpus is read ({pages})" (pages ≥ 100)
  let styled (decl body : String) : String :=
    s!"\\documentclass\{article}{decl}\\begin\{document}{body}\\end\{document}"
  for (name, src) in [
      ("a run", styled "" "x \\textcolor[HTML]{1A2433}{y}"),
      ("a list marker", styled "\\style{itemize}{ marker = {\\textcolor[HTML]{1A2433}{>}} }"
        "\\begin{itemize}\\item a\\end{itemize}"),
      ("a heading rule", styled "\\style{section}{ rule = red!50!black }" "\\section{A}b"),
      ("a link hover", styled "\\style{nav}{ hover = red!50!black }"
        "\\begin{nav}\\href{https://example.org}{Link}\\end{nav}")] do
    let (doc, _) := elabStr src
    let (offences, seen) := literalOffences doc
    t s!"literals: {name} rides its schemes ({seen} colours read): {offences.toList}"
      (offences.isEmpty && seen ≥ 1)
  for (kind, decl) in [("a one-scheme", "\\output{ schemes = light }"), ("a five-scheme", "")] do
    let (doc, _) := elabStr (styled (decl ++ "\\definecolor{facade}{HTML}{224466}")
      "A \\textcolor{facade}{stone} wall.")
    let (head, body, _) := emitIn {} doc .light
    let css := treeCssList "" head.toList
    t s!"literals: a colour named by a hex word ships as declared on {kind} page"
      ((elemStylesList #[] body.toList).any (fun (shown, st) =>
          hasStr shown "stone" && !hasStr shown "wall" && hasStr st "color: #224466") &&
       !hasStr css "#facade")

/-- The ground the last matching rule of `rules` paints an element with, by tag and classes or by
its parent's selector. -/
def ruleGround (rules : List (String × List (String × String))) (tag : String)
    (classes : List String) (parent : String × List String) (prop : String := "background") :
    Option String :=
  let compound (part t : String) (cs : List String) : Bool :=
    !part.contains ' ' && !part.contains ':' && !part.contains '[' &&
    match part.splitOn "." with
    | t' :: need => (t'.isEmpty || t' == t) && (t' == t || !need.isEmpty) && need.all cs.contains
    | [] => false
  rules.foldl (fun acc (sel, decls) =>
    let fits := (cssSelectorParts sel).any fun part =>
      match part.splitOn " > " with
      | [one] => compound one.trimAscii.toString tag classes && (one.splitOn ".").length > 1
      | [up, one] => compound up.trimAscii.toString parent.1 parent.2 &&
          compound one.trimAscii.toString tag classes
      | _ => false
    if fits then (lastDecl decls prop).orElse fun _ => acc else acc) none

mutual

/-- Each text of a typed tree with its properties in scope, nearest stated colour and ground, and
whether it is large-scale, pictures skipped. -/
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

/-- Each text a typed tree paints as one scheme's cascade reads it, with that scheme's gate for its
size; decorative colours skipped. -/
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

/-- Every pair a shipped scheme paints reads at its gate, none unread; the offences by scheme,
`edit` doctoring the sheet. -/
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

/-- More contrast keeps what already meets it: no text at the gate on the plain screen reads lower
in its more scheme. -/
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

/-- The sheet without its blocks under condition `prelude`. -/
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
  -- moloch's ink and bar are one colour, so no one tone serves both and the more-contrast screen drops.
  let barAlert := deck "\\theme{moloch}"
    "\\begin{frame}{Tide \\alert{Table}}Words. \\alert{Low water.}\\end{frame}"
  let barJudge := Contrast.schemeJudge barAlert
  t s!"scheme contract: an alert on moloch's bar and page drops the more-contrast screen, named: {schemeContractOffences barAlert |>.toList} {barJudge.diags.map (·.subject)}"
    ((schemeContractOffences barAlert).isEmpty && !barJudge.shipped.contains .lightMore &&
     barJudge.diags.any fun d => d.subject.any (·.startsWith "lightMore:alert@"))
  let conflict := deck
    "\\setbeamercolor{frametitle}{bg=#2E4A62, fg=white}\\definecolor{moss}{HTML}{3F7A3A}"
    ("\\begin{frame}{Kites and \\textcolor{moss}{moss}}Words. " ++
     "\\textcolor{moss}{Moss.}\\end{frame}\\begin{frame}{Second frame}More words.\\end{frame}")
  t s!"scheme contract: a colour no one tone serves on a bar and the page moves no bar: \
{moreKeepsOffences conflict |>.toList} {schemeContractOffences conflict |>.toList}"
    ((moreKeepsOffences conflict).isEmpty && (schemeContractOffences conflict).isEmpty)
  let standoutCode := deck "\\usepackage{minted}"
    ("\\begin{frame}{Code}\n\\begin{minted}{python}\ndef f(x):\n    return x\n\\end{minted}\n" ++
     "\\end{frame}\n\\begin{frame}[standout]\n\\begin{minted}{python}\nreturn 3\n" ++
     "\\end{minted}\n\\end{frame}")
  t s!"scheme contract: more contrast lowers no derived code colour that meets it: \
{moreKeepsOffences standoutCode |>.toList}"
    ((moreKeepsOffences standoutCode).isEmpty &&
     (Contrast.schemeJudge standoutCode).shipped.contains .lightMore)
  let (panel, _) := elabStr ("\\documentclass{article}\\usepackage{minted}" ++
    "\\palette{ codekeyword = #7A2E8E }\\begin{document}Words.\n\n" ++
    "\\palette{ bg = #1C2228, fg = #E4E6E8 }Dark words.\n" ++
    "\\begin{minted}[bgcolor=white]{python}\ndef f(x):\n    return x\n\\end{minted}\n" ++
    "\\end{document}")
  t s!"scheme contract: a listing on its own ground in an epoch reads its own code roles: \
{schemeContractOffences panel |>.toList}"
    ((schemeContractOffences panel).isEmpty &&
     (Contrast.schemeJudge panel).shipped == Ir.Scheme.all)
  let epochs := deck ""
    ("\\begin{frame}{One}Words.\\end{frame}" ++
     "\\begin{frame}{Two}\\palette{ bg = #1E2E36, fg = #E6E6E6 }Pale words.\\end{frame}" ++
     "\\begin{frame}{Three}\\palette{ fg = #686868 }Grey words.\\end{frame}")
  t s!"scheme contract: a later frame's ink on an earlier epoch's ground reads there: \
{schemeContractOffences epochs |>.toList}"
    ((schemeContractOffences epochs).isEmpty &&
     (Contrast.schemeJudge epochs).shipped.contains .lightMore)
  let barEpoch := deck ""
    ("\\begin{frame}{One}Words.\\end{frame}" ++
     "\\setbeamercolor{frametitle}{bg=teal!70!black, fg=white}" ++
     "\\begin{frame}{Two}Words.\\end{frame}")
  let barOffences := schemeContractOffences barEpoch (also := [.print, .light])
  t s!"scheme contract: a bar declared between frames stands under the title it carries: \
{barOffences.toList}"
    (barOffences.isEmpty && (Contrast.schemeJudge barEpoch).shipped.contains .lightMore)
  let greyEpoch := deck ""
    ("\\begin{frame}{One}Words.\\end{frame}" ++
     "\\setbeamercolor{normal text}{fg=black!65}" ++
     "\\begin{frame}{Two}Grey words. \\alert{An alert.}\\end{frame}")
  let greySeeds := (Contrast.docPalettes greyEpoch).filter fun p => p.seeded.isSome &&
    (p.seeded.bind (Ir.Design.carrySeeds · p.classColors.depth .lightMore false)).isNone
  t s!"scheme contract: an epoch whose seeds generate nothing is carried as declared ({greySeeds.length} such): {schemeContractOffences greyEpoch |>.toList}"
    (!greySeeds.isEmpty && (schemeContractOffences greyEpoch).isEmpty &&
     (Contrast.schemeJudge greyEpoch).shipped.contains .lightMore)
  -- The judge breaks once: without the more-contrast blocks the 7:1 gate refuses the AA colours.
  let (aa, _) := elabStr
    "\\documentclass{article}\\palette{ fg = #767676 }\\begin{document}Words.\\end{document}"
  let broken := schemeContractOffences aa (dropBlocks "@media (prefers-contrast: more)")
  t s!"scheme contract: an AA ink shipped as more contrast falls: {broken.toList.take 2}"
    ((schemeContractOffences aa).isEmpty && broken.any (·.startsWith "lightMore:") &&
     broken.any (·.startsWith "darkMore:"))

/-- High-contrast mode draws the bars the colours drew, with `CanvasText` borders on elements the
typed tree holds. -/
def forcedColorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, _) := elabStr (dvDeck "" ("\\begin{frame}{Bar}\\begin{block}{Band}x\\end{block}\\end{frame}" ++
    "\\begin{frame}[standout]Out\\end{frame}"))
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let css := treeCssList "" head.toList
  let forced := (sheetRules css).toList.filter fun (conds, _, decls) =>
    conds == ["@media (forced-colors: active)"] && hasStr decls "CanvasText"
  let sels := forced.flatMap fun (_, sel, _) => cssSelectorParts sel
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
