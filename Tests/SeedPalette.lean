module

public import Tests.Support
public import Tests.Artifact
public import LeanTex.Core.SeedPalette
public import LeanTex.Cli.RunBounded

public section

open LeanTex.Core
open LeanTex.Cli
open LeanTex.Cli.World

/-! A palette generated from its seeds: the generator over invented triples
in both polarities, the deck the native `\palette[seeds]` sets in both
artifacts, the export a TeX build reads, and the script that writes it. -/

namespace Tests.SeedPalette

private def hex (s : String) : Ir.Color :=
  match Decl.parseColorSpec (some "HTML") s with
  | .ok (.html r g b) => { r, g, b }
  | _ => Ir.Color.black

private def lchOf (c : Ir.Color) : Int × Int :=
  let l := Oklab.labOf c
  (Nat.sqrt (Oklab.chromaSq l).toNat, Oklab.hueMilli l.a l.b)

/-- Millidegrees between two hues, the short way round. -/
private def hueGap (h h' : Int) : Int :=
  let d := (h - h' + 540000) % 360000 - 180000
  if d < 0 then -d else d

private def generate (s : LeanTex.Core.SeedPalette.Seeds) (d : Ir.GroundDepth := .decks) :=
  LeanTex.Core.SeedPalette.generate s (s.targets d)

/-- The invented deck's seeds. -/
def deckSeeds : LeanTex.Core.SeedPalette.Seeds :=
  { ink := hex "2B2440", paper := hex "FFFFFF", accent := hex "E85D2A" }

/-- Invented triples, each generating a palette or naming the role that
cannot meet what its sites owe: an achromatic ink beside a blue accent, a
warm ink on cream beside teal, dark papers, a yellow and an amber accent, a
low-chroma accent, and seeds too close to read. -/
def tripleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let ok : List (String × LeanTex.Core.SeedPalette.Seeds) := [
    ("invented deck", deckSeeds),
    ("achromatic ink, blue accent", { ink := hex "1A1A1A", paper := hex "FFFFFF", accent := hex "2563EB" }),
    ("warm ink on cream, teal accent", { ink := hex "3B2F2A", paper := hex "FBF6EC", accent := hex "0D9488" }),
    ("dark paper, amber accent", { ink := hex "F4F1EA", paper := hex "1B2430", accent := hex "F2A541" }),
    ("dark paper, blue accent", { ink := hex "E8EEF6", paper := hex "10151C", accent := hex "4F8EF7" }),
    ("yellow accent", { ink := hex "1C1917", paper := hex "FFFFFF", accent := hex "FACC15" }),
    ("amber accent", { ink := hex "1C1917", paper := hex "FFFFFF", accent := hex "F59E0B" }),
    ("low-chroma accent", { ink := hex "202020", paper := hex "FFFFFF", accent := hex "8A8F99" }),
    ("magenta accent", { ink := hex "241B2F", paper := hex "FFFFFF", accent := hex "C026D3" }),
    ("green accent", { ink := hex "14281D", paper := hex "FFFFFF", accent := hex "16A34A" }),
    ("pale accent", { ink := hex "1E293B", paper := hex "FFFFFF", accent := hex "FDE68A" }),
    ("grey everything", { ink := hex "000000", paper := hex "FFFFFF", accent := hex "777777" }),
    ("named alert and example",
      { ink := hex "2B2440", paper := hex "FFFFFF", accent := hex "E85D2A",
        alert := some (hex "D9254C"), exampleColor := some (hex "1F8A70") })]
  for (name, s) in ok do
    for d in [Ir.GroundDepth.documents, .decks] do
      match generate s d with
      | .error f =>
        t s!"seeds {name} ({d.body}): generate, not fail at {reprStr f.role}: {f.detail}" false
      | .ok g =>
        let c := g.colors
        t s!"seeds {name}: the seeds ship exactly"
          (LeanTex.Core.SeedPalette.Colors.role s c .ink == some s.ink &&
            LeanTex.Core.SeedPalette.Colors.role s c .page == some s.paper &&
            LeanTex.Core.SeedPalette.Colors.role s c .accent == some s.accent)
        t s!"seeds {name}: surface, band and rule stand in that order from the page"
          (Contrast.contrastMilli c.surface s.paper < Contrast.contrastMilli c.surfaceStrong s.paper &&
            Contrast.contrastMilli c.surfaceStrong s.paper < Contrast.contrastMilli c.rule s.paper)
  -- Seeds that cannot read: the ink no farther from the paper than a grey,
  -- and an ink the accent's inverse tones cannot meet.
  let bad : List (String × LeanTex.Core.SeedPalette.Seeds) := [
    ("ink near the paper", { ink := hex "8A8A8A", paper := hex "9A9A9A", accent := hex "E85D2A" }),
    ("mid-grey ink", { ink := hex "808080", paper := hex "FFFFFF", accent := hex "E85D2A" }),
    ("a CMYK ink",
      { ink := { r := 0, g := 0, b := 0, cmyk := some (0, 0, 0, 1000) },
        paper := hex "FFFFFF", accent := hex "E85D2A" })]
  for (name, s) in bad do
    match generate s with
    | .ok _ => t s!"seeds {name}: name the role that fails" false
    | .error f =>
      t s!"seeds {name}: the failure names a role and why ({f.detail})" (!f.detail.isEmpty)

/-- A darkening amber turns toward red by the warm turn, never further: its
accent text's hue stands below the seed's, by at most 20° and the 8-bit
step's turn. A cool hue holds. -/
def amberChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (name, accent) in [("amber", "F59E0B"), ("yellow", "FACC15"), ("dark orange", "FF8C00")] do
    let s : LeanTex.Core.SeedPalette.Seeds :=
      { ink := hex "1C1917", paper := hex "FFFFFF", accent := hex accent }
    match generate s with
    | .error _ => t s!"warm turn {name}: generates" false
    | .ok g =>
      let seedHue := (lchOf s.accent).2
      let textHue := (lchOf g.colors.accentText).2
      t s!"warm turn {name}: the accent text turns toward red ({seedHue} → {textHue} m°)"
        (textHue ≤ seedHue)
      t s!"warm turn {name}: by at most the turn's 20°" (hueGap textHue seedHue ≤ 21000)
  let s : LeanTex.Core.SeedPalette.Seeds :=
    { ink := hex "1C1917", paper := hex "FFFFFF", accent := hex "3B82F6" }
  match generate s with
  | .error _ => t "warm turn blue: generates" false
  | .ok g =>
    t "warm turn blue: a cool accent's text keeps its hue"
      (hueGap (lchOf g.colors.accentText).2 (lchOf s.accent).2 ≤ 1500)

/-- The digits a value at `labOf`'s 10¹⁸ scale has after the point. -/
private def fraction (v : Int) : String :=
  let s := toString v.natAbs
  String.ofList (List.replicate (18 - s.length) '0') ++ s

/-- `oklch()` and `oklab()` read as CSS Color 4 reads them: an in-gamut value
round-trips through the 8-bit colour within one step per channel, an
out-of-gamut one maps at its own hue, and an alpha is refused. -/
def oklchChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let read (src : String) : Option Ir.Color := do
    let spec ← (Decl.parseColorSpec none src).toOption
    Ir.Palette.resolveSpec {} spec
  let near (a b : Ir.Color) : Bool :=
    let d (x y : UInt8) := if x ≤ y then y - x else x - y
    d a.r b.r ≤ 1 && d a.g b.g ≤ 1 && d a.b b.b ≤ 1
  for c in [hex "2B2440", hex "E85D2A", hex "0D9488", hex "FACC15", hex "7F7F7F", hex "C026D3"] do
    let l := Oklab.labOf c
    let C := (Nat.sqrt (Oklab.chromaSq l).toNat : Int)
    let H := Oklab.hueMilli l.a l.b
    let src := s!"oklch(0.{fraction l.L} 0.{fraction C} {H / 1000}.{(fraction (H % 1000)).drop 15})"
    match read src with
    | none => t s!"oklch: {src} reads" false
    | some c' => t s!"oklch: {c.css} round-trips within one step ({src} → {c'.css})" (near c c')
    let sign (v : Int) := if v < 0 then "-" else ""
    let srcLab := s!"oklab(0.{fraction l.L} {sign l.a}0.{fraction l.a} {sign l.b}0.{fraction l.b})"
    match read srcLab with
    | none => t s!"oklab: {srcLab} reads" false
    | some c' => t s!"oklab: {c.css} round-trips within one step" (near c c')
  match read "oklch(70% 0.3 150)" with
  | none => t "oklch: an out-of-gamut green reads" false
  | some c =>
    t s!"oklch: an out-of-gamut green maps at its hue ({c.css})" (hueGap (lchOf c).2 150000 ≤ 3000)
  t "oklch: an alpha is refused" (read "oklch(0.7 0.1 150 / 0.5)").isNone
  t "oklch: a lightness past 1 is refused" (read "oklch(1.2 0.1 150)").isNone
  t "oklab: a negative component reads" (read "oklab(0.5 -0.1 0.05)").isSome

private def deckSource (pre : String) : String :=
  "\\documentclass{beamer}\n" ++ pre ++
  "\\begin{document}\n\\begin{frame}{Rates \\alert{rise}}\n" ++
  "\\begin{block}{Plain}Kilo body.\\end{block}\n" ++
  "\\begin{alertblock}{Alerted}Lima body.\\end{alertblock}\n" ++
  "\\begin{exampleblock}{Example}Mike body.\\end{exampleblock}\n" ++
  "\\end{frame}\n\\end{document}"

/-- The deck the native `\palette[seeds]` sets: every block's title band and
body fill stand at least 1.10:1 apart on the page, each a tint of its
family's hue with chroma to show it (the grey surface before held 0.002),
and an `\alert` in a frame title on the ink bar ships in the accent's
inverse tone, legible there, with nothing to report. -/
def deckChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let pre := "\\palette[seeds]{ ink = #2B2440, paper = #FFFFFF, accent = #E85D2A }\n" ++
    "\\palette{ frametitlebg = #2B2440, frametitlefg = #FFFFFF }\n"
  let (doc, ds) := elabStr (deckSource pre)
  t s!"seed deck: no warning ({(ds.filter (·.severity != .note)).map (·.code)})"
    (ds.all (·.severity == .note))
  t "seed deck: no low-contrast report" (ds.all (·.code != "W0315"))
  let some g := (generate deckSeeds).toOption | t "seed deck: the seeds generate" false; return
  let c := g.colors
  let out := Layout.run (Layout.Geom.ofPage doc.page) fonts none doc
  let fills := out.pages.flatMap (·.fills) |>.map (·.color)
  let neutral := LeanTex.Core.SeedPalette.neutralFamily deckSeeds
  let accent := LeanTex.Core.SeedPalette.accentFamily deckSeeds.accent
  for (kind, bar, body, fam) in [("block", c.surfaceStrong, c.surface, neutral),
      ("alert", c.accentSoft, c.accentWash, accent), ("example", c.surfaceStrong, c.surface, neutral)] do
    t s!"seed deck: the {kind} block paints its title band and body"
      (fills.contains bar && fills.contains body)
    t s!"seed deck: the {kind} band and body stand at least 1.10:1 apart"
      (1100 ≤ Contrast.contrastMilli bar body)
    for fill in [bar, body] do
      t s!"seed deck: the {kind} fill {fill.css} shows chroma 0.005 or more"
        (5 * 10 ^ 15 ≤ (lchOf fill).1)
      t s!"seed deck: the {kind} fill {fill.css} holds its family's hue within 10°"
        (LeanTex.Core.SeedPalette.withinTenDegrees fam fill)
  let bar := deckSeeds.ink
  let titleRuns := out.pages.flatMap (·.lines) |>.filter (fun l => (lineText l).startsWith "Rates")
    |>.flatMap (·.segs) |>.filterMap fun
      | .run _ ink _ _ _ _ _ _ _ _ _ => some ink
      | _ => none
  t "seed deck: the frame title ships" (!titleRuns.isEmpty)
  t s!"seed deck: every run of the frame title reads on the ink bar ({titleRuns.map (·.css)})"
    (titleRuns.all fun ink => Contrast.aaText ≤ Contrast.contrastMilli ink bar)
  t "seed deck: the title's alert is the accent's inverse tone"
    (titleRuns.contains c.accentOnInverse)
  let (_, nodes, _) := HtmlDoc.emitTree {} doc
  let html := Html.render (Html.elem "div" nodes) 0
  t "seed deck: the web title's alert reads the inverse role"
    (html.contains (Ir.ColorRef.role .accentOnInverse).property)

/-- A declaration list with every `var()` reference replaced by what the
root table holds for it (or its fallback), 512 references deep; a
reference that dangles reads `<dangling>`. -/
private def substVars (vars : List (String × String)) (v : String) : String := Id.run do
  let mut cur := v
  for _ in [0:512] do
    match cur.splitOn "var(" with
    | pre :: tailParts@(_ :: _) =>
      let mut depth := 0
      let mut inner := ""
      let mut rest := ""
      let mut closed := false
      for c in ("var(".intercalate tailParts).toList do
        if closed then
          rest := rest.push c
        else if c == '(' then
          depth := depth + 1
          inner := inner.push c
        else if c == ')' then
          if depth == 0 then
            closed := true
          else
            depth := depth - 1
            inner := inner.push c
        else
          inner := inner.push c
      let rep := match inner.splitOn "," with
        | key :: more =>
          match vars.lookup key.trimAscii.toString with
          | some w => w
          | none => if more.isEmpty then "<dangling>" else (",".intercalate more).trimAscii.toString
        | [] => "<dangling>"
      cur := pre ++ rep ++ rest
    | _ => break
  return cur

/-- A page's light-screen rules outside its root table, each selector with
its declarations' `var()` references read through that table. -/
private def resolvedRules (html : String) : List (String × String) :=
  let css := ((html.splitOn "<style>").getD 1 "").splitOn "</style>" |>.headD ""
  let vars := screenRootVars html
  (artTopCssBlocks css).toList.filterMap fun (sel, decls) =>
    if sel == ":root" then none else some (sel, substVars vars decls)

/-- **The export is the native palette's print projection**: every colour
the include declares is the colour the native `\palette[seeds]` build
resolves the role it names to in print, every channel of every beamer element
it writes (`SeedPalette.beamerChannels`: the text and the canvas, the footline
and its page number, the alert, the six block elements, the progress bar and
the title separator) names a colour
it declares, set at the native build's print colour for the role that
channel paints, and the code colours `--pygments` writes are the colours the
native build paints each code role in on the page — the values a TeX build
consumes. Built from the include, the invented deck, which reads only
exported roles, ships the native build's PDF bytes and typed HTML body in
both block styles, and the light screen's rules, read through each
stylesheet's own root table, are alike but the standout frame's, whose colours
the include leaves to the beamer theme. What the engine derives at a use site
is the native build's alone: a generated role's tone on a ground it does not
read on, a code tone on the palette's own fills, and the web page's focus ring
(both builds declare it alike here), for the include declares colours, and a
declared colour ships as declared. -/
def exportChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  -- The include's values, role by role and element by element.
  for style in LeanTex.Core.SeedPalette.Blocks.all do
    let some g := (generate deckSeeds).toOption | t "export: the seeds generate" false; return
    let st : LeanTex.Core.SeedPalette.SeedState :=
      { seeds := deckSeeds, targets := deckSeeds.targets .decks, blocks := style, colors := g.colors }
    let (nd, _) := elabStr ("\\documentclass{beamer}\n\\palette[seeds]{ ink = #2B2440, " ++
      s!"paper = #FFFFFF, accent = #E85D2A, blocks = {style.name} }\n" ++
      "\\begin{document}\n\\begin{frame}x\\end{frame}\n\\end{document}")
    let decls := LeanTex.Core.SeedPalette.declarations "seed" st
    for r in Ir.Role.all do
      if let some name := r.row.exportName then
        if let some c := LeanTex.Core.SeedPalette.Colors.role st.seeds st.colors r then
          let native := (Ir.Design.at nd.palette .print r).map fun n =>
            Ir.Color.hexByte n.r ++ Ir.Color.hexByte n.g ++ Ir.Color.hexByte n.b
          t s!"export {style.name}: {name} is the native build's print {name}"
            (hasStr decls ("\\definecolor{seed" ++ name ++ "}{HTML}{" ++ Ir.Color.hexByte c.r ++
              Ir.Color.hexByte c.g ++ Ir.Color.hexByte c.b ++ "}") &&
              native == some (Ir.Color.hexByte c.r ++ Ir.Color.hexByte c.g ++ Ir.Color.hexByte c.b))
    let channels := LeanTex.Core.SeedPalette.beamerChannels st
    let written := LeanTex.Core.SeedPalette.beamerDeclarations "seed" st
    t s!"export {style.name}: the include binds every block element"
      (LeanTex.Core.SeedPalette.beamerElements.all fun (e, _, _) =>
        channels.any fun (e', fg, bg) => e' == e && fg.isSome && bg.isSome)
    for (element, fg, bg) in channels do
      for (label, ch, src) in [("fg", Ir.Channel.fg, fg), ("bg", Ir.Channel.bg, bg)] do
        if let some r := src then
          let exported := LeanTex.Core.SeedPalette.Colors.role st.seeds st.colors r
          let native := (BeamerColor.channelRole element ch).bind (Ir.Design.at nd.palette .print)
          let declared := match r.row.exportName, exported with
            | some n, some c => hasStr decls ("\\definecolor{seed" ++ n ++ "}{HTML}{" ++
                Ir.Color.hexByte c.r ++ Ir.Color.hexByte c.g ++ Ir.Color.hexByte c.b ++ "}") &&
                hasStr written ("\\setbeamercolor{" ++ element ++ "}{")
            | _, _ => false
          t s!"export {style.name}: '{element}' {label} is the native build's print colour"
            (declared && exported.isSome && native == exported)
    -- The code colours a TeX build's minted reads are the native page's.
    for ls in Ir.ListingStyle.all do
      let exported := CodeExport.pageBrushes (({} : Ir.Palette).applySeeds st) ls
      let native := CodeExport.pageBrushes nd.palette ls
      t s!"export {style.name}: the {ls.name} code colours are the native page's"
        (ListingHighlight.Role.all.all fun r => (exported.get r).ink == (native.get r).ink)
  let body := "\\begin{document}\n\\begin{frame}{Rates}\nPlain text and \\alert{an alert}.\n" ++
    "\\begin{block}{Plain}Kilo body.\\end{block}\n" ++
    "\\begin{alertblock}{Alerted}Lima body.\\end{alertblock}\n" ++
    "\\begin{exampleblock}{Example}Mike body.\\end{exampleblock}\n" ++
    "\\end{frame}\n\\end{document}"
  let focus := "\\palette{ focus = #1D4ED8 }\n"
  for style in LeanTex.Core.SeedPalette.Blocks.all do
    let some g := (generate deckSeeds).toOption | t "export: the seeds generate" false; return
    let st : LeanTex.Core.SeedPalette.SeedState :=
      { seeds := deckSeeds, targets := deckSeeds.targets .decks, blocks := style, colors := g.colors }
    let native := "\\documentclass{beamer}\n\\palette[seeds]{ ink = #2B2440, paper = #FFFFFF, " ++
      s!"accent = #E85D2A, blocks = {style.name} }\n" ++ focus ++ body
    let exported := "\\documentclass{beamer}\n" ++
      LeanTex.Core.SeedPalette.beamerDeclarations "seed" st ++ focus ++ body
    let (nd, nds) := elabStr native
    let (ed, eds) := elabStr exported
    t s!"export {style.name}: both build clean"
      (nds.all (·.severity == .note) && eds.all (·.severity == .note))
    let geom := Layout.Geom.ofPage nd.page
    let pdf (d : Ir.Doc) := driverPdf fonts geom d (Layout.run geom fonts none d)
    t s!"export {style.name}: identical PDF bytes" (pdf nd == pdf ed)
    let parts (d : Ir.Doc) :=
      let (head, nodes, _) := HtmlDoc.emitTree {} d
      (Html.render (Html.elem "head" head) 0, Html.render (Html.elem "body" nodes) 0)
    let (_, nb) := parts nd
    let (_, eb) := parts ed
    t s!"export {style.name}: identical typed HTML body" (nb == eb)
    -- The light screen's rules, each `var()` read through its own sheet's
    -- root table, are alike in both builds but the standout frame's, whose
    -- colours the include leaves to the beamer theme.
    let rules (d : Ir.Doc) := resolvedRules (HtmlDoc.emit {} d).1
    let (rn, re) := (rules nd, rules ed)
    let differ := (rn.zip re).filter (fun (x, y) => x != y) |>.map (·.1.1)
    t s!"export {style.name}: the light screen's rules resolve alike but the standout frame's ({differ})"
      (rn.length == re.length && rn.length > 100 &&
        differ.all (·.startsWith "section.slide.standout"))

/-- **A generated palette is the palette the seeds make, under what the
document declares**: a role the document declared before the seeds keeps its
colour, one declared after replaces the generated colour, and a theme's
colour gives way to the seeds' (document > generated > bundle); the default
bundle's colours stay out of a seeded deck, whose rule, progress bar and title
separator are the seeds' own; a generated role on the standout inversion takes
its family's tone there, legible, with nothing to report; and `decorative`,
which a generated palette has nothing to exempt from, is named and ignored.
Read off the palette both artifacts resolve, `Layout.Out` and the log. -/
def seedRoleChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let seeds := "\\palette[seeds]{ ink = #2B2440, paper = #FFFFFF, accent = #E85D2A }\n"
  let deck (pre body : String) : String :=
    "\\documentclass{beamer}\n" ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let frame := "\\begin{frame}{Probe}Probe.\\end{frame}"
  let declared (d : Ir.Doc) (r : Ir.Role) := Ir.Design.declared? d.palette r
  let (before, _) := elabStr (deck ("\\palette{ muted = #AA0000, blocktitlebg = #00AA00 }\n" ++ seeds) frame)
  t "seed roles: a role declared before the seeds keeps its colour"
    (declared before .muted == some (hex "AA0000") && declared before .blockTitleBar == some (hex "00AA00"))
  let (after, _) := elabStr (deck (seeds ++ "\\palette{ muted = #AA0000 }\n") frame)
  t "seed roles: a role declared after the seeds replaces the generated colour"
    (declared after .muted == some (hex "AA0000"))
  let some g := (generate deckSeeds).toOption | t "seed roles: the seeds generate" false; return
  let c := g.colors
  let (themed, _) := elabStr (deck ("\\theme{moloch}\n" ++ seeds) frame)
  t "seed roles: the seeds' alert replaces a theme's"
    (declared themed .alert == some c.alert)
  let (plain, _) := elabStr (deck seeds frame)
  t "seed roles: the rule a seeded deck ships is the generated rule"
    (declared plain .rule == some c.rule)
  t "seed roles: the progress bar and the separator are the seeds' accent"
    (declared plain .progressFill == some deckSeeds.accent &&
      declared plain .progressTrack == some c.accentSoft && declared plain .separator == some deckSeeds.accent)
  t "seed roles: no colour of the default bundle reaches a seeded deck"
    ((declared plain .standoutGround).isNone && (declared plain .example).isNone)
  -- A generated role on the standout inversion: its family's tone there.
  let (so, soDs) := elabStr (deck seeds
    "\\begin{frame}[standout]\\alert{Loud} and \\textcolor{muted}{quiet}.\\end{frame}")
  let ground := (Ir.Design.ofPalette so.palette).standout.bg
  let inks := (allLines (Layout.run (Layout.Geom.ofPage so.page) fonts none so)).flatMap
    (·.segs) |>.filterMap fun
      | .run _ ink _ _ glyphs .. => if glyphs.isEmpty then none else some ink
      | _ => none
  t s!"seed roles: every run on the standout inversion reads there ({inks.map (·.css)})"
    (!inks.isEmpty && inks.all fun i => Contrast.aaText ≤ Contrast.contrastMilli i ground)
  t "seed roles: the standout frame has nothing to report" (soDs.all (·.code != "W0315"))
  let (decoSeeds, decoDs) := elabStr (deck ("\\palette[seeds, decorative]{ ink = #2B2440, " ++
    "paper = #FFFFFF, accent = #E85D2A }\n") frame)
  t "seed roles: decorative is named once and ignored"
    ((decoDs.filter (·.code == "W0110")).size == 1)
  -- `decorative` changes nothing a generated palette ships: the two builds
  -- apart by the option alone install one palette and are judged alike (the
  -- premise of its W0110).
  let (plainSeeds, plainDs) := elabStr (deck seeds frame)
  t "seed roles: decorative leaves the generated palette and its judgement as they are"
    (decoSeeds.palette == plainSeeds.palette &&
      (decoDs.filter (·.code != "W0110")).map (·.code) == plainDs.map (·.code))
  -- Every role door, and an author colour named like a role key, before the
  -- seeds; the seeds' own ink, paper and accent as the latest declarations.
  let kept (pre : String) (r : Ir.Role) (c : Ir.Color) : Bool :=
    declared (elabStr (deck (pre ++ seeds) frame)).1 r == some c
  t "seed roles: an author colour named like a role key keeps no role from the seeds"
    (kept "\\definecolor{fg}{HTML}{3366AA}\n" .ink deckSeeds.ink &&
      kept "\\definecolor{alert}{HTML}{3366AA}\n" .alert c.alert &&
      kept "\\colorlet{muted}{blue}\n" .muted c.muted)
  t "seed roles: a beamer channel declared before the seeds keeps its colour"
    (kept "\\setbeamercolor{alerted text}{fg=green!50!black}\n" .alert (hex "008000") &&
      kept "\\setbeamercolor{block title}{bg=red, fg=white}\n" .blockTitleBar (hex "FF0000") &&
      kept "\\setbeamercolor{block title}{bg=red, fg=white}\n" .blockTitleInk (hex "FFFFFF"))
  t "seed roles: the seeds' ink, paper and accent are the latest declarations"
    (kept "\\palette{ fg = #000000, bg = #FFFFEE, accent = #0000AA }\n" .ink deckSeeds.ink &&
      kept "\\palette{ fg = #000000, bg = #FFFFEE, accent = #0000AA }\n" .page deckSeeds.paper &&
      kept "\\palette{ fg = #000000, bg = #FFFFEE, accent = #0000AA }\n" .accent deckSeeds.accent)
  t "seed roles: what a style binds reads its source role as installed"
    (kept "\\palette{ fg = #000000 }\n" .blockBodyInk deckSeeds.ink &&
      kept "\\palette{ accent = #0000AA }\n" .separator deckSeeds.accent)
  let (themedAfter, themedDs) := elabStr (deck (seeds ++ "\\theme{moloch}\n") frame)
  t "seed roles: a theme after the seeds replaces their colours and says so"
    (declared themedAfter .ink != some deckSeeds.ink &&
      (themedDs.filter (·.code == "W0348")).size ≥ 1)

/-- Seeds that generate no palette are named once, by the role that fails,
and stand as the page's text, ground and accent. -/
def failureChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr (dvDoc
    "\\palette[seeds]{ ink = #808080, paper = #FFFFFF, accent = #E85D2A }\n" "Text.")
  let named := ds.filter (·.code == "W0306")
  t "seeds failure: named once" (named.size == 1)
  t "seeds failure: the subject names the failing role"
    (named.all fun d => (d.subject.getD "").startsWith "palette:seeds:")
  let d := Ir.Design.ofPalette doc.palette
  t "seeds failure: the seeds stand as the page's text and ground"
    (d.fg == hex "808080" && d.bg == hex "FFFFFF")
  let (_, missing) := elabStr (dvDoc "\\palette[seeds]{ ink = #2B2440, paper = #FFFFFF }\n" "Text.")
  t "seeds failure: a missing accent is an invalid block" (missing.any (·.code == "E0320"))
  let (_, style) := elabStr (dvDoc
    "\\palette[seeds]{ ink = #2B2440, paper = #FFFFFF, accent = #E85D2A, blocks = loud }\n" "Text.")
  t "seeds failure: an unknown block style is unreadable" (style.any (·.code == "E0321"))

/-- The script a TeX build's include comes from: it names every exported
role, the eleven names it wrote before among them, and `--check` exits 0 on
the include it writes and 1 on a stale one. -/
def scriptChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (lean, leanPath) ← leanChild "the palette script's checks"
  let dir ← IO.FS.realPath (← IO.currentDir)
  let tmp := dir / ".lake" / "seed-script-check"
  IO.FS.createDirAll tmp
  let run (args : Array String) :=
    RunBounded.runBounded lean.toString (#["--run", "scripts/palette.lean"] ++ args) dir 120000 100
      (env := #[("LEAN_PATH", some leanPath)])
  let made ← run #["--beamer-blocks", "seed", "2B2440", "FFFFFF", "E85D2A"]
  t s!"palette script: writes an include ({made.err})" (made.complete && made.ran == .exited 0)
  for name in ["Ink", "Paper", "Accent", "Muted", "MutedOnDark", "DiagramMuted", "Surface",
      "AccentText", "AccentOnDark", "AccentEdge", "AccentSoft", "SurfaceStrong", "AccentWash",
      "AlertTitle", "ExampleTitle"] do
    t s!"palette script: names seed{name}" (made.out.contains ("\\definecolor{seed" ++ name ++ "}"))
  IO.FS.writeFile (tmp / "fresh.tex") made.out
  IO.FS.writeFile (tmp / "stale.tex") (made.out.replace "seedSurface}" "seedSurface}%")
  let fresh ← run #["--beamer-blocks", "--check", (tmp / "fresh.tex").toString, "seed", "2B2440",
    "FFFFFF", "E85D2A"]
  t s!"palette script: --check passes a fresh include ({fresh.err})" (fresh.ran == .exited 0)
  let stale ← run #["--beamer-blocks", "--check", (tmp / "stale.tex").toString, "seed", "2B2440",
    "FFFFFF", "E85D2A"]
  t s!"palette script: --check fails a stale include ({stale.err})" (stale.ran == .exited 1)

end Tests.SeedPalette
