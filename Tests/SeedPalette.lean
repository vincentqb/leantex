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

/-- **The export is a projection of the native palette**: the invented deck
built from `\palette[seeds]` and built from the include the generator
exports, through beamer's own colour elements, ship identical PDF bytes and
an identical typed HTML body in both block styles, and their stylesheets
declare the same properties at the same values. What the include adds is
its own xcolor names, which the web page exposes as named colours for a host
to override (`--ltx-c-<name>` and the name itself) and the native build has
none of. Both declare the focus ring alike: the ring is the web page's own,
with no element in a TeX build. -/
def exportChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
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
    let declarations (head : String) : List String :=
      ((head.splitOn "\n").map (·.trimAscii.toString)).filter (fun l =>
        !l.isEmpty && (l.splitOn "--ltx-c-seed").length == 1 && !l.startsWith "--seed")
        |>.mergeSort (· ≤ ·)
    let (nh, nb) := parts nd
    let (eh, eb) := parts ed
    t s!"export {style.name}: identical typed HTML body" (nb == eb)
    t s!"export {style.name}: the stylesheets declare alike, the include's own names aside"
      (declarations nh == declarations eh)

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

/-- The script a TeX build's include comes from: its names keep the eleven
the talks' includes read, and `--check` exits 0 on the include it writes and
1 on a stale one. -/
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
