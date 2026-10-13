module

public import Tests.Support
public import LeanTex.Core.ContrastSolve

public section

open LeanTex.Core

namespace Tests.PaletteDefaults

/-- The glyph runs a page set, with the scalars each shipped. -/
private def runsOf (out : Layout.Out) : Array (String × Ir.Color) :=
  out.pages.flatMap fun p => p.lines.flatMap fun l => l.segs.filterMap fun
    | .run _ ink _ _ glyphs .. =>
      if glyphs.isEmpty then none else some (String.ofList (glyphs.map (·.2.1)).toList, ink)
    | _ => none

/-- A role's value in a page's light stylesheet, its `var()` chain chased. -/
private def cssRole (css : String) (r : Ir.Role) : Option String :=
  chaseCssValue (screenRootVars css) (HtmlDoc.roleRef r)

/-- What an undeclared document and a shipped bundle show on the page, in the PDF's operators and in
the typed HTML. -/
def checks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  -- moloch's lineage, as lualatex writes it: `0.92157 0.50587 0.10588 rg`.
  let (mdoc, _) := elabStr ("\\documentclass[aspectratio=169]{beamer}\n\\usetheme{moloch}\n" ++
    "\\title{Probe Title}\n\\author{Probe Author}\n\\begin{document}\n\\maketitle\n" ++
    "\\begin{frame}{One}Probe.\\end{frame}\n\\end{document}")
  let mgeom := Layout.Geom.ofPage mdoc.page
  let mpdf := pdfText (Pdf.write mgeom fonts (layoutOf fonts mdoc mgeom).pages mdoc.info)
  t "moloch: the title separator draws lualatex's lineage operator"
    (bytesContain mpdf "0.92157 0.50587 0.10588 rg")
  let lineage := Ir.Color.ofHtml 0xEB 0x81 0x1B
  -- A declared colour is reported, never repainted.
  let (adoc, _) := elabStr ("\\documentclass[aspectratio=169]{beamer}\n\\usetheme{moloch}\n" ++
    "\\begin{document}\n\\begin{frame}{One}Probe \\alert{alerted} words.\\end{frame}\n" ++
    "\\end{document}")
  t "moloch: the alert is the lineage colour exactly"
    (Ir.Design.declared? adoc.palette .alert == some lineage)
  t "moloch: the alerted words set in it on the page"
    ((runsOf (layoutOf fonts adoc)).any fun (text, ink) => hasStr text "alerted" && ink == lineage)
  let alertSays := (Contrast.docDiags adoc).filter fun d =>
    d.severity == .warning && d.subject.any (hasStr · "alert")
  t s!"moloch: the report names the alert's pairing once ({alertSays.map (·.code)})"
    (alertSays.size == 1)
  -- A seedless bundle's muted ink is the quietest tone of its ink's family at a document's 4.5:1 on
  -- its page.
  for th in [Theme.moloch, Theme.plain, Theme.gemini] do
    let pal := th.realize .decks
    match Ir.Design.declared? pal .muted, Ir.Design.declared? pal .ink,
        Ir.Design.at pal .print .page with
    | some m, some ink, some page =>
      t s!"{th.name}: its muted {m.css} is its ink's derived by the generated rule"
        (some m == SeedPalette.mutedFor ink page && m != ink.mix 70 page)
      t s!"{th.name}: its muted {m.css} reads at 4.5:1 on its page, and no further"
        (4500 ≤ Contrast.contrastMilli m page && Contrast.contrastMilli m page ≤ 4600)
    | _, _, _ => t s!"{th.name}: its muted, ink and page resolve" false
  for th in Theme.builtin do
    let short := Theme.installs.flatMap fun c => Theme.shipped.flatMap fun sc =>
      (Ir.Design.sites (Theme.installedAt th c) sc).filterMap fun st =>
        if st.passesAt c.depth.stage then none else some st.role
    t s!"{th.name}: the roles it ships short of their need are the ones it reports"
      (short.all th.reported.contains && th.reported.all short.contains)
  let (ldoc, _) := elabStr (dvDoc "" ("Probe words.\n\\begin{itemize}\n\\item First\n" ++
    "\\item Second\n\\end{itemize}"))
  let lout := layoutOf fonts ldoc
  let bullets := (runsOf lout).filter (·.1.any (· == '•')) |>.map (·.2)
  let lcss := (HtmlDoc.emit {} ldoc).1
  t s!"an undeclared list: the page and the HTML mark it in one colour ({bullets.map (·.css)}, {cssRole lcss .marker})"
    (!bullets.isEmpty && bullets.all fun c => cssRole lcss .marker == some (HtmlDoc.cssColor c))
  let (adoc, _) := elabStr (dvDoc "" "Probe words in an undeclared article.")
  let ageom := Layout.Geom.ofPage adoc.page
  let aout := layoutOf fonts adoc ageom
  let apdf := pdfText (Pdf.write ageom fonts aout.pages adoc.info)
  t "an undeclared article: the HTML body stands on white"
    (cssRole (HtmlDoc.emit {} adoc).1 .page == some "#ffffff")
  t "an undeclared article: the PDF paints no page and sets its words in black"
    (aout.pages.all (·.fills.isEmpty) && (runsOf aout).all (·.2 == Ir.Color.black) &&
      !bytesContain apdf " rg\n" && !bytesContain apdf " k\n")
  let (mddoc, _) := elabMd "Probe words.\n\n```\nalpha = 1\nbravo = 2\n```\n"
  let ground := Ir.Design.at mddoc.palette .print .codeSurface
  let mdout := layoutOf fonts mddoc
  t s!"a markdown note: the fenced code stands on its code ground in the PDF ({ground.map (·.css)})"
    (ground.isSome && mdout.pages.any fun p => p.fills.any fun f => some f.color == ground)
  t "a markdown note: the HTML paints the same ground"
    ((ground.map HtmlDoc.cssColor) == cssRole (HtmlDoc.emit {} mddoc).1 .codeSurface &&
      ground.isSome)
  let tint := Ir.Color.ofHtml 0xEE 0xF2 0xE8
  let (edoc, _) := elabStr (dvDoc "" ("Fern words.\n\\palette{ tint = #EEF2E8 }\n" ++
    "\\begin{verbatim}\nfrond = 1\n\\end{verbatim}"))
  t "an epoch's code ground: the PDF paints it under the listing"
    ((layoutOf fonts edoc).pages.any fun p => p.fills.any (·.color == tint))
  let ecss := (HtmlDoc.emit {} edoc).1
  let decls (style : String) : List (String × String) :=
    ((style.splitOn ";").filterMap fun d => match d.splitOn ":" with
      | [k, v] => some (k.trimAscii.toString, v.trimAscii.toString)
      | _ => none).reverse
  t "an epoch's code ground: the HTML paints it under the listing"
    ((elemNodesList (· == "pre") #[] (docNodesOf edoc).toList).any fun n => match n with
      | .elem _ attrs _ =>
        let own := decls ((HtmlDoc.attrOf? attrs "style").getD "")
        (own.lookup "background").any fun v =>
          lightValue (own ++ screenRootVars ecss) v == HtmlDoc.cssColor tint
      | _ => false)
  let docOf (src : Option String) : Ir.Doc := match src with
    | some s => (elabStr s).1
    | none => (elabMd "Probe words.\n").1
  for (what, src) in [("a markdown note", none),
      ("a webpage", some "\\documentclass{webpage}\n\\begin{document}\nProbe words.\n\\end{document}"),
      ("an undeclared deck", some "\\documentclass{beamer}\n\\begin{document}\n\\begin{frame}x\\end{frame}\n\\end{document}")] do
    let doc := docOf src
    let muted := Ir.Design.at doc.palette .print .muted
    t s!"{what}: its PDF and its HTML read one muted ({muted.map (·.css)})"
      (muted.isSome && muted == Ir.Design.at doc.palette .light .muted &&
        muted != Ir.Design.at doc.palette .print .ink)
  for (what, src) in [("an undeclared article", some (dvDoc "" "Probe words.")),
      ("a deck under beamer's default theme", some ("\\documentclass{beamer}\n\\usetheme{default}\n" ++
        "\\begin{document}\n\\begin{frame}x\\end{frame}\n\\end{document}"))] do
    let doc := docOf src
    t s!"{what}: its muted is its ink, in print and on screen"
      ([Ir.Scheme.print, .light].all fun s =>
        Ir.Design.at doc.palette s .muted == Ir.Design.at doc.palette s .ink)
  let (ddoc, _) := elabStr ("\\documentclass[aspectratio=169]{beamer}\n\\begin{document}\n" ++
    "\\begin{frame}{Cards}\n\\begin{block}{Plain}Kilo body.\\end{block}\n" ++
    "\\begin{alertblock}{Alerted}Lima body.\\end{alertblock}\n" ++
    "\\begin{exampleblock}{Example}Mike body.\\end{exampleblock}\n\\end{frame}\n\\end{document}")
  let fills := (layoutOf fonts ddoc).pages.flatMap (·.fills) |>.map (·.color)
  for (kind, barRole, bodyRole) in [("block", Ir.Role.blockTitleBar, Ir.Role.blockBodyGround),
      ("alert", .alertTitleBar, .alertBodyGround), ("example", .exampleTitleBar, .exampleBodyGround)] do
    match Ir.Design.at ddoc.palette .print barRole, Ir.Design.at ddoc.palette .print bodyRole with
    | some bar, some body =>
      t s!"an undeclared deck: the {kind} block paints its title band and body"
        (fills.contains bar && fills.contains body)
      t s!"an undeclared deck: the {kind} band and body stand at least 1.10:1 apart"
        (1100 ≤ Contrast.contrastMilli bar body)
      for fill in [bar, body] do
        t s!"an undeclared deck: the {kind} fill {fill.css} shows chroma 0.005 or more"
          (5 * 10 ^ 15 ≤ (lchOf fill).1)
    | _, _ => t s!"an undeclared deck: the {kind} block has a band and a body" false

/-- A generated palette's inks give way where the document declares a ground, ink or paper. -/
def yieldChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let deck (pre : String) := "\\documentclass[aspectratio=169]{beamer}\n" ++ pre ++
    "\\begin{document}\n\\begin{frame}{Cards}\n" ++
    "\\begin{block}{Plain}Kilo body.\\end{block}\n" ++
    "\\begin{alertblock}{Alerted}Lima body.\\end{alertblock}\n\\end{frame}\n\\end{document}"
  let bars := "\\palette{ blocktitlebg = #333333, alerttitlebg = #333333 }\n"
  for (what, pre) in [("the class's default bundle", bars),
      ("a bundle named outright", "\\usetheme{daylight}\n" ++ bars),
      ("the document's own seeds",
        "\\palette[seeds]{ ink = #2B2440, paper = #FFFFFF, accent = #E85D2A }\n" ++ bars),
      ("a beamer channel", "\\usetheme{daylight}\n\\setbeamercolor{block title}{bg=black!80}\n" ++
        "\\setbeamercolor{block title alerted}{bg=black!80}\n")] do
    let (doc, ds) := elabStr (deck pre)
    let reads (s : Ir.Scheme) (text bar : Ir.Role) : Bool :=
      match Ir.Design.at doc.palette s text, Ir.Design.at doc.palette s bar with
      | some i, some b => Contrast.aaText ≤ Contrast.contrastMilli i b
      | _, _ => false
    t s!"generated inks give way under {what}: the titles read on the declared bars"
      ([Ir.Scheme.print, .light].all fun s =>
        reads s .blockTitleInk .blockTitleBar && reads s .alertTitleInk .alertTitleBar)
    t s!"generated inks give way under {what}: nothing to report"
      (ds.all fun d => d.code != "W0315" && d.code != "W0345")
  let darkPage := Ir.Color.ofHtml 0x10 0x14 0x18
  let lightInk := Ir.Color.ofHtml 0xE8 0xE8 0xE8
  let (dark, _) := elabStr (deck "\\palette{ bg = #101418, fg = #E8E8E8 }\n")
  t "a deck's own paper and ink: the cards' text is its ink"
    (Ir.Design.at dark.palette .print .blockBodyInk == some lightInk &&
      Ir.Design.at dark.palette .print .blockTitleInk == some lightInk)
  t "a deck's own paper and ink: the cards are tints of its dark paper, legible"
    (match Ir.Design.at dark.palette .print .blockBodyGround,
        Ir.Design.at dark.palette .print .blockTitleBar with
      | some body, some bar =>
        Contrast.luminance body < Contrast.luminance lightInk &&
          Contrast.contrastMilli body darkPage < 1500 &&
          Contrast.aaText ≤ Contrast.contrastMilli lightInk body &&
          Contrast.aaText ≤ Contrast.contrastMilli lightInk bar
      | _, _ => false)
  let purple := Ir.Color.ofHtml 0x5B 0x2A 0x86
  let (inked, _) := elabStr (deck "\\palette{ fg = #5B2A86 }\n")
  t "a deck's own ink: its cards' titles and bodies are set in it"
    (Ir.Design.at inked.palette .print .blockBodyInk == some purple &&
      Ir.Design.at inked.palette .print .blockTitleInk == some purple)

/-- A bundle's generated palette follows the seeds a deck declares, through every door. -/
def reseedChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let deck (pre body : String) := "\\documentclass[aspectratio=169]{beamer}\n" ++ pre ++
    "\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let cards := "\\begin{frame}{Cards}\n\\begin{block}{Plain}Kilo body.\\end{block}\n" ++
    "\\begin{alertblock}{Alerted}Lima body.\\end{alertblock}\n\\end{frame}"
  let dark := Ir.Color.ofHtml 0x10 0x14 0x18
  let darkCards (pal : Ir.Palette) : Bool :=
    match Ir.Design.at pal .print .page, Ir.Design.at pal .print .blockBodyGround,
        Ir.Design.at pal .print .blockTitleBar, Ir.Design.at pal .print .blockBodyInk with
    | some page, some body, some bar, some ink =>
      Contrast.contrastMilli body page < 1500 && Contrast.contrastMilli bar page < 1700 &&
        Contrast.luminance body < 1800000 &&
        Contrast.aaText ≤ Contrast.contrastMilli ink body &&
        Contrast.aaText ≤ Contrast.contrastMilli ink bar
    | _, _, _, _ => false
  let quiet (ds : Array Diag) : Bool :=
    ds.all fun d => !(["W0304", "W0315", "W0330", "W0345"].contains d.code)
  let (bgOnly, ds) := elabStr (deck "\\palette{ bg = #101418 }\n" cards)
  t "a deck's own dark page: its ink reads there and its cards are its page's tints"
    (darkCards bgOnly.palette && (Ir.Design.at bgOnly.palette .print .ink).any fun i =>
      Contrast.aaText ≤ Contrast.contrastMilli i dark)
  t "a deck's own dark page: nothing to report" (quiet ds)
  let (paged, ds) := elabStr (deck "\\pagecolor[HTML]{101418}\n" cards)
  t "a deck's page through \\pagecolor: its cards are its page's tints" (darkCards paged.palette)
  t "a deck's page through \\pagecolor: nothing to report" (quiet ds)
  let (named, ds) := elabStr (deck "\\usetheme{daylight}\n\\palette{ bg = #101418, fg = #E8E8E8 }\n" cards)
  t "a named bundle under a deck's page and ink: its cards are generated from them"
    (darkCards named.palette &&
      Ir.Design.at named.palette .print .blockTitleInk == some (Ir.Color.ofHtml 0xE8 0xE8 0xE8))
  t "a named bundle under a deck's page and ink: nothing to report" (quiet ds)
  let purple := Ir.Color.ofHtml 0x5B 0x2A 0x86
  let (inked, _) := elabStr (deck "\\usetheme{daylight}\n\\palette{ fg = #5B2A86 }\n" cards)
  t "a named bundle under a deck's ink: its cards' titles and bodies are set in it"
    (Ir.Design.at inked.palette .print .blockTitleInk == some purple &&
      Ir.Design.at inked.palette .print .blockBodyInk == some purple)
  let (epoch, ds) := elabStr (deck "" ("\\begin{frame}{Light}\\begin{block}{Plain}Kilo.\\end{block}\\end{frame}\n" ++
    "\\palette{ bg = #101418, fg = #E8E8E8 }\n" ++ cards))
  let epochs := epoch.body.filterMap fun b => match b with
    | .setPalette p => some p
    | _ => none
  t "a body epoch's page and ink: its cards are generated from them"
    (epochs.any fun p => darkCards p &&
      Ir.Design.at p .print .blockBodyInk == some (Ir.Color.ofHtml 0xE8 0xE8 0xE8))
  t "a body epoch's page and ink: nothing to report" (quiet ds)
  let (refused, ds) := elabStr (deck "\\palette{ fg = #666666 }\n"
    ("\\begin{frame}{Cards}Dust \\alert{flare}.\n\\begin{exampleblock}{Example}Mike.\\end{exampleblock}\n" ++
      "\\end{frame}"))
  t "seeds a deck declares that generate nothing: the bundle's alert and example stand"
    ((Ir.Design.at refused.palette .print .alert).isSome &&
      (Ir.Design.at refused.palette .print .example).isSome &&
      Ir.Design.at refused.palette .print .page == some Theme.daylightSeeds.paper &&
      Ir.Design.at refused.palette .print .ink == some (Ir.Color.ofHtml 0x66 0x66 0x66))
  t "seeds a deck declares that generate nothing: no colour goes missing"
    (ds.all fun d => d.code != "W0304")
  let (trip, _) := elabStr (deck "" ("\\begin{frame}{One}\\begin{alertblock}{A}One.\\end{alertblock}\\end{frame}\n" ++
    "\\palette{ alerttitlebg = #333333 }\n" ++
    "\\begin{frame}{Two}\\begin{alertblock}{A}Two.\\end{alertblock}\\end{frame}\n" ++
    "\\palette{ alerttitlebg = #CAE1FF }\n" ++
    "\\begin{frame}{Three}\\begin{alertblock}{A}Three.\\end{alertblock}\\end{frame}"))
  let trips := trip.body.filterMap fun b => match b with
    | .setPalette p => some p
    | _ => none
  let generated := Ir.Design.at trip.palette .print .alertTitleInk
  t s!"an epoch restoring a bar's generated ground restores its generated ink ({generated.map (·.css)})"
    (generated.isSome && Ir.Design.declared? trip.palette .alertTitleBar ==
        some (Ir.Color.ofHtml 0xCA 0xE1 0xFF) &&
      (trips.back?.any fun p => Ir.Design.at p .print .alertTitleInk == generated) &&
      (trips[0]?.any fun p => Ir.Design.at p .print .alertTitleInk != generated))

end Tests.PaletteDefaults
