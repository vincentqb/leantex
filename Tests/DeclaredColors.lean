module

public import Tests.ListingHighlight

public section

open LeanTex.Core

namespace Tests.DeclaredColors

private def hex (r g b : UInt8) : Ir.Color := { r, g, b }

/-- The styles of the HTML elements whose text holds `text`, as the printed page reads them. -/
private def htmlStyles (doc : Ir.Doc) (text : String) : Array String :=
  let (_, body, _) := emitIn {} doc .print
  (elemStylesList #[] body.toList).filterMap fun (t, st) =>
    if hasStr t text && !st.isEmpty then some st else none

/-- The contrast reports a run shows: the warnings, never the notes carrying a pairing's later runs. -/
private def reports (ds : Array Diag) : Array Diag :=
  ds.filter fun d => (d.code == "W0315" || d.code == "W0345" || d.code == "W0330") &&
    d.severity == .warning

/-- A declared colour ships as declared in both artifacts, on the page and every local ground, and a
pairing short of its medium's ratio is one warning; a deck's stage asks 3:1, a page 4.5:1. -/
public def checks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  -- A role on the page: an orange that fails a document's 4.5:1.
  let orange := hex 0xE9 0x6A 0x10
  let (doc, ds) := elabStr ("\\documentclass{article}\\palette{ alert = #E96A10 }" ++
    "\\begin{document}\\textcolor{alert}{Warm word} and plain text.\\end{document}")
  let out := layoutOf fonts doc
  t "declared colours: a failing role ships its declared ink on the page"
    (let inks := inksOn out (hasStr · "Warm word")
     !inks.isEmpty && inks.contains orange)
  t "declared colours: the HTML span carries the declared ink"
    ((htmlStyles doc "Warm word").any (hasStr · (HtmlDoc.cssColor orange)))
  t "declared colours: the failing role is reported once, on one line"
    (let rs := reports ds
     rs.size == 1 && rs.all fun d =>
       d.code == "W0315" && d.help.isNone && d.subject.any (·.startsWith "alert:#E96A10@"))
  -- A role on a local ground: the frame-title bar of a deck.
  let accent := hex 0xC0 0x39 0x2B
  let bar := hex 0x23 0x37 0x3B
  let (deck, deckDs) := elabStr ("\\documentclass{beamer}" ++
    "\\palette{ frametitlebg = #23373B, alert = #C0392B, bg = #FFFFFF }\\begin{document}" ++
    "\\begin{frame}{An \\textcolor{alert}{urgent} word}Body.\\end{frame}\\end{document}")
  let deckOut := layoutOf fonts deck
  t "declared colours: a role on the frame-title bar ships its declared ink"
    (let inks := inksOn deckOut (hasStr · "urgent")
     !inks.isEmpty && inks.contains accent)
  t "declared colours: the bar is the declared one"
    (deckOut.pages.any fun p => p.fills.any (·.color == bar))
  t "declared colours: the HTML title carries the declared ink"
    ((htmlStyles deck "urgent").any (hasStr · (HtmlDoc.cssColor accent)))
  t "declared colours: the pair on the bar is reported once, naming the bar"
    (let rs := reports deckDs
     rs.size == 1 && rs.all fun d =>
       d.code == "W0315" && hasStr d.message "the frame-title bar" && d.help.isNone)
  let fg := hex 0x23 0x37 0x3B
  let page := hex 0xFA 0xFA 0xFA
  let mixed := fg.mix 60 page
  let (mixDoc, mixDs) := elabStr ("\\documentclass{article}" ++
    "\\palette{ fg = #23373B, bg = #FAFAFA }\\begin{document}" ++
    "\\textcolor{fg!60!bg}{Mixed words here.}\\end{document}")
  t "declared colours: a mix ships xcolor's value in the PDF"
    (let inks := inksOn (layoutOf fonts mixDoc) (hasStr · "Mixed")
     !inks.isEmpty && inks.all (· == mixed))
  t "declared colours: a mix ships xcolor's value in the HTML"
    ((htmlStyles mixDoc "Mixed").any (· == s!"color: {HtmlDoc.cssColor mixed}"))
  t "declared colours: the mix is reported under the expression the author wrote"
    (let rs := reports mixDs
     rs.size == 1 && rs.all fun d => d.subject.any (·.startsWith "fg!60!bg:"))
  let red := hex 0xFF 0x00 0x00
  let comment := hex 0x60 0xA0 0xB0
  let source := "sorry -- note"
  let spec : Ir.ListingSpec :=
    { style := some .friendly
      highlight := #[#[{ kind := .genericError, text := "sorry" }, { kind := .text, text := " " },
        { kind := .comment, text := "-- note" }]] }
  let listing : Ir.Doc :=
    { (elabStr "\\documentclass{article}\\begin{document}x\\end{document}").1 with
      body := #[.verbatim none source spec] }
  let glyphs := ListingHighlight.glyphColors (layoutOf fonts listing)
  t "declared colours: the style's error red ships unmoved in the PDF"
    (glyphs.any (fun (c, ink) => c == 's' && ink == red) &&
     glyphs.all fun (c, ink) => c != 's' || ink == red)
  t "declared colours: the style's comment colour ships unmoved in the PDF"
    (glyphs.any fun (c, ink) => c == 'n' && ink == comment)
  let (_, listingHtml, _) := emitIn {} listing .print
  -- A coloured run's text, without the blanks that join a run and show no ink.
  let spans := (ListingHighlight.coloredSpansList #[] listingHtml.toList).map fun (txt, st) =>
    (txt.trimAscii.toString, st)
  t "declared colours: the style's colours ship unmoved in the HTML"
    (spans.any (fun (txt, st) => txt == "sorry" && hasStr st (HtmlDoc.cssColor red)) &&
     spans.any fun (txt, st) => txt == "-- note" && hasStr st (HtmlDoc.cssColor comment))
  t "declared colours: each failing token colour is reported once"
    (let rs := reports (Contrast.docDiags listing)
     rs.size == 2 && rs.all (·.code == "W0315"))
  -- A style's colour with no key is reported by the style; a palette code role by its key.
  t "declared colours: a style's token colour is reported under the style"
    (let rs := reports (Contrast.docDiags listing)
     rs.all fun d => hasStr d.message "'friendly' highlighting style" &&
       !hasStr d.message "'codeerror'" && !hasStr d.message "'codecomment'")
  let keyed : Ir.Doc :=
    { (elabStr ("\\documentclass{article}\\palette{ codecomment = #C0C0C0 }" ++
        "\\begin{document}x\\end{document}")).1 with body := #[.verbatim none source spec] }
  t "declared colours: a declared code role is reported under its key"
    ((reports (Contrast.docDiags keyed)).any fun d =>
      hasStr d.message "'codecomment'" && hasStr (diagWords d) "#C0C0C0 on")
  -- The medium's size: a grey between 3:1 and 4.5:1 on white.
  let greySrc (cls body : String) : String :=
    "\\documentclass{" ++ cls ++ "}\\palette{ bg = #FFFFFF }\\definecolor{quiet}{HTML}{808080}" ++
      "\\begin{document}" ++ body ++ "\\end{document}"
  t "declared colours: a deck's stage-size text asks 3:1"
    ((reports (elabStr (greySrc "beamer"
      "\\begin{frame}\\textcolor{quiet}{Grey words.}\\end{frame}")).2).isEmpty)
  t "declared colours: a document's page text asks 4.5:1"
    ((reports (elabStr (greySrc "article" "\\textcolor{quiet}{Grey words.}")).2).size == 1)
  -- An undeclared highlighting style is fitted to the listing's ground with nothing to report.
  let darkPage := hex 0x11 0x11 0x11
  let darkListing (env opts : String) : Ir.Doc × Array Diag :=
    elabStr ("\\documentclass{article}\\usepackage{minted}\\usepackage{listings}" ++
      "\\palette{ bg = #111111, fg = #EEEEEE }\\begin{document}\n" ++
      s!"\\begin\{{env}}{opts}\nx = \"text\"  # note\nprint(len(x))\n\\end\{{env}}\n" ++
      "\\end{document}")
  for (what, env, opts) in [("minted with no style", "minted", "{python}"),
      ("a listings listing", "lstlisting", "[language=Python]")] do
    let (doc, ds) := darkListing env opts
    let inks := (ListingHighlight.glyphColors (layoutOf fonts doc)).map (·.2)
    t s!"declared colours: {what} sets every token legibly on a dark page"
      (!inks.isEmpty && inks.all fun c => Contrast.aaText ≤ Contrast.contrastMilli c darkPage)
    t s!"declared colours: {what} draws no contrast report" (reports ds).isEmpty
  let (declDoc, declDs) := darkListing "minted" "[style=friendly]{python}"
  let friendlyString := (CodeColor.styleColor .friendly .literal).getD Ir.Color.black
  t "declared colours: a declared style's literal colour ships as stated on a dark page"
    ((ListingHighlight.glyphColors (layoutOf fonts declDoc)).any (·.2 == friendlyString))
  t "declared colours: a declared style's colours short of the dark page are reported"
    ((reports declDs).any fun d => hasStr d.message "'friendly' highlighting style")
  -- A declared accent short of non-text's 3:1 is reported once, where a link ships its focus ring.
  let focusSrc (body : String) : String :=
    "\\documentclass{article}\\palette{ accent = #FFE000 }\\begin{document}" ++ body ++
      "\\end{document}"
  t "declared colours: a failing focus ring is reported once, as the focus ring"
    (let rs := reports (elabStr (focusSrc "See \\href{https://example.org}{the probe}.")).2
     rs.size == 1 && rs.all fun d =>
       d.code == "W0345" && hasStr d.message "the focus ring" && hasStr d.message "SC 1.4.11")
  t "declared colours: a page with no link draws no focus ring to judge"
    ((reports (elabStr (focusSrc "No link here.")).2).isEmpty)
  for (what, body) in [("a reference", "\\section{One}\\label{one}See \\ref{one}."),
      ("a footnote", "Text\\footnote{An invented note}.")] do
    t s!"declared colours: {what} takes focus, so its ring is judged"
      ((reports (elabStr (focusSrc body)).2).any fun d => hasStr d.message "the focus ring")
  t "declared colours: a page shipping no stylesheet of the engine's draws no ring to judge"
    ((reports (elabStr ("\\documentclass{article}\\output{ css = none }" ++
      "\\palette{ accent = #FFE000 }\\begin{document}See " ++
      "\\href{https://example.org}{the probe}.\\end{document}")).2).isEmpty)
  t "declared colours: a legible document draws no contrast report"
    ((reports (elabStr ("\\documentclass{article}\\palette{ fg = #111111, bg = #FFFFFF, " ++
      "quiet = #444444 }\\begin{document}\\textcolor{quiet}{Dark words.}\\end{document}")).2).isEmpty)

/-- The focus ring is judged where a page draws it, two builds apart by the gate's own condition. -/
public def focusGateChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src (output : String) : String :=
    "\\documentclass{article}" ++ output ++ "\\palette{ accent = #FFE000 }\\begin{document}See " ++
      "\\href{https://example.org}{the probe}.\\end{document}"
  -- The page as the driver emits it: the stylesheet the document declares.
  let ring (doc : Ir.Doc) : Bool :=
    let css := match LeanTex.Cli.cssFor doc.output.css with
      | .own => HtmlDoc.CssMode.own
      | .bulma => HtmlDoc.CssMode.bulma
      | .none => HtmlDoc.CssMode.none
    hasStr (HtmlDoc.emit { css } doc).1 ":focus-visible"
  let (styled, styledDs) := elabStr (src "")
  let (bare, bareDs) := elabStr (src "\\output{ css = none }")
  t "focus gate: the page the engine styles draws the ring and reports its accent"
    (ring styled && (reports styledDs).any (·.code == "W0345"))
  t "focus gate: the page with no engine stylesheet draws no ring and reports none"
    (!ring bare && !(reports bareDs).any (·.code == "W0345"))
  let (_, pdfDs) := elabStr (src "\\output{ formats = pdf }")
  t "focus gate: a document declaring only PDF builds no page and reports no ring"
    (!(({ cmd := .build "probe.tex" } : LeanTex.Cli.Config).effectiveEmit #["pdf"]).contains .html &&
      !(reports pdfDs).any (·.code == "W0345"))
  let (_, bothDs) := elabStr (src "\\output{ formats = pdf, html }")
  t "focus gate: a document declaring HTML among its formats has its ring judged"
    ((({ cmd := .build "probe.tex" } : LeanTex.Cli.Config).effectiveEmit #["pdf", "html"]).contains .html &&
      (reports bothDs).any (·.code == "W0345"))

/-- A deck's focused stage draws the deck's mark, never the browser's ring, a rule in its ink, which
its ground holds legible, down the middle half of each side margin, or in forced colours a ring on
its own edge, and the pager, which owns the keys, takes the stages out of the tab order. -/
public def stageFocusChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (deckDoc, deckDs) := elabStr ("\\documentclass{beamer}\\palette{ focus = #FFE000 }" ++
    "\\begin{document}\\begin{frame}{Placeholder}A line with no link.\\end{frame}" ++
    "\\begin{frame}[standout]Questions?\\end{frame}\\end{document}")
  t "stage focus: a stage marks in its ink, so a focus colour no link ships is not judged"
    (!(reports deckDs).any fun d => d.code == "W0345" && hasStr d.message "the focus ring")
  let side := "max(2px, calc(0.5 * var(--safearea, 6vmin)))"
  t "stage focus: a focused stage's mark is its background, a rule down each side margin's middle half"
    (hasStr (HtmlDoc.emit {} deckDoc).1
      ("html section.slide:focus-visible, html section.section-page:focus-visible { outline: none; " ++
        "background-image: linear-gradient(currentColor, currentColor), " ++
        "linear-gradient(currentColor, currentColor); background-size: 2px 50%; " ++
        s!"background-position: left {side} center, right {side} center; " ++
        "background-repeat: no-repeat; }"))
  t "stage focus: in forced colours, which drop the mark, a focused stage rings its own edge"
    (hasStr (HtmlDoc.emit {} deckDoc).1
      ("@media (forced-colors: active) { html section.slide:focus-visible, " ++
        "html section.section-page:focus-visible { outline: 2px solid currentColor; " ++
        "outline-offset: -2px; } }"))
  t "stage focus: the pager takes the stages out of the tab order"
    (hasStr HtmlDoc.deckScript
      ("const stops = \"section.slide[tabindex], section.section-page[tabindex]\";\n" ++
        "  for (const s of document.querySelectorAll(stops)) s.removeAttribute(\"tabindex\");"))

/-- The ink of every glyph of `c` the pages set, outside furniture. -/
private def charInks (out : Layout.Out) (c : Char) : Array Ir.Color :=
  (ListingHighlight.glyphColors out).filterMap fun (g, ink) => if g == c then some ink else none

/-- A listing's plain text reads on the ground the listing declares, in one colour in both
artifacts, while a declared code ink ships as declared and is reported once. -/
public def listingGroundChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let listing (cls pre opts : String) : String :=
    "\\documentclass{" ++ cls ++ "}\\usepackage{minted}" ++ pre ++ "\\begin{document}\n" ++
      (if cls == "beamer" then "\\begin{frame}\n" else "") ++
      s!"\\begin\{minted}[{opts}]\{python}\ndef f(x):\n    return x + 1\n\\end\{minted}\n" ++
      (if cls == "beamer" then "\\end{frame}\n" else "") ++ "\\end{document}"
  let probes : List (String × String × String × String × Ir.Color) := [
    ("no palette on a black ground", "article", "", "bgcolor=black", Ir.Color.black),
    ("a declared ink on a black ground", "article", "\\palette{ fg = #111111 }", "bgcolor=black",
      Ir.Color.black),
    ("an author colour as the ground", "article", "\\definecolor{bg}{HTML}{282C34}", "bgcolor=bg",
      hex 0x28 0x2C 0x34),
    ("a dark page under a white ground", "article", "\\palette{ bg = #111111, fg = #EEEEEE }",
      "bgcolor=white", Ir.Color.white),
    ("a deck on a black ground", "beamer", "", "bgcolor=black", Ir.Color.black)]
  for (what, cls, pre, opts, ground) in probes do
    let (doc, ds) := elabStr (listing cls pre opts)
    let out := layoutOf fonts doc
    let inks := charInks out '+' ++ charInks out '('
    t s!"listing ground: {what}: the plain text reads on the ground in the PDF"
      (!inks.isEmpty && inks.all fun c => Contrast.aaText ≤ Contrast.contrastMilli c ground)
    t s!"listing ground: {what}: the HTML listing sets the PDF's plain-text colour"
      (let styles := (htmlStyles doc "return").filter (hasStr · "background:")
       !styles.isEmpty && inks.all fun c =>
         styles.all fun st => cssProperty st "color" == some (HtmlDoc.cssColor c))
    t s!"listing ground: {what}: nothing to report" (reports ds).isEmpty
  let declared := hex 0x22 0x22 0x22
  let (keyDoc, keyDs) := elabStr (listing "article" "\\palette{ codeink = #222222 }" "bgcolor=black")
  t "listing ground: a declared code ink ships as declared on the ground"
    (let inks := charInks (layoutOf fonts keyDoc) '+'
     !inks.isEmpty && inks.all (· == declared))
  t "listing ground: a declared code ink short of the ground is reported once"
    (let rs := reports keyDs
     rs.size == 1 && rs.all fun d => hasStr d.message "'codeink'")

end Tests.DeclaredColors
