module

public import Tests.ListingHighlight

public section

open LeanTex.Core

namespace Tests.DeclaredColors

private def hex (r g b : UInt8) : Ir.Color := { r, g, b }

/-- The inks of every glyph run on a line holding `text`. -/
private def inksOn (out : Layout.Out) (text : String) : Array Ir.Color :=
  (allLines out).filter (fun l => hasStr (lineText l) text) |>.flatMap fun l =>
    l.segs.filterMap fun
      | .run _ ink _ _ glyphs .. => if glyphs.isEmpty then none else some ink
      | _ => none

/-- The styles of the HTML elements whose text holds `text`. -/
private def htmlStyles (doc : Ir.Doc) (text : String) : Array String :=
  let (_, body, _) := HtmlDoc.emitTree {} doc
  (elemStylesList #[] body.toList).filterMap fun (t, st) =>
    if hasStr t text && !st.isEmpty then some st else none

/-- The contrast reports a run shows: the warnings, never the notes that
carry a pairing's later runs. -/
private def reports (ds : Array Diag) : Array Diag :=
  ds.filter fun d => (d.code == "W0315" || d.code == "W0345" || d.code == "W0330") &&
    d.severity == .warning

/-- **A declared colour ships as declared, in both artifacts, and its
contrast is reported once.** A colour a document states — a role, an author
colour, a mix of two named colours, a highlighting style's token colour —
is the colour the PDF's glyph runs and the HTML's spans carry, on the page
and on every local ground; a pairing that falls short of what its medium
asks is one warning, on one line, with no repair named. A deck's stage
shows its text at the size of the screen, so it asks large-scale text's
3:1 where a document's page asks 4.5:1. Read off `Layout.Out` and the typed
HTML tree. -/
public def checks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  -- A role on the page: an orange that fails a document's 4.5:1.
  let orange := hex 0xE9 0x6A 0x10
  let (doc, ds) := elabStr ("\\documentclass{article}\\palette{ alert = #E96A10 }" ++
    "\\begin{document}\\textcolor{alert}{Warm word} and plain text.\\end{document}")
  let out := layoutOf fonts doc
  t "declared colours: a failing role ships its declared ink on the page"
    (let inks := inksOn out "Warm word"
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
    (let inks := inksOn deckOut "urgent"
     !inks.isEmpty && inks.contains accent)
  t "declared colours: the bar is the declared one"
    (deckOut.pages.any fun p => p.fills.any (·.color == bar))
  t "declared colours: the HTML title carries the declared ink"
    ((htmlStyles deck "urgent").any (hasStr · (HtmlDoc.cssColor accent)))
  t "declared colours: the pair on the bar is reported once, naming the bar"
    (let rs := reports deckDs
     rs.size == 1 && rs.all fun d =>
       d.code == "W0315" && hasStr d.message "the frame-title bar" && d.help.isNone)
  -- A mix of two named colours ships xcolor's value.
  let fg := hex 0x23 0x37 0x3B
  let page := hex 0xFA 0xFA 0xFA
  let mixed := fg.mix 60 page
  let (mixDoc, mixDs) := elabStr ("\\documentclass{article}" ++
    "\\palette{ fg = #23373B, bg = #FAFAFA }\\begin{document}" ++
    "\\textcolor{fg!60!bg}{Mixed words here.}\\end{document}")
  t "declared colours: a mix ships xcolor's value in the PDF"
    (let inks := inksOn (layoutOf fonts mixDoc) "Mixed"
     !inks.isEmpty && inks.all (· == mixed))
  t "declared colours: a mix ships xcolor's value in the HTML"
    ((htmlStyles mixDoc "Mixed").any (· == s!"color: {HtmlDoc.cssColor mixed}"))
  t "declared colours: the mix is reported under the expression the author wrote"
    (let rs := reports mixDs
     rs.size == 1 && rs.all fun d => d.subject.any (·.startsWith "fg!60!bg:"))
  -- A highlighting style's token colours ship as the style states them.
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
  let (_, listingHtml, _) := HtmlDoc.emitTree {} listing
  -- A coloured run's text, without the blanks that join a run and show no ink.
  let spans := (ListingHighlight.coloredSpansList #[] listingHtml.toList).map fun (txt, st) =>
    (txt.trimAscii.toString, st)
  t "declared colours: the style's colours ship unmoved in the HTML"
    (spans.any (fun (txt, st) => txt == "sorry" && hasStr st (HtmlDoc.cssColor red)) &&
     spans.any fun (txt, st) => txt == "-- note" && hasStr st (HtmlDoc.cssColor comment))
  t "declared colours: each failing token colour is reported once"
    (let rs := reports (Contrast.docDiags listing)
     rs.size == 2 && rs.all (·.code == "W0315"))
  -- The document wrote no key for a style's colour: the report names the
  -- style, and a code role the palette declares is named by its key.
  t "declared colours: a style's token colour is reported under the style"
    (let rs := reports (Contrast.docDiags listing)
     rs.all fun d => hasStr d.message "'friendly' highlighting style" &&
       !hasStr d.message "'codeerror'" && !hasStr d.message "'codecomment'")
  let keyed : Ir.Doc :=
    { (elabStr ("\\documentclass{article}\\palette{ codecomment = #C0C0C0 }" ++
        "\\begin{document}x\\end{document}")).1 with body := #[.verbatim none source spec] }
  t "declared colours: a declared code role is reported under its key"
    ((reports (Contrast.docDiags keyed)).any fun d =>
      hasStr d.message "'codecomment' (#C0C0C0)")
  -- The medium's size: a grey between 3:1 and 4.5:1 on white.
  let greySrc (cls body : String) : String :=
    "\\documentclass{" ++ cls ++ "}\\palette{ bg = #FFFFFF }\\definecolor{quiet}{HTML}{808080}" ++
      "\\begin{document}" ++ body ++ "\\end{document}"
  t "declared colours: a deck's stage-size text asks 3:1"
    ((reports (elabStr (greySrc "beamer"
      "\\begin{frame}\\textcolor{quiet}{Grey words.}\\end{frame}")).2).isEmpty)
  t "declared colours: a document's page text asks 4.5:1"
    ((reports (elabStr (greySrc "article" "\\textcolor{quiet}{Grey words.}")).2).size == 1)
  -- A highlighting style the document never declared is the engine's own
  -- choice of colours: fitted to the ground the listing stands on, in both
  -- artifacts, with nothing to report. A declared style ships as it states.
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
  -- The focus ring a link draws on the HTML page: a declared accent short of
  -- non-text's 3:1 is reported once, where a link ships.
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
  -- A legible document says nothing.
  t "declared colours: a legible document draws no contrast report"
    ((reports (elabStr ("\\documentclass{article}\\palette{ fg = #111111, bg = #FFFFFF, " ++
      "quiet = #444444 }\\begin{document}\\textcolor{quiet}{Dark words.}\\end{document}")).2).isEmpty)

end Tests.DeclaredColors
