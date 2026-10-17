module

public import Tests.Support
public import Tests.Icc
public import LeanTex.Core.PdfX

public section

open LeanTex.Core

namespace Tests.PrintColour

/-- A source elaborated with an output profile's transform, as the driver elaborates a document
declaring one. -/
def elabThrough (t : Option Icc.Transform) (src : String) : Ir.Doc × Array Diag :=
  let prepared := { Elab.prepare "t" (Parse.parse "t" (Lex.lex "t" src).1).1 with profile := t }
  Elab.runPreparedFinal "t" prepared #[] (fun _ _ => {})

/-- An invented print article in CMYK, `body` on its page. -/
private def card (pre body : String) : String :=
  "\\documentclass{article}\n\\usepackage{xcolor}\n\\usepackage{colorspace}\n" ++
    "\\definecolor{accent}{cmyk}{0,.7,1,0}\n\\definespotcolor{ink}{Probe Ink}{.2,.9,0,.1}\n" ++ pre ++
    "\\begin{document}\n" ++ body ++ "\n\\end{document}"

/-- A document's web page and its PDF, written under the invented press's output profile when
`pressed`. -/
private def artifacts (oneFace : Font.FontSet) (doc : Ir.Doc) (pressed : Bool) :
    String × ByteArray :=
  let geom := Layout.Geom.ofPage doc.page
  let imgs : Image.Store := { profile := if pressed then some Tests.Icc.press else none }
  ((HtmlDoc.emit {} doc).1, Pdf.write geom oneFace (layoutOf oneFace doc geom).pages doc.info imgs)

/-- The device spaces a PDF paints in, as the PDF/X judge reads them. -/
private def devices (b : ByteArray) : Array String :=
  ((PdfX.read b).toOption.map (·.devices)).getD #["unread"]

/-- Whether a PDF's inflated streams hold `s`. -/
private def paints (b : ByteArray) (s : String) : Bool := bytesContain (pdfText b) s

/-- Unit components as the 16-bit values a transform reads. -/
private def at16 (vs : List Rat) : Array Nat := vs.toArray.map fun v => (v * 65535 + 1 / 2).floor.toNat

/-- A screen colour as CSS spells it. -/
private def css (rgb : UInt8 × UInt8 × UInt8) : String :=
  ({ r := rgb.1, g := rgb.2.1, b := rgb.2.2 } : Ir.Color).css

/-- A CMYK colour, a tint of an ink and a CMYK mix show on the web page, and in the contrast the
page is judged by, as the declared output profile shows them, the PDF painting the same inks; a
mix in RGB keeps xcolor's own numbers; with no profile the preview is xcolor's. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let some press := Icc.Transform.of? Tests.Icc.press | t "the invented press reads" false
  let accent := css (press.toSrgb (at16 [0, 7 / 10, 1, 0]))
  let half := css (press.toSrgb (at16 [0, 7 / 20, 1 / 2, 0]))
  let tint := css (press.toSrgb (at16 [1 / 10, 9 / 20, 0, 1 / 20]))
  t "the invented press shows the accent unlike xcolor's projection" (accent != "#ff4d00")
  let src := card "" ("\\textcolor{accent}{Alpha} \\textcolor{accent!50}{Beta} " ++
    "\\textcolor{ink!50}{Gamma} \\textcolor{red!50!accent}{Delta}")
  let (doc, ds) := elabThrough (some press) src
  let (html, pdf) := artifacts oneFace doc true
  let (plain, plainDs) := elabThrough none src
  let (plainHtml, plainPdf) := artifacts oneFace plain false
  t s!"the web page shows the accent, its mix and the ink's tint through the profile: {accent}, {half}, {tint}"
    (hasStr html accent && hasStr html half && hasStr html tint && !hasStr html "#ff4d00")
  t "the PDF paints the declared inks either way"
    (paints pdf "0 0.7 1 0 k" && paints pdf "/Ink.Probe#20Ink cs 0.5 scn" &&
      paints plainPdf "0 0.7 1 0 k")
  t "an RGB mix of the accent paints the same RGB under the press as under no profile"
    (paints pdf "1 0.153 0 rg" && paints plainPdf "1 0.153 0 rg")
  let mixes := card "" "\\textcolor{red!30}{Alpha} \\textcolor{blue!20}{Beta} \\textcolor{red}{Gamma}"
  let (_, mixPdf) := artifacts oneFace (elabThrough (some press) mixes).1 true
  t "a declared RGB colour and its mixes paint as declared under the press, none of them pressed"
    (paints mixPdf "1 0.702 0.702 rg" && paints mixPdf "0.8 0.8 1 rg" &&
      paints mixPdf "1 0 0 rg" && (devices mixPdf).contains "DeviceRGB")
  t "under no profile the accent shows as xcolor projects it"
    (hasStr plainHtml "#ff4d00" && !hasStr plainHtml accent)
  let judged (ds : Array Diag) (hex : String) : Bool :=
    ds.any fun d => d.code == DiagCode.W0315.code &&
      ((d.detail.getD "") ++ d.message).toLower.contains hex
  t "the contrast the page is judged by reads the accent through the profile"
    (judged ds accent && !judged ds "#ff4d00" && judged plainDs "#ff4d00")
  -- The engine's own colours: a listing's derived inks, a placeholder, an RGB stop of a shading.
  let engine := card "\\usepackage{listings}\n\\usepackage{graphicx}\n\\usepackage{tikz}\n"
    ("\\begin{lstlisting}[language=Python]\ndef f(x):\n    return \"s\" + 1  # note\n" ++
      "\\end{lstlisting}\n\\includegraphics{absent.png}\n" ++
      "\\tikz \\shade[left color=accent, right color=ink!30] (0,0) rectangle (2,1);")
  let (edoc, _) := elabThrough (some press) engine
  let geom := Layout.Geom.ofPage edoc.page
  let pages := (layoutOf oneFace edoc geom).pages
  let pressed := Pdf.write geom oneFace pages edoc.info { profile := some Tests.Icc.press }
  let unpressed := Pdf.write geom oneFace pages edoc.info
  t "under no output profile the engine's own colours paint in DeviceRGB"
    ((devices unpressed).contains "DeviceRGB")
  t "under a CMYK output profile nothing paints in DeviceRGB: the listing, the placeholder and the shading print in the press"
    (!(devices pressed).contains "DeviceRGB" && (devices pressed).contains "DeviceCMYK" &&
      bytesContain (pdfText pressed) "/ShadingType 2 /ColorSpace /DeviceCMYK")
  let placeholder := Pdf.pressColor press Pdf.placeholderInk
  t "the placeholder's hairline prints as the press prints its grey, its screen grey kept"
    (match placeholder.pdfModel with
      | some (.cmyk ..) => placeholder.r == 158 && placeholder.b == 168
      | _ => false)
  let neutral := Pdf.pressColor press ({ r := 128, g := 128, b := 128 } : Ir.Color)
  t "an engine grey prints in black ink alone, as light as the press shows it"
    (match neutral.pdfModel with
      | some (.gray v) => v == Ir.Color.pdfMilli ((65535 - press.blackFor 128) * 1000 / 65535)
      | _ => false)
  t "a declared grey and a declared RGB colour are not pressed"
    ((Pdf.pressColor press ({ r := 128, g := 128, b := 128 } : Ir.Color).declared).pdfModel == none &&
      (Pdf.pressColor press (Ir.Color.ofHtml 255 0 0)).pdfModel == (Ir.Color.ofHtml 255 0 0).pdfModel)
  -- A themed deck's colours are the engine's: none of them paints in DeviceRGB under the press.
  let deck := "\\documentclass{beamer}\n\\usetheme{moloch}\n\\begin{document}\n" ++
    "\\begin{frame}{Probe}\nAlpha \\alert{Beta}\n\\end{frame}\n\\end{document}"
  let (themed, _) := elabThrough (some press) deck
  let (_, themedPdf) := artifacts oneFace themed true
  let (_, themedPlain) := artifacts oneFace themed false
  t "a theme's colours paint in DeviceRGB under no profile and in the press under a CMYK one"
    ((devices themedPlain).contains "DeviceRGB" && !(devices themedPdf).contains "DeviceRGB" &&
      (devices themedPdf).contains "DeviceCMYK")
  -- Colours the engine derives at a site, not from a palette slot, are its own too.
  let derived := [("covered steps", "\\documentclass{beamer}\n\\usetheme{moloch}\n" ++
      "\\setbeamercovered{transparent}\n\\begin{document}\n\\begin{frame}{Probe}\n" ++
      "\\begin{itemize}\n\\item<1-> Alpha\n\\item<2-> Beta\n\\end{itemize}\n\\end{frame}\n\\end{document}"),
    ("generated tones on a block and a standout frame", "\\documentclass{beamer}\n\\begin{document}\n" ++
      "\\begin{frame}{Probe}\n\\begin{block}{Block}\n\\textcolor{muted}{Quiet} \\alert{Loud}\n" ++
      "\\end{block}\n\\end{frame}\n\\begin{frame}[standout]\n\\alert{Loud} \\textcolor{muted}{Quiet}\n" ++
      "\\end{frame}\n\\end{document}"),
    ("a pin's grey", "\\documentclass{article}\n\\usepackage{tikz}\n\\begin{document}\n" ++
      "\\tikz \\node[draw, pin=above:Note] {Alpha};\n\\end{document}")]
  for (what, src) in derived do
    let (ddoc, _) := elabThrough (some press) src
    let (_, dpdf) := artifacts oneFace ddoc true
    t s!"under the press, {what} paint in no DeviceRGB: {devices dpdf}" (!(devices dpdf).contains "DeviceRGB")
  let seeded := "\\documentclass{article}\n\\palette[seeds]{ ink = #2B2440, paper = #FFFFFF, " ++
    "accent = #1D4ED8 }\n\\begin{document}\nAlpha \\textcolor{accent}{Beta}\n\\end{document}"
  let (sdoc, _) := elabThrough (some press) seeded
  let (_, spdf) := artifacts oneFace sdoc true
  t "a seed a palette declares paints as declared under the press"
    (paints spdf (Ir.Color.ofHtml 0x1D 0x4E 0xD8).pdfFill)

/-- Every CMYK colour the engine mixes shows through the profile as the palette's do: a listing's
ink fitted to its ground, a shading's stops, a ball's and an ink declared again, the contrast the
page is judged by reading the same colour. -/
def previewChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let some press := Icc.Transform.of? Tests.Icc.press | t "the invented press reads" false
  let shown (vs : List Rat) : String := css (press.toSrgb (at16 vs))
  let naive (vs : List Rat) : String :=
    let ch (i : Nat) : UInt8 := Ir.inkPreviewByte (vs.getD i 0) (vs.getD 3 0)
    ({ r := ch 0, g := ch 1, b := ch 2 } : Ir.Color).css
  let listing := card "\\usepackage{listings}\n\\palette{ tint = gray!50 }\n"
    "{\\color{accent}\nSome text.\n\\begin{lstlisting}\nplain words here\n\\end{lstlisting}\n}"
  -- The bisection finds the step the scan of every step finds.
  let scan (pal : Ir.Palette) (req : Nat) (ground seed : Ir.Color) : Ir.Color := Id.run do
    if Contrast.contrastMilli seed ground ≥ req then return seed
    let pole := if Contrast.contrastMilli Ir.Color.black ground >
        Contrast.contrastMilli Ir.Color.white ground then Ir.Color.black else Ir.Color.white
    for step in [1:101] do
      let c := pal.mix seed (100 - step) pole
      if Contrast.contrastMilli c ground ≥ req then return c
    return pole
  let shownPal : Ir.Palette := { profile := some press }
  let mut st : UInt64 := 88172645463325252
  let mut same := true
  for i in [0:400] do
    let (r, s1) := rand st 256
    let (g, s2) := rand s1 256
    let (b, s3) := rand s2 256
    let (gr, s4) := rand s3 256
    st := s4
    let seed : Ir.Color := if i % 2 == 0 then { r := UInt8.ofNat r, g := UInt8.ofNat g, b := UInt8.ofNat b }
      else shownPal.shown (Ir.Color.ofCmyk (r * 1000 / 255) (g * 1000 / 255) (b * 1000 / 255) 0)
    let ground : Ir.Color := { r := UInt8.ofNat gr, g := UInt8.ofNat gr, b := UInt8.ofNat ((gr + 40) % 256) }
    for req in [3000, 4500, 7000] do
      let a := Listing.fitInk shownPal req ground seed
      let z := scan shownPal req ground seed
      same := same && a == z
  t "a fitted ink found by bisection is the one the scan of every step finds" same
  let (_, lds) := elabThrough (some press) listing
  t "a listing's ink fitted to its ground from a CMYK colour is judged as the profile shows it"
    (!lds.any fun d => d.code == DiagCode.W0315.code && ((d.detail.getD "") ++ d.message).contains "listing")
  let shades := card "\\usepackage{tikz}\n"
    ("\\tikz \\shade[left color=accent, right color=white] (0,0) rectangle (2,1);\n" ++
      "\\tikz \\shade[ball color=cyan] (0,0) circle (1);")
  let (sdoc, _) := elabThrough (some press) shades
  let (shtml, spdf) := artifacts oneFace sdoc true
  t s!"a shading's mixed stop shows through the profile: {shown [0, 7 / 20, 1 / 2, 0]}"
    (hasStr shtml (shown [0, 7 / 20, 1 / 2, 0]) && !hasStr shtml (naive [0, 7 / 20, 1 / 2, 0]))
  t s!"a ball's stops show through the profile: {shown [15 / 100, 0, 0, 0]}"
    (hasStr shtml (shown [15 / 100, 0, 0, 0]) && !hasStr shtml (naive [15 / 100, 0, 0, 0]))
  t "a CMYK shading to white prints its white stop in black ink alone, in DeviceCMYK"
    (paints spdf "/ShadingType 2 /ColorSpace /DeviceCMYK" && !(devices spdf).contains "DeviceRGB")
  let inks := card "" ("\\definespotcolor{again}{Probe Ink}{.3,.8,0,.1}\n" ++
    "\\textcolor{ink}{Alpha} \\textcolor{again}{Beta}")
  let (idoc, _) := elabThrough (some press) inks
  let (ihtml, _) := artifacts oneFace idoc false
  t s!"an ink declared again shows its first alternate through the profile: {shown [2 / 10, 9 / 10, 0, 1 / 10]}"
    (hasStr ihtml (shown [2 / 10, 9 / 10, 0, 1 / 10]) && !hasStr ihtml (naive [2 / 10, 9 / 10, 0, 1 / 10]))

/-- The driver reads a declared output profile beside the document before it elaborates, so the
built web page shows a CMYK colour through it and the built PDF embeds it as its intent and paints
the engine's own colours in its press. -/
def driverChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some press := Icc.Transform.of? Tests.Icc.press | t "the invented press reads" false
  let accent := css (press.toSrgb (at16 [0, 7 / 10, 1, 0]))
  let dir ← IO.FS.createTempDir
  IO.FS.writeBinFile (dir / "face.ttf") (← IO.FS.readBinFile (testFonts ++ "/OpenSans-Regular.ttf"))
  IO.FS.writeBinFile (dir / "press.icc") Tests.Icc.press
  IO.FS.writeFile (dir / "card.tex") ("\\DocumentMetadata{colorprofiles={X=press.icc}}\n" ++
    "\\documentclass{article}\n\\usepackage{xcolor}\n" ++
    "\\output{ formats = pdf, html }\n\\definecolor{accent}{cmyk}{0,.7,1,0}\n" ++
    "\\begin{document}\n\\textcolor{accent}{Alpha}\n\\end{document}\n")
  let run ← engineRun dir #["card.tex", "--best-effort"] (dir / "face.ttf") (dir / "cache")
  let html ← if ← (dir / "card.html").pathExists then IO.FS.readFile (dir / "card.html") else pure ""
  let pdf ← if ← (dir / "card.pdf").pathExists then
      (pdfText <$> IO.FS.readBinFile (dir / "card.pdf")) else pure ByteArray.empty
  t s!"the built page shows the accent through the profile beside the document ({run.exitCode}): {run.stderr}"
    (hasStr html accent && !hasStr html "#ff4d00")
  t "the built PDF embeds the profile as its intent and paints the declared ink"
    (bytesContain pdf "/OutputIntents" && bytesContain pdf "0 0.7 1 0 k")
  IO.FS.removeDirAll dir

end Tests.PrintColour
