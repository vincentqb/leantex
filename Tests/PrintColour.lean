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

/-- A document's web page and its PDF with streams inflated. -/
private def artifacts (oneFace : Font.FontSet) (doc : Ir.Doc) : String × ByteArray :=
  let geom := Layout.Geom.ofPage doc.page
  ((HtmlDoc.emit {} doc).1, pdfText (Pdf.write geom oneFace (layoutOf oneFace doc geom).pages doc.info))

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
  let (html, pdf) := artifacts oneFace doc
  let (plain, plainDs) := elabThrough none src
  let (plainHtml, plainPdf) := artifacts oneFace plain
  t s!"the web page shows the accent, its mix and the ink's tint through the profile: {accent}, {half}, {tint}"
    (hasStr html accent && hasStr html half && hasStr html tint && !hasStr html "#ff4d00")
  t "the PDF paints the declared inks either way"
    (bytesContain pdf "0 0.7 1 0 k" && bytesContain pdf "/Ink.Probe#20Ink cs 0.5 scn" &&
      bytesContain plainPdf "0 0.7 1 0 k")
  t "an RGB mix of the accent paints xcolor's numbers, whatever the profile shows"
    (bytesContain pdf "1 0.153 0 rg" && bytesContain plainPdf "1 0.153 0 rg")
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
  let devices (b : ByteArray) : Array String := ((PdfX.read b).toOption.map (·.devices)).getD #["unread"]
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
