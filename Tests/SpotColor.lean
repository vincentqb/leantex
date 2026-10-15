module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.SpotColor

/-- An article loading colorspace with one invented ink, `pre` after it. -/
private def probe (pre body : String) : String :=
  "\\documentclass{article}\n\\usepackage{xcolor}\n\\usepackage{colorspace}\n\\usepackage{tikz}\n" ++
    "\\definespotcolor{ink}{Probe Ink}{0,.5,1,0}\n" ++ pre ++ "\\begin{document}\n" ++ body ++
    "\n\\end{document}"

/-- One elaborated document's diagnostics, its PDF with streams inflated, and its web page. -/
private def artifacts (oneFace : Font.FontSet) (src : String) : Array Diag × ByteArray × String :=
  let (doc, ds) := elabStr src
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf oneFace doc geom
  (ds ++ out.diags, pdfText (Pdf.write geom oneFace out.pages doc.info), (HtmlDoc.emit {} doc).1)

private def codes (ds : Array Diag) (c : DiagCode) : Nat := (ds.filter (·.code == c.code)).size

/-- The probe ink. -/
private def probeInk : Ir.Ink := { name := "Probe Ink", c := 0, m := 1 / 2, y := 1, k := 0 }

/-- A spot colour is a `/Separation` named by its colorant over its CMYK alternate, painted at the
tint `!` over the paper sets wherever the document paints, previewed on the web page; a mix that is
no tint of its ink is a named process colour. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (ds, pdf, html) := artifacts oneFace (probe "" "\\textcolor{ink}{Alpha}")
  t "an ink reads with no error, no skipped package and no unknown command"
    (ds.all (·.severity != .error) && codes ds .W0440 == 0 && codes ds .W0441 == 0 &&
      codes ds .W0103 == 0 && codes ds .W0301 == 0)
  t "the ink's space is a Separation named by its colorant over its DeviceCMYK alternate"
    (bytesContain pdf ("/ColorSpace << /Ink.Probe#20Ink [/Separation /Probe#20Ink /DeviceCMYK " ++
      "<< /FunctionType 2 /Domain [0 1] /C0 [0 0 0 0] /C1 [0 0.5 1 0] /N 1 >>] >>"))
  t "the ink at full tint paints its separation at tint 1, and no device colour stands in"
    (bytesContain pdf "/Ink.Probe#20Ink cs 1 scn" && !bytesContain pdf "0 0.5 1 0 k")
  t "the web page shows the alternate's preview" (hasStr html "#ff8000")
  let (ods, _, ohtml) := artifacts oneFace (probe "" "A \\textoverprint{\\mbox{Over}} B")
  t "an overprinted text is kept and read as any text is, its overprint alone named"
    (codes ods .W0104 == 1 && codes ods .W0301 == 0 && hasStr ohtml "A Over B")
  -- Each expression alone on its page, so the tint it ships is its own.
  let tintOf (pre expr : String) : ByteArray × String :=
    let (_, p, h) := artifacts oneFace (probe pre s!"\\textcolor\{{expr}}\{Alpha}")
    (p, h)
  for (pre, expr, tint, preview) in [
      ("", "ink!50", "0.5", "#ffbf80"), ("", "ink!50!white", "0.5", "#ffbf80"),
      ("", "ink!25!white!50", "0.125", "#ffefdf"), ("\\colorlet{alias}{ink}\n", "alias", "1", "#ff8000"),
      ("\\colorlet{pale}{ink!30}\n", "pale", "0.3", "#ffd9b2"), ("", "ink!50!ink", "1", "#ff8000"),
      ("", "white!50!ink", "0.5", "#ffbf80"), ("", "ink!100!black", "1", "#ff8000"),
      ("", "ink!0", "0", "#ffffff")] do
    let (p, h) := tintOf pre expr
    t s!"'{expr}' paints the ink at tint {tint}, previewed {preview}"
      (bytesContain p s!"/Ink.Probe#20Ink cs {tint} scn" && hasStr h preview)
  let (_, rpdf, _) := artifacts oneFace (probe "" "\\textcolor{ink}{\\rule{2em}{1pt}}")
  t "a rule in the ink is filled in its separation"
    (bytesContain rpdf "q /Ink.Probe#20Ink cs 1 scn ")
  let (fds, fpdf, _) := artifacts oneFace (probe ""
    ("\\begin{tikzpicture}\\draw[ink, line width=1pt] (0,0) -- (2,0);" ++
      "\\shade[left color=ink, right color=white] (0,1) rectangle (2,2);\\end{tikzpicture}"))
  t "a picture strokes in the ink, and its form names the separation in the shared resources"
    (bytesContain fpdf "/Ink.Probe#20Ink CS 1 SCN" &&
      bytesContain fpdf "/ColorSpace << /Ink.Probe#20Ink [/Separation /Probe#20Ink" &&
      codes fds .W0440 == 0)
  t "a gradient from the ink to the paper is shaded through the ink's tints in its separation"
    (bytesContain fpdf "/ShadingType 2 /ColorSpace [/Separation /Probe#20Ink /DeviceCMYK" &&
      bytesContain fpdf "/C0 [0.5] /C1 [1] /N 1" && !bytesContain fpdf "/ColorSpace /DeviceRGB")
  -- lualatex stops with an error on a mix of an ink with black or a process colour, and ships an
  -- ink mixed with another ink silently as the first ink at tint 1.
  let (mds, mpdf, mhtml) := artifacts oneFace
    (probe "\\definespotcolor{other}{Other Ink}{.2,0,0,.1}\n"
      "\\textcolor{ink!50!black}{Alpha} \\textcolor{ink!40!other}{Beta} \\textcolor{other}{Gamma}")
  t "a mix of the ink with black or another ink is named once per expression, in text"
    (codes mds .W0440 == 2 && mds.all (·.severity != .error))
  t "the mix with black is the process mix of the alternate, in PDF and on screen"
    (bytesContain mpdf "0 0.25 0.5 0.5 k" && hasStr mhtml "#804000")
  t "a second ink is a second separation, named by its own colorant"
    (bytesContain mpdf "/Ink.Other#20Ink [/Separation /Other#20Ink /DeviceCMYK " &&
      bytesContain mpdf "/C1 [0.2 0 0 0.1]" && bytesContain mpdf "/Ink.Other#20Ink cs 1 scn")
  let (pds, ppdf, _) := artifacts oneFace (probe ""
    ("\\begin{tikzpicture}\\fill[ink!50!black] (0,0) rectangle (1,1);" ++
      "\\shade[left color=ink, right color=black] (0,1) rectangle (1,2);\\end{tikzpicture}\n\n" ++
      "$\\color{ink!60!black} x$"))
  t "a mix lost in a picture, a gradient into another colour and a mix in a formula are named"
    (codes pds .W0440 == 3 && bytesContain ppdf "0 0.25 0.5 0.5 k")
  let (uds, updf, _) := artifacts oneFace
    (probe "\\definespotcolor{again}{Probe Ink}{1,0,0,0}\n" "\\textcolor{again}{Alpha}")
  t "a colorant declared again with another alternate is named, and its first alternate stands"
    (codes uds .W0441 == 1 && bytesContain updf "/C1 [0 0.5 1 0]" &&
      !bytesContain updf "/C1 [1 0 0 0]" && bytesContain updf "/Ink.Probe#20Ink cs 1 scn")
  let (_, apdf, _) := artifacts oneFace (probe
    ("\\definespotcolor{viargb}{Rgb Ink}[rgb]{1,.5,0}\n\\definespotcolor{viagray}{Gray Ink}[gray]{.4}\n" ++
      "\\definespotcolor{vianame}{Ink \u00cbcru}{0,.1,.2,0}\n")
    "\\textcolor{viargb}{A} \\textcolor{viagray}{B} \\textcolor{vianame}{C}")
  t "an alternate in rgb or gray converts to CMYK as xcolor's cmyk:<model> does"
    (bytesContain apdf "/Separation /Rgb#20Ink /DeviceCMYK << /FunctionType 2 /Domain [0 1] /C0 [0 0 0 0] /C1 [0 0.5 1 0]" &&
      bytesContain apdf "/Separation /Gray#20Ink /DeviceCMYK << /FunctionType 2 /Domain [0 1] /C0 [0 0 0 0] /C1 [0 0 0 0.6]")
  t "a colorant outside ASCII is named by its UTF-8 bytes, in its space and its resource key"
    (bytesContain apdf "/Ink.Ink#20#C3#8Bcru [/Separation /Ink#20#C3#8Bcru " &&
      bytesContain apdf "/Ink.Ink#20#C3#8Bcru cs 1 scn")
  let (nds, npdf, nhtml) := artifacts oneFace
    ("\\documentclass{article}\n\\palette{ ink = spot(\"Probe Ink\", cmyk(0, 0.5, 1, 0)) }\n" ++
      "\\begin{document}\n\\textcolor{ink!50}{Alpha}\n\\end{document}")
  t "the native spot spelling declares the same ink"
    (nds.all (·.severity != .error) && bytesContain npdf "/C1 [0 0.5 1 0]" &&
      bytesContain npdf "/Ink.Probe#20Ink cs 0.5 scn" && hasStr nhtml "#ffbf80")
  let (_, labDs) := elabStr (probe "\\definespotcolor{lab}{Lab Ink}[alt=lab]{50,20,30}\n" "x")
  t "a Lab alternate is refused by name" (codes labDs .W0102 == 1)
  t "the boundary standalone declares each ink once, and a full tint by the ink's own name"
    (Ir.colorDeclLine ("full", Ir.Color.ofInk probeInk 1) ==
        "\\colorlet{full}{ink@50726f626520496e6b}\n" &&
      Ir.colorDeclLine ("half", Ir.Color.ofInk probeInk (1 / 2)) ==
        "\\colorlet{half}{ink@50726f626520496e6b!50}\n" &&
      Ir.inkDeclLines #[("full", Ir.Color.ofInk probeInk 1), ("half", Ir.Color.ofInk probeInk (1 / 2))] ==
        "\\usepackage{colorspace}\n\\definespotcolor{ink@50726f626520496e6b}{Probe Ink}{0,0.5,1,0}\n")

  let sepPdf := syntheticPdf #[
    "<< /Type /Catalog /Pages 2 0 R >>",
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 20 20] /Contents 4 0 R /Resources << " ++
      "/ColorSpace << /CS0 [/Separation /Probe#20Ink /DeviceCMYK << /FunctionType 2 " ++
      "/Domain [0 1] /C0 [0 0 0 0] /C1 [0 0.5 1 0] /N 1 >>] >> >> >>",
    streamObj "/CS0 cs 0.5 scn 0 0 10 10 re f"]
  let sepFill : Option Ir.Color := match PdfGfx.importPage sepPdf with
    | .ok imp => imp.figure.marks.findSome? fun (mk : Gfx.Mark) => match mk with
      | .paint _ _ (some f) _ _ _ => match f.paint with
        | .solid c => some c
        | .gradient _ => none
      | _ => none
    | .error _ => none
  t "a PDF figure's ink is read back as the ink, its preview the alternate's at the tint"
    (sepFill.any fun c => (c.ink?.map (·.1.name)) == some "Probe Ink" && c.r == 255 && c.g == 191 && c.b == 128)

end Tests.SpotColor
