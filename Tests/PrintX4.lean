module

public import Tests.Support
public import Tests.DriverAssets
public import LeanTex.Core.PdfX
import LeanTex.Core.PdfDate

public section

open LeanTex.Core

namespace Tests.PrintX4

private def be32 (n : Nat) : List UInt8 :=
  [n / 16777216 % 256, n / 65536 % 256, n / 256 % 256, n % 256].map UInt8.ofNat

private def ascii (s : String) : List UInt8 := s.toList.map fun c => UInt8.ofNat c.toNat

/-- A minimal ICC profile: its header's version, class and colour space, and one `desc` tag. -/
def profile (major minor : Nat) (cls space name : String) : ByteArray :=
  let text := ascii name ++ [0]
  let tag := ascii "desc" ++ [0, 0, 0, 0] ++ be32 text.length ++ text ++
    List.replicate (4 + 4 + 2 + 1 + 67) 0
  let tag := tag ++ List.replicate ((4 - tag.length % 4) % 4) 0
  let table := [be32 1, ascii "desc", be32 144, be32 tag.length].flatten
  let size := 128 + table.length + tag.length
  let header := [be32 size, ascii "none", [UInt8.ofNat major, UInt8.ofNat (minor * 16), 0, 0],
    ascii cls, ascii space, ascii "Lab ", List.replicate 12 0, ascii "acsp", List.replicate 28 0,
    be32 0xF6D6, be32 0x10000, be32 0xD32D, List.replicate 48 0].flatten
  ⟨(header ++ table ++ tag).toArray⟩

/-- An invented print card declaring PDF/X-4 with an output profile, `extra` in its preamble and
`body` on its page. -/
private def card (extra body : String) (dated : Bool := true) : String :=
  "\\DocumentMetadata{lang=en, pdfversion=1.6, pdfstandard=X-4, colorprofiles={X=probe.icc}}\n" ++
  "\\documentclass{article}\n\\usepackage{xcolor}\n\\usepackage{hyperref}\n" ++
  "\\page{ bleed = 9bp }\n\\pagecolor{white}\n\\pagestyle{empty}\n\\definecolor{body}{cmyk}{.5,.4,.3,.9}\n" ++
  "\\ExplSyntaxOn\n\\prop_const_from_keyval:cn { c__pdfmeta_colorprofile_probe.icc }\n" ++
  "  { ,OutputConditionIdentifier = Probe~Press~1 ,Info = {Probe~press,~coated~stock}\n" ++
  "    ,RegistryName = http://www.example.org ,N = 4 }\n\\ExplSyntaxOff\n" ++
  (if dated then "\\hypersetup{pdftitle={Probe card}, pdfcreationdate={D:20261014120000Z}}\n"
   else "\\hypersetup{pdftitle={Probe card}}\n") ++
  extra ++ "\\begin{document}\n\\color{body}" ++ body ++ "\n\\end{document}"

/-- A source's PDF as the driver writes it under its claim, beside the figures `figures` names: the
elaboration's diagnostics, the claim's, and the written bytes, a write error a failing claim. -/
private def written (oneFace : Font.FontSet) (src : String) (icc : Option ByteArray)
    (figures : Array (String × ByteArray) := #[]) : Array Diag × Array Diag × ByteArray :=
  let (doc, ds) := elabStr src
  let geom := Layout.Geom.ofPage doc.page
  let imgs : Image.Store := { profile := icc
                              entries := figures.map fun (src, b) => { src, info := (Image.decode b).toOption } }
  let out := layoutOf oneFace doc geom (imgs := imgs)
  let first := Pdf.write geom oneFace out.pages doc.info imgs
  match Tests.DriverAssets.pdfxClaim doc.info first (Pdf.linkCount geom out.pages) fun info =>
      Pdf.writeChecked geom oneFace out.pages info imgs with
  | .ok (pdf, claim) => (ds, claim, pdf)
  | .error _ => (ds, #[Diag.of .W0445 "the probe's file could not be written"], ByteArray.empty)

/-- Whether a claim stands: no requirement the file breaks is named. -/
private def claimed (claim : Array Diag) : Bool := !claim.any (·.code == DiagCode.W0445.code)

/-- A one-page figure of the given resources and content, its other objects after it. -/
private def figure (resources content : String) (more : Array ByteArray := #[]) : ByteArray :=
  syntheticPdfBin (#["<< /Type /Catalog /Pages 2 0 R >>", "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
    s!"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 20 20] /Resources {resources} /Contents 4 0 R >>",
    streamObj content].map String.toUTF8 ++ more)

/-- A file meeting PDF/X-4 as the judge reads it, built by hand: its intent embedding `icc`. -/
public def passingPdf (icc : ByteArray) : ByteArray :=
  let xmp := "<?xpacket begin=\"\" id=\"W5M0MpCehiHzreSzNTczkc9d\"?><x:xmpmeta xmlns:x=\"adobe:ns:meta/\">" ++
    "<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"><rdf:Description rdf:about=\"\">" ++
    "<dc:title><rdf:Alt><rdf:li xml:lang=\"x-default\">Probe</rdf:li></rdf:Alt></dc:title>" ++
    "<pdfxid:GTS_PDFXVersion>PDF/X-4</pdfxid:GTS_PDFXVersion><xmpMM:DocumentID>xmp.did:1</xmpMM:DocumentID>" ++
    "<xmpMM:VersionID>1</xmpMM:VersionID><xmpMM:RenditionClass>default</xmpMM:RenditionClass>" ++
    "<xmp:CreateDate>2026-10-14</xmp:CreateDate><xmp:ModifyDate>2026-10-14</xmp:ModifyDate>" ++
    "<pdf:Trapped>False</pdf:Trapped></rdf:Description></rdf:RDF></x:xmpmeta><?xpacket end=\"w\"?>"
  let pdf := syntheticPdfBin #[
    ("<< /Type /Catalog /Pages 2 0 R /Metadata 5 0 R /OutputIntents [<< /Type /OutputIntent " ++
      "/S /GTS_PDFX /OutputConditionIdentifier (Probe Press 1) /DestOutputProfile 6 0 R >>] >>").toUTF8,
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>".toUTF8,
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 20 20] /TrimBox [1 1 19 19] /Contents 4 0 R >>".toUTF8,
    (streamObj "0 0 0 1 k 0 0 5 5 re f").toUTF8,
    (streamObj xmp "/Type /Metadata /Subtype /XML ").toUTF8,
    streamObjBin icc "/N 4 ",
    "<< /Trapped /False /CreationDate (D:20261014) /ModDate (D:20261014) >>".toUTF8] "/Info 7 0 R "
  pdf.set! 7 54

private def codes (ds : Array Diag) (c : DiagCode) : Nat := (ds.filter (·.code == c.code)).size

private def rect (x0 y0 x1 y1 : Nat) : Option PdfX.Rect :=
  some ⟨mkRat x0 10, mkRat y0 10, mkRat x1 10, mkRat y1 10⟩

/-- Facts of a file that meets every requirement the judge reads. -/
private def passing : PdfX.Facts :=
  { version := "1.6"
    intents := #[{ subtype := some "GTS_PDFX", condition := some "Probe Press 1"
                   profile := some { version := (2, 1), deviceClass := "prtr", colorSpace := "CMYK" }
                   declaredN := some 4, embedded := true }]
    xmpVersion := some "PDF/X-4", xmpTrapped := some "False", xmpCreated := some "2026-10-14"
    xmpModified := some "2026-10-14", xmpTitle := true, xmpDocumentId := some "xmp.did:0"
    xmpVersionId := some "1", xmpRendition := some "default", infoTrapped := some "False"
    infoCreated := some "D:20261014", infoModified := some "D:20261014"
    pages := #[{ media := rect 0 0 2592 1440, bleed := rect 0 0 2592 1440, trim := rect 90 90 2502 1350 }]
    devices := #["DeviceCMYK", "DeviceGray"] }

private def broken (f : PdfX.Facts) (rule : String) : Bool :=
  (PdfX.breaches f).any (·.rule == rule)

/-- The claim against what an imported figure, the metadata and the declarations can carry. -/
def figureChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let icc := profile 2 1 "prtr" "CMYK" "Probe Press 1"
  let withFigure (fig : ByteArray) : Array Diag × ByteArray :=
    let (_, claim, pdf) := written oneFace (card "\\usepackage{graphicx}\n" "\\includegraphics{fig.pdf}")
      (some icc) #[("fig.pdf", fig)]
    (claim, pdf)
  let font (f : String) := s!"<< /Font << /F1 {f} >> >>"
  for (what, subject, fig) in [
      ("an unembedded font in a direct font dictionary", "pdfx:fonts",
        figure (font "<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>") "BT /F1 9 Tf 1 1 Td (x) Tj ET"),
      ("a composite font whose direct descendant is unembedded", "pdfx:fonts",
        figure (font ("<< /Type /Font /Subtype /Type0 /BaseFont /Probe /Encoding /Identity-H " ++
          "/DescendantFonts [<< /Type /Font /Subtype /CIDFontType0 /BaseFont /Probe " ++
          "/CIDSystemInfo << /Registry (Adobe) /Ordering (Identity) /Supplement 0 >> " ++
          "/FontDescriptor << /Type /FontDescriptor /FontName /Probe /Flags 4 /FontBBox [0 0 1 1] " ++
          "/ItalicAngle 0 /Ascent 1 /Descent 0 /CapHeight 1 /StemV 1 >> >>] >>"))
          "BT /F1 9 Tf 1 1 Td <0001> Tj ET"),
      ("DeviceRGB in a Type 3 glyph", "pdfx:colour",
        figure (font ("<< /Type /Font /Subtype /Type3 /FontBBox [0 0 1 1] /FontMatrix [1 0 0 1 0 0] " ++
          "/CharProcs << /a 5 0 R >> /Encoding << /Type /Encoding /Differences [97 /a] >> " ++
          "/FirstChar 97 /LastChar 97 /Widths [1] >>")) "BT /F1 9 Tf 1 1 Td (a) Tj ET"
          #[(streamObj "1 0 d0 1 0 0 rg 0 0 1 1 re f").toUTF8]),
      ("DeviceRGB in a tiling pattern's cell", "pdfx:colour",
        figure "<< /Pattern << /P1 5 0 R >> >>" "/Pattern cs /P1 scn 0 0 5 5 re f"
          #[(streamObj "1 0 0 rg 0 0 1 1 re f"
            "/PatternType 1 /PaintType 1 /TilingType 1 /BBox [0 0 1 1] /XStep 1 /YStep 1 /Resources << >> ").toUTF8]),
      ("an ICC 4.4 profile in a colour space", "pdfx:colour",
        figure "<< /ColorSpace << /C0 [/ICCBased 5 0 R] >> >>" "/C0 cs 0 0 0 1 sc 0 0 5 5 re f"
          #[streamObjBin (profile 4 4 "prtr" "CMYK" "Probe Ink") "/N 4 "]),
      ("a transfer function", "pdfx:constructs",
        figure "<< /ExtGState << /G1 << /TR 5 0 R >> >> >>" "/G1 gs 0 0 0 1 k 0 0 5 5 re f"
          #["<< /FunctionType 2 /Domain [0 1] /C0 [0] /C1 [1] /N 1 >>".toUTF8]),
      ("a halftone named for a device", "pdfx:constructs",
        figure ("<< /ExtGState << /G1 << /HT << /Type /Halftone /HalftoneType 1 " ++
          "/HalftoneName (ProbeScreen) /Frequency 60 /Angle 45 /SpotFunction /Round >> >> >> >>")
          "/G1 gs 0 0 0 1 k 0 0 5 5 re f"),
      ("a PostScript XObject", "pdfx:constructs",
        figure "<< /XObject << /X1 5 0 R >> >>" "/X1 Do"
          #[(streamObj "%!" "/Type /XObject /Subtype /PS ").toUTF8]),
      ("a form carrying PostScript", "pdfx:constructs",
        figure "<< /XObject << /X1 5 0 R >> >>" "/X1 Do"
          #[(streamObj "0 0 0 1 k 0 0 1 1 re f" ("/Type /XObject /Subtype /Form /BBox [0 0 1 1] " ++
            "/Subtype2 /PS /PS 6 0 R ")).toUTF8, (streamObj "%!").toUTF8]),
      ("a reference to another file's page", "pdfx:constructs",
        figure "<< /XObject << /X1 5 0 R >> >>" "/X1 Do"
          #[(streamObj "0 0 0 1 k 0 0 1 1 re f" ("/Type /XObject /Subtype /Form /BBox [0 0 1 1] " ++
            "/Ref << /F (other.pdf) /Page 0 >> ")).toUTF8]),
      ("an indexed space over a separation with an RGB alternate", "pdfx:colour",
        figure ("<< /ColorSpace << /C0 [/Indexed [/Separation /ProbeSpot /DeviceRGB " ++
          "<< /FunctionType 2 /Domain [0 1] /C0 [1 1 1] /C1 [1 0 0] /N 1 >>] 1 <00ff>] >> >>")
          "/C0 cs 1 sc 0 0 5 5 re f"),
      ("a DeviceN whose colorant is a separation over RGB", "pdfx:colour",
        figure ("<< /ColorSpace << /C0 [/DeviceN [/ProbeSpot] /DeviceCMYK " ++
          "<< /FunctionType 2 /Domain [0 1] /C0 [0 0 0 0] /C1 [0 0 0 1] /N 1 >> << /Colorants << " ++
          "/ProbeSpot [/Separation /ProbeSpot /DeviceRGB << /FunctionType 2 /Domain [0 1] " ++
          "/C0 [1 1 1] /C1 [1 0 0] /N 1 >>] >> >>] >> >>") "/C0 cs 1 sc 0 0 5 5 re f")] do
    let (claim, pdf) := withFigure fig
    t s!"a figure holding {what} withholds the claim, named"
      (!claimed claim && claim.any (·.subject == some subject) && !bytesContain (pdfText pdf) "pdfxid:")
  let (unknown, uClaim, uPdf) := written oneFace
    (card "\\hypersetup{pdftrapped=Unknown}\n" "Alpha") (some icc)
  t "a declared unknown trapping is named under PDF/X-4 and the file states False, as it is untrapped"
    (codes unknown .W0447 == 0 && codes uClaim .W0447 == 1 &&
      uClaim.any (·.subject == some "pdfx:trapped") && claimed uClaim &&
      bytesContain (pdfText uPdf) "/Trapped /False")
  let native := "\\documentclass{article}\n\\pdfmeta{ trapped = unknown, standard = \"X-4\", " ++
    "intent = \"probe.icc\", title = \"Probe\", created = \"2026-10-14\" }\n\\page{ bleed = 9bp }\n" ++
    "\\pagestyle{empty}\n\\definecolor{body}{cmyk}{.5,.4,.3,.9}\n\\begin{document}\n\\color{body}Alpha\n\\end{document}"
  let (_, oClaim, _) := written oneFace native (some icc)
  let (_, eClaim, _) := written oneFace
    (card "\\pdfmeta{ trapped = unknown }\n\\hypersetup{pdftrapped=False}\n" "Alpha") (some icc)
  t "an unknown trapping is named wherever it stands, and a later declaration replaces it"
    (codes oClaim .W0447 == 1 && claimed oClaim && codes eClaim .W0447 == 0)
  let (strings, stringDs) := elabStr ("\\documentclass{article}\n" ++
    "\\pdfmeta{ trapped = \"true\", intent-components = \"4\" }\n\\begin{document}\nx\n\\end{document}")
  let (_, wrongDs) := elabStr ("\\documentclass{article}\n\\pdfmeta{ trapped = 5 }\n" ++
    "\\begin{document}\nx\n\\end{document}")
  t "quoted trapping and channel counts read as written, and a wrong type names the values it takes"
    (strings.info.trapped == some true && (strings.info.intent.bind (·.components)) == some 4 &&
      codes stringDs .E0323 == 0 &&
      wrongDs.any fun d => d.code == DiagCode.E0323.code && hasStr (saidText d) "true, false or unknown")
  let (_, febDs) := elabStr ("\\documentclass{article}\n\\pdfmeta{ created = \"2026-02-31\" }\n" ++
    "\\begin{document}\nx\n\\end{document}")
  t "a date the calendar does not have is refused" (codes febDs .E0323 == 1)
  let builtin (pre : String) : Option Ir.OutputIntent := (elabStr ("\\DocumentMetadata{pdfstandard=X-4, " ++
    "colorprofiles={X=FOGRA39L_coated.icc}}\n\\documentclass{article}\n" ++ pre ++
    "\\begin{document}\nx\n\\end{document}")).1.info.intent
  t "a profile of the colorprofiles package a document does not describe takes l3pdfmeta's description"
    ((builtin "").any fun oi => oi.condition == some "FOGRA39L Coated" &&
      oi.registry == some "http://www.fogra.org" && oi.components == some 4 &&
      oi.info.any (·.startsWith "Offset printing, according to ISO 12647-2:2004/Amd 1, OFCOM,"))
  t "a document's own description of such a profile stands over l3pdfmeta's"
    ((builtin "\\pdfmeta{ intent-condition = \"Probe Press 2\" }\n").any fun oi =>
      oi.condition == some "Probe Press 2" && oi.registry == some "http://www.fogra.org")
  let (_, nbClaim, nbPdf) := written oneFace
    ((card "" "Alpha").replace "\\page{ bleed = 9bp }\n" "") (some icc)
  t "a claimed page with no declared trim is trimmed at its media box"
    (claimed nbClaim && bytesContain (pdfText nbPdf) "/TrimBox [0 0 612 792]")
  let (_, cbClaim, cbPdf) := written oneFace
    ((card "\\page{ cropbox = \"20 20 592 772\" }\n" "Alpha").replace "\\page{ bleed = 9bp }\n" "") (some icc)
  t "a claimed page with a declared crop and no trim is trimmed at its crop box"
    (claimed cbClaim && bytesContain (pdfText cbPdf) "/TrimBox [20 20 592 772]")
  let geom : Layout.Geom := {}
  let claimedFeatures := Pdf.features geom oneFace #[] (info := { pdfx := some "X-4" })
  t "the feature census of a claimed file names its trim box and no outbound link"
    (claimedFeatures.contains .trimBox && !claimedFeatures.contains .linkURI)
  let (_, _, aPdf) := written oneFace (card "" "Alpha") (some icc)
  let (_, _, bPdf) := written oneFace (card "" "Beta") (some icc)
  let idOf (tag : String) (b : ByteArray) : String :=
    ((String.ofList (b.toList.map fun c => Char.ofNat c.toNat)).splitOn tag)[1]?.getD ""
      |>.take 32 |>.toString
  t "two documents of one title and creation share their document identifier, and other pages give another instance"
    (!(idOf "xmp.did:" aPdf).isEmpty && idOf "xmp.did:" aPdf == idOf "xmp.did:" bPdf &&
      idOf "xmp.iid:" aPdf != idOf "xmp.iid:" bPdf)
  t "a Custom condition with no description breaks the output intent rule"
    (broken { passing with intents := passing.intents.map fun i => { i with condition := some "Custom" } }
      "output-intent")
  let claimedHere := Tests.DriverAssets.pdfxClaim { pdfx := some "X-4" } (passingPdf icc) 2 fun _ => .ok .empty
  t "a hand-built file meeting the rules keeps its claim, naming its two links unwritten and what a preflight judges"
    (match claimedHere with
      | .ok (_, ds) => codes ds .W0444 == 1 && codes ds .N0448 == 1 && claimed ds
      | .error _ => false)

/-- A file declaring PDF/X-4 claims it only where its own bytes meet ISO 15930-7 as the judge reads
it; else it is written without the claim, each breach named. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  figureChecks ref oneFace
  let icc := profile 2 1 "prtr" "CMYK" "Probe Press 1"
  let (ds, claim, pdf) := written oneFace (card "" "Alpha") (some icc)
  let text := pdfText pdf
  t "the probe card elaborates with nothing dropped or skipped"
    (codes ds .W0101 == 0 && codes ds .W0106 == 0 && codes ds .W0447 == 0 &&
      ds.all (·.severity != .error))
  t "the card meets PDF/X-4 and claims it, naming what only a press's preflight judges"
    (claimed claim && codes claim .N0448 == 1 && codes claim .W0444 == 0)
  t "its header is PDF 1.6, the version PDF/X-4 is defined on"
    (pdf.extract 0 8 == "%PDF-1.6".toUTF8)
  t "one GTS_PDFX output intent embeds the profile and names its condition from the pdfmeta property"
    (bytesContain text ("/OutputIntents [<< /Type /OutputIntent /S /GTS_PDFX /DestOutputProfile ") &&
      bytesContain text ("/OutputConditionIdentifier (Probe Press 1) /Info (Probe press, coated stock) " ++
        "/RegistryName (http://www.example.org)") &&
      bytesContain pdf "/N 4" &&
      ((PdfRead.objects pdf).toOption.any fun es => es.val.any fun e => e.decoded == .ok (some icc)))
  t "the metadata identifies PDF/X-4, the document and its rendition, and states trapping and dates as the Info dictionary does"
    (bytesContain text "<pdfxid:GTS_PDFXVersion>PDF/X-4</pdfxid:GTS_PDFXVersion>" &&
      bytesContain text "<pdf:Trapped>False</pdf:Trapped>" &&
      bytesContain text "<xmp:CreateDate>2026-10-14T12:00:00Z</xmp:CreateDate>" &&
      bytesContain text "/CreationDate (D:20261014120000Z)" && bytesContain text "/Trapped /False" &&
      bytesContain text "<xmpMM:DocumentID>xmp.did:" &&
      bytesContain text "<xmpMM:VersionID>1</xmpMM:VersionID>" &&
      bytesContain text "<xmpMM:RenditionClass>default</xmpMM:RenditionClass>")
  t "the claimed file's metadata packet stands unfiltered, so a scan of the file's bytes finds it"
    (bytesContain pdf "<pdfxid:GTS_PDFXVersion>PDF/X-4</pdfxid:GTS_PDFXVersion>")
  t "every page carries a trim box and no art box beside it"
    (bytesContain text "/TrimBox [9 9" && !bytesContain text "/ArtBox")
  t "the page ground is white in DeviceGray, as xcolor declares white"
    (bytesContain text "q 1 g 0 0 " && !bytesContain text "1 1 1 rg")
  t "the engine's own reader finds no breach in the claimed file"
    ((PdfX.read pdf).toOption.any fun f => (PdfX.breaches f).isEmpty)
  let other := (card "" "Alpha").replace "c__pdfmeta_colorprofile_probe.icc" "c__pdfmeta_colorprofile_other.icc"
  let (otherDs, _, otherPdf) := written oneFace other (some icc)
  t "a profile description naming another file than the declared profile sets no field of the intent"
    (bytesContain (pdfText otherPdf) "/OutputConditionIdentifier (Custom)" &&
      !bytesContain (pdfText otherPdf) "/RegistryName" &&
      otherDs.any (·.subject == some "ctrl:nothing:explprofile"))
  let (_, rgbClaim, rgbPdf) := written oneFace (card "" "Alpha \\textcolor[rgb]{1,0,0}{Red}") (some icc)
  t "DeviceRGB under a CMYK intent withholds the claim, named once"
    (codes rgbClaim .W0445 == 1 && rgbClaim.any (·.subject == some "pdfx:colour") &&
      !bytesContain (pdfText rgbPdf) "pdfxid:GTS_PDFXVersion" &&
      bytesContain (pdfText rgbPdf) "/OutputIntents")
  let (_, undated, undatedPdf) := written oneFace (card "" "Alpha" (dated := false)) (some icc)
  t "a file with no declared dates is not claimed: PDF/X-4 asks them, and none is stamped"
    (undated.any (·.subject == some "pdfx:metadata") &&
      !bytesContain (pdfText undatedPdf) "xmp:CreateDate" &&
      !bytesContain (pdfText undatedPdf) "pdfxid:")
  let (_, noIntent, _) := written oneFace (card "" "Alpha") none
  t "a file without its profile carries no output intent and is not claimed"
    (noIntent.any (·.subject == some "pdfx:output-intent"))
  let (_, linked, linkedPdf) := written oneFace (card "" "Alpha \\href{https://example.org}{link}") (some icc)
  let (_, folio, folioPdf) := written oneFace (card "\\pagestyle{plain}\n" "Alpha") (some icc)
  t "a page number after a coloured run is black ink in DeviceGray, so a numbered page keeps the claim"
    (claimed folio && bytesContain (pdfText folioPdf) "/Type /Pagination >> BDC\n" &&
      !bytesContain (pdfText folioPdf) "0 0 0 rg")
  let linkedHtml := (HtmlDoc.emit {} (elabStr (card "" "Alpha \\href{https://example.org}{link}")).1).1
  t "a claimed file carries no link, PDF/X admitting none on the printed sheet; the loss is named and the web page keeps it"
    (claimed linked && codes linked .W0444 == 1 && !bytesContain (pdfText linkedPdf) "/Subtype /Link" &&
      hasStr linkedHtml "https://example.org")
  -- The judge, rule by rule, over facts a file could carry.
  t "the passing facts break nothing" (PdfX.breaches passing).isEmpty
  t "a page with both a trim box and an art box breaks PDF/X-4's one-or-the-other rule"
    (broken { passing with pages := passing.pages.map fun p => { p with art := p.trim } } "boxes")
  t "a bleed box past the media box by rounding breaks nesting"
    (broken { passing with pages := passing.pages.map fun p =>
      { p with bleed := some ⟨0, 0, mkRat 25920041 100000, mkRat 14399997 100000⟩ } } "boxes")
  t "an ICC 4.2 profile is admitted in a PDF 1.6 file, 2.1 too, a 4.4 refused"
    (!broken { passing with intents := passing.intents.map fun i =>
        { i with profile := i.profile.map fun h => { h with version := (4, 2) } } } "output-intent" &&
      broken { passing with intents := passing.intents.map fun i =>
        { i with profile := i.profile.map fun h => { h with version := (4, 4) } } } "output-intent")
  t "trapping stated in the Info dictionary alone, or differently in each, is a breach"
    (broken { passing with xmpTrapped := none } "trapped" &&
      broken { passing with xmpTrapped := some "True" } "trapped" &&
      broken { passing with infoTrapped := some "Unknown", xmpTrapped := some "Unknown" } "trapped")
  t "PDF 1.6 is the version PDF/X-4 admits, 1.7 and 2.0 are not"
    (!broken passing "version" && broken { passing with version := "1.7" } "version" &&
      broken { passing with version := "2.0" } "version")
  t "a printable link over the page breaks the annotation rule"
    (broken { passing with annots := #[(0, "Link", ⟨10, 10, 20, 20⟩)] } "annotations")
  t "metadata without a version or rendition identifier breaks PDF/X-4's identification"
    (broken { passing with xmpVersionId := none } "metadata" &&
      broken { passing with xmpRendition := some "" } "metadata")
  t "dates that disagree between the Info dictionary and the metadata are a breach"
    (broken { passing with infoCreated := some "D:20261015" } "metadata")
  -- The profile the driver reads.
  t "an output profile in CMYK is admitted; a display profile or a channel count it does not have is not"
    (PdfX.profileFault icc none == none && PdfX.profileFault icc (some 4) == none &&
      (PdfX.profileFault (profile 2 1 "mntr" "RGB " "Probe Screen") none).isSome &&
      (PdfX.profileFault icc (some 3)).isSome && (PdfX.profileFault "not icc".toUTF8 none).isSome)
  IO.FS.withTempDir fun dir => do
    let file := (dir / "doc.tex").toString
    let missing ← Tests.DriverAssets.loadProfile file { intent := some { profile := "absent.icc" } }
    IO.FS.writeBinFile (dir / "probe.icc") icc
    let found ← Tests.DriverAssets.loadProfile file { intent := some { profile := "probe.icc" } }
    t "the driver names a profile that is not there, and reads one that is"
      (missing.1.isNone && codes missing.2 .W0446 == 1 && found.1 == some icc && found.2.isEmpty)
    let losses := Tests.DriverAssets.claimLosses missing.2 (noIntent ++ undated)
    t "a refused profile names the missing intent once, the claim's other losses still named"
      (losses.all (·.subject != some "pdfx:output-intent") &&
        losses.any (·.subject == some "pdfx:metadata") &&
        (Tests.DriverAssets.claimLosses #[] noIntent).size == noIntent.size)
  -- xcolor's base colours in the models it declares them in.
  let (_, _, bpdf) := written oneFace (card "" ("Alpha \\textcolor{black}{A}\\textcolor{cyan}{B}" ++
    "\\textcolor{olive}{C}\\textcolor{black!50}{D}\\textcolor{gray}{E}\\textcolor{red}{F}")) (some icc)
  let btext := pdfText bpdf
  t "black, gray and their mixes are DeviceGray, cyan and olive DeviceCMYK, red DeviceRGB"
    (["0 g\n", "0.5 g\n", "1 0 0 0 k\n", "0 0 1 0.5 k\n", "1 0 0 rg\n"].all (bytesContain btext ·))
  let (linkDoc, _) := elabStr ("\\documentclass{article}\n\\usepackage[colorlinks]{hyperref}\n" ++
    "\\begin{document}\nSee \\url{https://example.org}.\n\\end{document}")
  t "a document's magenta link keeps its web schemes, as before the grays were declared in gray"
    ((HtmlDoc.emit {} linkDoc).2.all (·.code != DiagCode.W0308.code))
  let (odd, oddDs) := elabStr ("\\documentclass{article}\n\\usepackage{hyperref}\n" ++
    "\\hypersetup{pdftrapped=Unknown, pdfcreationdate={yesterday}}\n\\begin{document}\nx\n\\end{document}")
  t "a hyperref date the engine cannot read is named and dropped, an unknown trapping read, never an error"
    (odd.info.trapped.isNone && odd.info.trappedUnknownAt.isSome && odd.info.created.isNone &&
      codes oddDs .W0101 == 1 && oddDs.all (·.severity != .error))
  let worded := "\\documentclass{article}\n\\usepackage{hyperref}\n\\hypersetup{pdftitle={O'Brien's card}, " ++
    "pdfcreationdate={D:20260131090000+01'00'}, pdfmoddate={2026-02-01}, pdftrapped=FALSE}\n" ++
    "\\begin{document}\nx\n\\end{document}"
  let (wordDoc, wordDs) := elabStr worded
  let (_, _, wordPdf) := written oneFace worded none
  let notes := wordDs.filter fun d => d.code == DiagCode.N0100.code && d.message.startsWith "'\\hypersetup'"
  t "hyperref's dates and trapping reach the file as written, an offset's apostrophes kept, beside a title set as text"
    (wordDoc.info.created == some "D:20260131090000+01'00'" && wordDoc.info.modified == some "2026-02-01" &&
      wordDoc.info.trapped == some false && wordDoc.info.title == some "O’Brien’s card" &&
      bytesContain (pdfText wordPdf) "/CreationDate (D:20260131090000+01'00')" &&
      bytesContain (pdfText wordPdf) "<xmp:CreateDate>2026-01-31T09:00:00+01:00</xmp:CreateDate>" &&
      bytesContain (pdfText wordPdf) "/ModDate (D:20260201)" && bytesContain (pdfText wordPdf) "/Trapped /False")
  t "one note names what the setup lowers, its title, dates and trapping in one declaration"
    (notes.size == 1 && notes.all fun d => hasStr (saidText d) ("\\pdfmeta{ title = \"O’Brien’s card\", " ++
      "created = \"D:20260131090000+01'00'\", modified = \"2026-02-01\", trapped = \"false\" }"))
  for setup in ["\\hypersetup{pdftitle={T}, pdftrapped=True}", "\\hypersetup{pdftrapped=True}",
      "\\ExplSyntaxOn\\prop_const_from_keyval:cn{c__pdfmeta_colorprofile_probe.icc}{Info={x}}\\ExplSyntaxOff"] do
    let body := "\\documentclass{article}\n\\usepackage{hyperref}\n\\begin{document}\n" ++
      "Alpha " ++ setup ++ "{Kept one} two\n\\end{document}"
    let (_, bodyDs) := elabStr body
    let atSetup := bodyDs.filter fun d => d.span.any (·.pos.line == 4)
    t s!"a declaration in the body is named once and leaves its paragraph and the next group as written ({setup})"
      (atSetup.size == 1 && atSetup.all (fun d => (d.code == DiagCode.W0340.code ||
        d.code == DiagCode.W0106.code) && d.sites == 1) && hasStr (pageTextOf oneFace body) "Alpha Kept one two")
  let (blank, blankDs) := elabStr ("\\documentclass{article}\n\\usepackage{hyperref}\n" ++
    "\\hypersetup{pdfcreationdate={}, pdftrapped=}\n\\begin{document}\nx\n\\end{document}")
  t "an empty hyperref date or trapping alone declares nothing, as hyperref writes none"
    (blank.info.created.isNone && blank.info.trapped.isNone && codes blankDs .W0101 == 0)
  let (_, bothDs) := elabStr ("\\documentclass{article}\n\\usepackage{hyperref}\n" ++
    "\\hypersetup{pdfmoddate={soon}, linkcolor={blue, font = x}}\n\\begin{document}\nx\n\\end{document}")
  t "an unread date and an unread link colour are each named under their own code"
    (codes bothDs .W0101 == 1 && codes bothDs .W0102 == 1 &&
      bothDs.any fun d => d.code == DiagCode.W0101.code && hasStr (saidText d) "pdfmoddate")
  let (_, misDs) := elabStr ("\\documentclass{article}\n\\usepackage{hyperref}\n" ++
    "\\hypersetup{pdfmoddate=soon, pdfsubject=(a,b)}\n\\hypersetup{pdfcreationdate=bogus}\n" ++
    "\\begin{document}\nx\n\\end{document}")
  let misAt (line : Nat) := misDs.filter fun d => d.span.any (·.pos.line == line)
  t "a setup's dropped entries are named in one warning, and a setup whose every entry dropped has no note"
    (((misAt 3).filter (·.code == DiagCode.W0101.code)).size == 1 &&
      (misAt 3).any (fun d => d.code == DiagCode.W0101.code && hasStr (saidText d) "'pdfmoddate=soon'" &&
        hasStr (saidText d) "'b)'") &&
      (misAt 4).size == 1 && (misAt 4).all (·.code == DiagCode.W0101.code))
  let (hostileDoc, _) := elabStr ("\\DocumentMetadata{pdfstandard=X-4, " ++
    "colorprofiles={X={probe\", title = \"Injected.icc}}}\n\\documentclass{article}\n" ++
    "\\begin{document}\nx\n\\end{document}")
  t "a quote in a declared profile's name sets no other key, and the profile is named whole"
    (hostileDoc.info.title.isNone && hostileDoc.info.pdfx == some "X-4" &&
      (hostileDoc.info.intent.map (·.profile)) == some "probe\", title = \"Injected.icc")
  for (value, read) in [("{x~\",~intent-registry~=~\"Injected}", "x \", intent-registry = \"Injected"),
      ("{Coated}~{Stock}", "{Coated} {Stock}"),
      ("{a}\\pdfmeta{title=~\"Injected\"}{b}", "{a}\\pdfmeta{title= \"Injected\"}{b}")] do
    let src := (card "" "Alpha").replace "Info = {Probe~press,~coated~stock}" s!"Info = {value}"
    let (ds, claim, pdf) := written oneFace src (some icc)
    t s!"a profile description's value is carried exactly and sets no other key ({value})"
      (ds.all (·.severity != .error) && codes ds .W0101 == 0 && codes ds .W0343 == 0 && claimed claim &&
        ((PdfX.read pdf).toOption.bind fun f => f.intents[0]?.bind (·.info)) == some read &&
        bytesContain (pdfText pdf) "/RegistryName (http://www.example.org)")
  let special := (card "" "Alpha").replace "OutputConditionIdentifier = Probe~Press~1"
    "OutputConditionIdentifier = Probe~(Press)~\\\\1"
  let (_, specialClaim, specialPdf) := written oneFace special (some icc)
  t "an output condition holding a string's delimiters and a backslash reads back exactly"
    (claimed specialClaim && ((PdfX.read specialPdf).toOption.bind fun f =>
      f.intents[0]?.bind (·.condition)) == some "Probe (Press) \\\\1")
  t "an Info date's fields each take their digits: a short one is refused, a missing one defaults"
    (PdfDate.parse? "D:2026013" == none && PdfDate.parse? "D:2026013109000" == none &&
      PdfDate.parse? "D:202601310900Z" == none &&
      (PdfDate.parse? "D:202601").map (·.pdf) == some "D:20260101" &&
      (PdfDate.parse? "D:2026013109").map (·.pdf) == some "D:20260131090000" &&
      (PdfDate.parse? "D:20260131090000+01").map (·.xmp) == some "2026-01-31T09:00:00+01:00" &&
      (PdfDate.parse? "D:20260131090000-05'30").map (·.pdf) == some "D:20260131090000-05'30'" &&
      (PdfDate.parse? "D:20260131090000Z00'00'").map (·.xmp) == some "2026-01-31T09:00:00Z" &&
      PdfDate.parse? "D:20260131090000+01'99'" == none && PdfDate.parse? "2026-01-31T09:00:00+01:99" == none)
  t "the judge reads each date in its own field's spelling, the Info's and the metadata's"
    (broken { passing with xmpCreated := some "D:20261014" } "metadata" &&
      broken { passing with infoCreated := some "2026-10-14" } "metadata")
  let (version20, _) := elabStr ("\\documentclass{article}\n\\pdfmeta{ standard = \"X-4\", version = \"2.0\" }\n" ++
    "\\begin{document}\nx\n\\end{document}")
  let (version17, _) := elabStr ("\\documentclass{article}\n\\pdfmeta{ standard = \"X-4\", version = \"1.7\" }\n" ++
    "\\begin{document}\nx\n\\end{document}")
  t "a declared PDF 2.0 or 1.7 under PDF/X-4 is written as 1.6"
    (version20.info.writtenVersion == some "1.6" && version20.info.pdfx == some "X-4" &&
      version17.info.writtenVersion == some "1.6")
  let ver20 := (card "" "Alpha").replace "pdfversion=1.6" "pdfversion=2.0"
  let (_, vClaim, vPdf) := written oneFace ver20 (some icc)
  let (_, wClaim, wPdf) := written oneFace
    ((card "" "Alpha \\textcolor[rgb]{1,0,0}{Red}").replace "pdfversion=1.6" "pdfversion=2.0") (some icc)
  t "a declared 2.0 is replaced and named only where the claim stands; a withheld claim keeps it"
    (claimed vClaim && codes vClaim .W0447 == 1 && vPdf.extract 0 8 == "%PDF-1.6".toUTF8 &&
      !claimed wClaim && codes wClaim .W0447 == 0 && wPdf.extract 0 8 == "%PDF-2.0".toUTF8 &&
      (vClaim ++ wClaim).all fun d => d.code == DiagCode.N0448.code || d.output == some .pdf)

end Tests.PrintX4
