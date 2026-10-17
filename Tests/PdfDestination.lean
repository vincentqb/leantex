module

public import Tests.Backends
import LeanTex.Core.PdfDests

public section

open LeanTex.Core LeanTex.Core.Dim LeanTex.Cli
open LeanTex.Core.PdfRead (Obj)

/-- Every link annotation's explicit destination resolved through the PDF's page references, in
page order: its page index and destination array; a URI action is no in-document landing. -/
private def linkDestinations (pdf : ByteArray) : Except String (Array (Nat × Array Obj)) := do
  let es ← PdfRead.objects pdf
  let pages := es.val.filter (fun e => PdfCensus.kindOf e.val == .page)
  let mut out := #[]
  for page in pages do
    let annots := PdfCensus.deref es.val ((page.val.get? "Annots").getD .null)
    if let .arr anns := annots then
      for a in anns do
        let a := PdfCensus.deref es.val a
        if PdfCensus.kindOf a != .annot "Link" then continue
        let action := PdfCensus.deref es.val ((a.get? "A").getD .null)
        let dest := (a.get? "Dest").orElse fun _ =>
          if action.get? "S" == some (.name "GoTo") then action.get? "D" else none
        if let some (Obj.arr ds) := dest then
          if let some (Obj.ref n _) := ds[0]? then
            if let some i := pages.findIdx? (·.num == n) then out := out.push (i, ds)
  return out

/-- The first link annotation's landing. -/
private def linkDestination (pdf : ByteArray) : Except String (Option (Nat × Array Obj)) :=
  (linkDestinations pdf).map (·[0]?)

private def pageWith (out : Layout.Out) (text : String) : Option Nat :=
  out.pages.findIdx? fun p => p.lines.any (fun l => hasStr (lineText l) text)

private def lineWith (out : Layout.Out) (text : String) : Option Layout.LineOut :=
  (pageWith out text).bind fun i =>
    out.pages[i]?.bind fun p => p.lines.find? (fun l => hasStr (lineText l) text)

private def pageGeometry (out : Layout.Out) :=
  out.pages.map fun p => p.lines.filterMap fun l =>
    if l.furniture then none else some (l.x, l.y, l.setWidth, lineText l)

/-- Whether a destination array opens at a line's ink: `/XYZ` at its left edge and ink top, the
zoom kept; PDF coordinates round to a millipoint. -/
private def opensAt (fs : Font.FontSet) (geom : Layout.Geom) (ds : Array Obj)
    (line : Layout.LineOut) : Bool :=
  let tolerance := (spPerPt + 999) / 1000
  ds[1]? == some (.name "XYZ") && ds[4]? == some .null &&
    (match ds[2]?.bind Obj.sp?, ds[3]?.bind Obj.sp? with
     | some x, some y =>
       (x - (line.x + geom.bleed)).natAbs ≤ tolerance.toNat &&
         (y - (geom.pageH + geom.bleed - line.y +
           (Layout.segsInk fs line.segs).1)).natAbs ≤ tolerance.toNat
     | _, _ => false)

/-- The in-page fragments a document's HTML links to, one per anchor element, sorted; a note's mark
and back-link are the endnote list's own apparatus, and a pinned navigation a screen's control. -/
private def htmlLinks (doc : Ir.Doc) : Array String :=
  let w : Html.Walk Unit (Array String) :=
    { inner := fun _ tag attrs =>
        if tag == "nav" && hasStr ((HtmlDoc.attrOf? attrs "style").getD "") "position: fixed"
        then none else some ()
      enter := fun _ acc tag attrs _ =>
        if tag != "a" then acc else
        match (HtmlDoc.attrOf? attrs "href").bind Ir.linkFragment?, HtmlDoc.attrOf? attrs "role" with
        | some f, role =>
          if role == some "doc-noteref" || role == some "doc-backlink" then acc else acc.push f
        | none, _ => acc }
  (w.list () #[] (docNodesOf doc).toList).qsort (· < ·)

/-- The in-page links one page carries, each a run of link segments to one target across gaps and
lines, then its block links. -/
private def pageLinks (p : Layout.PageOut) : Array String := Id.run do
  let mut found : Array String := #[]
  let mut current : Option String := none
  for l in p.lines do
    unless l.furniture do
      for seg in l.segs do
        match seg with
        | .run _ _ link _ glyphs .. =>
          if link.isNone && !glyphs.isEmpty then current := none
          else if link.isSome && current != link then
            current := link
            if let some f := link.bind Ir.linkFragment? then found := found.push f
        | _ => pure ()
  return found ++ p.links.filterMap (Ir.linkFragment? ·.target)

/-- The in-page fragments a laid-out document links to, one per link, sorted: a frame's step pages
count each link once, as the most any step shows, a link continued over a page break once, and each
outline entry once. -/
private def pdfLinks (out : Layout.Out) : Array String := Id.run do
  let mut found : Array String := #[]
  let mut group : Option Nat := none
  let mut most : Std.HashMap String Nat := {}
  let mut last : Option String := none
  for p in out.pages do
    let source := p.frameOrigin.map (·.source)
    if source.isNone || source != group then
      found := most.fold (fun acc f n => acc ++ Array.replicate n f) found
      most := {}
    group := source
    let here := pageLinks p
    -- A link continued from the previous page counts with it.
    let here := if source.isNone && here[0]? == last && last.isSome then here.extract 1 else here
    let counts := here.foldl (fun (m : Std.HashMap String Nat) f => m.insert f (m.getD f 0 + 1)) {}
    most := counts.fold (fun m f n => m.insert f (max n (m.getD f 0))) most
    last := (p.lines.reverse.findSome? fun l =>
      if l.furniture then none else l.segs.reverse.findSome? fun seg => match seg with
        | .run _ _ link _ glyphs .. => if glyphs.isEmpty then none else some link
        | _ => none).join.bind Ir.linkFragment?
  found := most.fold (fun acc f n => acc ++ Array.replicate n f) found
  return (found ++ out.outline.filterMap (·.fragment)).qsort (· < ·)

/-- One synthetic file: a catalog with `catalog`'s entries, one page tree holding object 3, a
dictionary that is no page, and a link annotation with `link`'s entries, then `more`. -/
private def navPdf (catalog link : String) (more : Array String := #[]) : ByteArray :=
  syntheticPdf (#[s!"<< /Type /Catalog /Pages 2 0 R {catalog}>>",
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 100 100] /Annots [5 0 R] >>",
    "<< /Kind /Other >>",
    s!"<< /Type /Annot /Subtype /Link /Rect [0 0 10 10] {link}>>"] ++ more)

/-- The judge's verdicts both ways on invented files, each with the reasons it must give. -/
private def judgeCases : List (String × ByteArray × List PdfDests.Why) :=
  [("an explicit destination onto a page", navPdf "" "/Dest [3 0 R /XYZ 0 100 null]", []),
   ("a go-to action's explicit destination", navPdf "" "/A << /S /GoTo /D [3 0 R /Fit] >>", []),
   ("a URI action", navPdf "" "/A << /S /URI /URI (https://example.org/) >>", []),
   ("a string the name tree defines",
    navPdf "/Names << /Dests << /Names [(here) [3 0 R /FitH 50]] >> >>"
      "/A << /S /GoTo /D (here) >>", []),
   ("a string a kid of the name tree defines, as a dictionary's /D",
    navPdf "/Names << /Dests 6 0 R >>" "/A << /S /GoTo /D <68657265> >>"
      #["<< /Kids [7 0 R] >>", "<< /Limits [(a) (z)] /Names [(here) << /D [3 0 R /Fit] >>] >>"],
    []),
   ("a name the catalog's /Dests defines", navPdf "/Dests << /here [3 0 R /Fit] >>" "/Dest /here",
    []),
   ("a string no table defines", navPdf "" "/A << /S /GoTo /D (ref-missing) >>", [.undefined]),
   ("a name the catalog's /Dests lacks, though the name tree holds its string",
    navPdf "/Names << /Dests << /Names [(here) [3 0 R /Fit]] >> >>" "/Dest /here", [.undefined]),
   ("an explicit destination onto no page", navPdf "" "/Dest [4 0 R /Fit]", [.notPage]),
   ("a fit type Table 149 does not name", navPdf "" "/Dest [3 0 R /Zoom 2]", [.badFit]),
   ("a fit's operands miscounted", navPdf "" "/Dest [3 0 R /XYZ 0 100]", [.badFit]),
   ("a null where /FitR wants a number", navPdf "" "/Dest [3 0 R /FitR 0 0 null 10]", [.badFit]),
   ("a destination in another file",
    navPdf "" "/A << /S /GoToR /F (other.pdf) /D [0 /Fit] >>", [.remote]),
   ("a link naming nothing", navPdf "" "", [.nowhere]),
   ("a link with both a destination and an action",
    navPdf "" "/Dest [3 0 R /Fit] /A << /S /URI /URI (https://example.org/) >>", [.malformed]),
   ("an outline item naming nothing",
    navPdf "/Outlines 6 0 R" "/Dest [3 0 R /Fit]"
      #["<< /Type /Outlines /First 7 0 R /Last 7 0 R /Count 1 >>", "<< /Title (Item) /Parent 6 0 R >>"],
    [.nowhere]),
   ("an outline item onto a page",
    navPdf "/Outlines 6 0 R" "/Dest [3 0 R /Fit]"
      #["<< /Type /Outlines /First 7 0 R /Last 7 0 R /Count 1 >>",
        "<< /Title (Item) /Parent 6 0 R /Dest [3 0 R /XYZ null null null] >>"], []),
   ("an open action onto no page", navPdf "/OpenAction [4 0 R /Fit]" "/Dest [3 0 R /Fit]",
    [.notPage]),
   ("a go-to action in an annotation's additional actions",
    navPdf "" "/Dest [3 0 R /Fit] /AA << /E << /S /GoTo /D (gone) >> >>", [.undefined]),
   ("a structure destination naming a structure element",
    navPdf "" "/A << /S /GoTo /D [3 0 R /Fit] /SD [6 0 R /Fit] >>" #["<< /S /P /P 1 0 R >>"], []),
   ("a structure destination naming no structure element",
    navPdf "" "/A << /S /GoTo /D [3 0 R /Fit] /SD [4 0 R /Fit] >>", [.malformed]),
   ("a dangling reference as a link's action", navPdf "" "/A 9 0 R", [.malformed]),
   ("an action that is no dictionary", navPdf "" "/A [1 2]", [.malformed]),
   ("a destination above its page's media box, which a viewer clamps",
    navPdf "" "/Dest [3 0 R /XYZ 0 150 null]", []),
   ("a name tree leaf whose keys stand out of order",
    navPdf "/Names << /Dests << /Names [(z) [3 0 R /Fit] (a) [3 0 R /Fit]] >> >>" "/A << /S /GoTo /D (a) >>",
    [.undefined]),
   ("a name tree kid whose limits miss the key",
    navPdf "/Names << /Dests 6 0 R >>" "/A << /S /GoTo /D (here) >>"
      #["<< /Kids [7 0 R] >>", "<< /Limits [(m) (z)] /Names [(here) [3 0 R /Fit]] >>"],
    [.undefined]),
   ("an outline item with no parent, found through the outline",
    navPdf "/Outlines 6 0 R" "/Dest [3 0 R /Fit]"
      #["<< /Type /Outlines /First 7 0 R /Last 7 0 R /Count 1 >>", "<< /Title (Item) >>"],
    [.nowhere])]

/-- A deck's stages and sections land in both artifacts: an empty frame ships a page of its own, as
beamer's, what it names opening at that page's top, and a section answers to its slug, claimed in
one ledger with the frames, on its section page or the frame set next. -/
def deckDestinationChecks (ref : IO.Ref (List String)) (fs : Font.FontSet) : IO Unit := do
  let t := check ref
  -- A deck's sections answer to their slugs, claimed in one ledger with its frames, in both
  -- artifacts: on a section page, or riding the frame set next.
  for (pre, onPage) in [("\\usetheme{moloch}\n", true), ("\\AtBeginSection{}\n", false)] do
    let secSrc := "\\documentclass{beamer}\n" ++ pre ++ "\\begin{document}\n" ++
      "\\begin{frame}{Opening}\\href{#alpha}{to alpha} \\href{#gamma}{to gamma} " ++
      "\\href{#gamma-2}{to its frame}\\end{frame}\n" ++
      "\\section{Alpha}\n\\begin{frame}{First}FirstWords\\end{frame}\n" ++
      "\\section{Gamma}\n\\begin{frame}{Gamma}GammaWords\\end{frame}\n\\end{document}\n"
    let (sdoc, sds) := elabStr secSrc
    let sout := layoutOf fs sdoc
    let sanchors := Layout.anchorIndex sout.pages
    let shtml := HtmlDoc.emitTree {} sdoc
    let lands (f : String) := (Layout.landing? sanchors sout.pages f).map (·.page)
    let first := pageWith sout "FirstWords"
    let gammaFrame := pageWith sout "GammaWords"
    let unlanded := (shtml.2.2.filter (·.code == "W0326")).map (·.message)
    t s!"a deck's sections answer to their slugs in the web deck ({unlanded})"
      (sds.all (·.code != "W0301") && shtml.2.2.all (·.code != "W0326") &&
        ["alpha", "gamma", "gamma-2"].all fun id =>
          (attrValuesOf (fun _ => true) "id" (Html.elem "body" shtml.2.1 #[])).contains id)
    t s!"a deck's sections answer to their slugs in the PDF, each where it stands ({pdfLinks sout})"
      (pdfLinks sout == htmlLinks sdoc && (htmlLinks sdoc).size == 3 &&
        lands "gamma-2" == gammaFrame && gammaFrame.isSome &&
        (if onPage then lands "alpha" == first.map (· - 1) && lands "gamma" == gammaFrame.map (· - 1)
          else lands "alpha" == first && lands "gamma" == gammaFrame))
  -- An empty frame ships a page of its own, as beamer's, and what it names lands on that page's
  -- top, as does what a last frame setting nothing names.
  let emptySrc := "\\documentclass{beamer}\n\\begin{document}\n" ++
    "\\begin{frame}{One}OneWords, \\hyperlink{blank}{blank} \\hyperlink{fin}{end}.\\end{frame}\n" ++
    "\\begin{frame}\\hypertarget{blank}{}\\end{frame}\n" ++
    "\\begin{frame}{Two}TwoWords\\end{frame}\n" ++
    "\\begin{frame}\\hypertarget{fin}{}\\end{frame}\n\\end{document}\n"
  let (edoc, _) := elabStr emptySrc
  let eout := layoutOf fs edoc
  let egeom := Layout.Geom.ofPage edoc.page
  let epdf := Pdf.write egeom fs eout.pages edoc.info
  -- PDF coordinates round to a millipoint.
  let atTop (i : Nat) : Option (Nat × Array Obj) → Bool
    | some (j, ds) => j == i && ds[1]? == some (.name "XYZ") &&
        (ds[3]?.bind Obj.sp?).any fun y =>
          (y - (egeom.pageH + 2 * egeom.bleed)).natAbs ≤ ((spPerPt + 999) / 1000).toNat
    | none => false
  t s!"an empty frame ships a page of its own, its ink furniture alone ({eout.pages.size} pages)"
    (eout.pages.size == 4 && [1, 3].all fun i =>
      (eout.pages[i]?.any fun p => p.lines.all (·.furniture) && p.inks.isEmpty))
  t "what an empty frame names, and what a last frame setting nothing names, opens at its page's top"
    (match linkDestinations epdf with
     | .ok ds => atTop 1 ds[0]? && atTop 3 ds[1]?
     | .error _ => false)
  t "an empty frame: every navigation reaches a destination the file defines"
    ((PdfDests.ofBytes epdf).map (·.isEmpty) == .ok true)
  t "an empty frame: the web deck sets a stage for each page, the PDF's frame numbers on them"
    ((attrValuesOf (fun _ => true) "data-frame-number"
      (Html.elem "body" (docNodesOf edoc) #[])) == #["1", "2", "3", "4"])
  -- A break at the top of a frame that set nothing does nothing, as beamer's.
  for brk in ["\\newpage", "\\pagebreak", "\\clearpage"] do
    let (bdoc, _) := elabStr ("\\documentclass{beamer}\n\\begin{document}\n" ++
      "\\begin{frame}{One}OneWords\\end{frame}\n\\begin{frame}" ++ brk ++ " TextWords\\end{frame}\n" ++
      "\\begin{frame}{Two}TwoWords\\end{frame}\n\\end{document}\n")
    let bout := layoutOf fs bdoc
    t s!"a break opening an untitled frame ships no page of its own ({brk}: {bout.pages.size} pages)"
      (bout.pages.size == 3 && pageWith bout "TextWords" == some 1)
  -- An author's label keeps its name; a section or frame slug meeting it takes a numbered form.
  let (ldoc, _) := elabStr ("\\documentclass{beamer}\n\\usetheme{moloch}\n\\begin{document}\n" ++
    "\\begin{frame}{Opening}\\hyperlink{intro}{to the label}\\end{frame}\n\\section{Intro}\n" ++
    "\\begin{frame}{First}\\label{intro}FirstWords\\end{frame}\n\\end{document}\n")
  let lout := layoutOf fs ldoc
  let lids := attrValuesOf (fun _ => true) "id" (Html.elem "body" (docNodesOf ldoc) #[])
  t s!"a label and a section of one slug: one id each, the label keeping its name ({lids.filter (·.startsWith "intro")})"
    ((lids.filter (· == "intro")).size == 1 && lids.contains "intro-2" &&
      (Layout.landing? (Layout.anchorIndex lout.pages) lout.pages "intro").map (·.page) ==
        pageWith lout "FirstWords")

/-- Every navigation of a corpus file reaches a destination the file defines, a target stands at
what it names, and a resolved reference or citation links in both artifacts, equally often. -/
def pdfDestinationChecks (ref : IO.Ref (List String))
    (fs : Font.FontSet) (arts : Array GoldenArt) : IO Unit := do
  let t := check ref
  for (name, pdf, whys) in judgeCases do
    t s!"destination judge: {name}"
      ((PdfDests.ofBytes pdf).map (·.toList.map (·.why)) == .ok whys)
  let mathSet ← mathSetOf fs
  let shipped ← FontDiscovery.scanRoots [testFonts]
  for a in arts do
    let found := PdfDests.ofBytes a.pdf
    t s!"pdf destinations {a.name}: every navigation reaches a destination the file defines \
({(found.map (·.toList.map PdfDests.Finding.render)).toOption.getD ["unreadable"]})"
      (found.map (·.isEmpty) == .ok true)
    -- A link whose ink the single face cannot set is judged under the faces the fixture ships.
    let linked ← if htmlLinks a.doc == pdfLinks a.out then pure (pdfLinks a.out)
      else do
        let ffs ← fixtureFontSet fs mathSet shipped a.doc
        pure (pdfLinks (fittedOf ffs a.doc a.geom none (← corpusStore a.doc (some ffs))).out)
    t s!"pdf destinations {a.name}: the PDF links each in-page target as often as the HTML does \
({htmlLinks a.doc} against {linked})"
      (htmlLinks a.doc == linked)
    let anchors := Layout.anchorIndex a.out.pages
    t s!"pdf destinations {a.name}: every in-page link the pages carry lands"
      ((pdfLinks a.out).all fun f => (Layout.landing? anchors a.out.pages f).isSome)
    if a.doc.info.pdfx.isNone then
      t s!"pdf destinations {a.name}: the file carries one annotation per link that lands"
        ((PdfCensus.census a.pdf).map (·.linkAnnots) == .ok (Pdf.linkCount a.geom a.out.pages))
  let pre := "\\usepackage{hyperref,paracol}\n" ++
    "\\page{width=260pt,height=220pt,hmargin=24pt,vmargin=24pt}\n"
  let longText := String.join (List.replicate 24 "Earlier words occupy the available lines. ")
  let longColumn := String.join (List.replicate 24 "Earlier column words.\\par ")
  let targets : Array (String × String × String × String) := #[
    ("paragraph", "destination", "\\newpage\\hypertarget{destination}{TARGET words.}",
      "\\newpage TARGET words."),
    ("box", "destination", "\\newpage\\hypertarget{destination}{\\begin{minipage}{.6\\textwidth}" ++
      "TARGET words.\\par More words.\\end{minipage}}",
      "\\newpage\\begin{minipage}{.6\\textwidth}TARGET words.\\par More words.\\end{minipage}"),
    ("continued paragraph", "destination", "\\newpage " ++ longText ++
      "\\hypertarget{destination}{TARGET words.}",
      "\\newpage " ++ longText ++ "TARGET words."),
    ("word boundary", "destination", "\\newpage A\\hypertarget{destination}{V} TARGET words.",
      "\\newpage AV TARGET words."),
    ("standalone label", "destination", "\\newpage\\label{destination}TARGET words.",
      "\\newpage TARGET words."),
    ("table cell", "destination", "\\newpage\\begin{tabular}{ll}First&" ++
      "\\hypertarget{destination}{TARGET}\\\\Next&Last\\end{tabular}",
      "\\newpage\\begin{tabular}{ll}First&TARGET\\\\Next&Last\\end{tabular}"),
    ("column", "destination", "\\newpage\\begin{paracol}{2}Left.\\switchcolumn " ++
      "\\hypertarget{destination}{TARGET words.}\\end{paracol}",
      "\\newpage\\begin{paracol}{2}Left.\\switchcolumn TARGET words.\\end{paracol}"),
    ("overflowing left column", "destination", "\\newpage\\begin{paracol}{2}" ++ longColumn ++
      "\\switchcolumn\\hypertarget{destination}{TARGET words.}\\end{paracol}",
      "\\newpage\\begin{paracol}{2}" ++ longColumn ++
      "\\switchcolumn TARGET words.\\end{paracol}"),
    ("overflowing right column", "destination", "\\newpage\\begin{paracol}{2}" ++
      "\\hypertarget{destination}{TARGET words.}\\switchcolumn " ++ longColumn ++
      "\\end{paracol}",
      "\\newpage\\begin{paracol}{2}TARGET words.\\switchcolumn " ++ longColumn ++
      "\\end{paracol}"),
    ("a key its anchor spelling rewrites", "a b/c", "\\newpage\\hypertarget{a b/c}{TARGET words.}",
      "\\newpage TARGET words.")
  ]
  for (name, key, target, bare) in targets do
    let link := "\\hyperlink{" ++ key ++ "}{Jump to target.}\\par "
    let (doc, ds) := elabStr (dvDoc pre (link ++ target))
    let out := layoutOf fs doc
    let bareOut := layoutOf fs (elabStr (dvDoc pre (link ++ bare))).1
    t s!"{name}: target adds neither ink nor a break or kern"
      (pageGeometry out == pageGeometry bareOut &&
        shippedBodyGlyphs out == shippedBodyGlyphs bareOut)
    t s!"{name}: target and link elaborate without unknown-command recovery"
      (ds.all fun d => !["W0301", "W0302"].contains d.code)
    let geom := Layout.Geom.ofPage doc.page
    let pdf := Pdf.write geom fs out.pages doc.info
    let dest := linkDestination pdf
    t s!"{name}: the PDF link reaches the page carrying the target"
      (pageWith out "TARGET" != none &&
        dest.map (·.map (·.1)) == .ok (pageWith out "TARGET"))
    t s!"{name}: the PDF destination opens at the target line's ink"
      (match dest, lineWith bareOut "TARGET" with
       | .ok (some (_, ds)), some line => opensAt fs geom ds line
       | _, _ => false)
    t s!"{name}: every navigation reaches a destination the file defines"
      ((PdfDests.ofBytes pdf).map (·.isEmpty) == .ok true)
  let filler := String.join (List.replicate 60 "Earlier words fill the page.\n\n")
  let (mdoc, mds) := elabMd ("[Jump to target.](#destination)\n\n" ++ filler ++
    "<a name=\"destination\"></a>TARGET words.\n")
  let mout := layoutOf fs mdoc
  let mpdf := Pdf.write (Layout.Geom.ofPage mdoc.page) fs mout.pages mdoc.info
  t "a markdown target: the PDF link reaches the later page carrying it"
    (mds.all (·.kind != .E0390) && (pageWith mout "TARGET").any (· > 0) &&
      (linkDestination mpdf).map (·.map (·.1)) == .ok (pageWith mout "TARGET"))
  let doc := (elabStr (dvDoc pre
    ("\\hyperlink{destination}{Jump.}\\par\\newpage" ++
      "\\hypertarget{destination}{\\begin{minipage}{.6\\textwidth}" ++
      "TARGET words.\\end{minipage}}"))).1
  let trees := doc.body.map (HtmlDoc.blockNode {})
  let ids := trees.foldl
    (fun acc n => acc ++ attrValuesOf (fun _ => true) "id" n) #[]
  let links := trees.foldl
    (fun acc n => acc ++ attrValuesOf (· == "a") "href" n) #[]
  t "the HTML keeps the same internal destination spelling"
    (ids.contains "destination" && links.contains "#destination")
  -- A citation and a reference link in both artifacts, each landing on its target's line.
  let bib := "@article{probe2020, author = {Example, Alice}, title = {A Probe Title},\n\
    journal = {Journal of Examples}, year = {2020}}\n"
  let (cdoc, _) := bibBuild (dvDoc "" ("\\section{One}\\label{s}\n" ++
    "Some words cite \\cite{probe2020} and refer to Section~\\ref{s}.\n" ++
    "\\bibliographystyle{plain}\\bibliography{c}")) #[("c", bib)]
  let cout := layoutOf fs cdoc
  let cgeom := Layout.Geom.ofPage cdoc.page
  let cpdf := Pdf.write cgeom fs cout.pages cdoc.info
  let cdests := linkDestinations cpdf
  t "a citation and a reference: both link in the PDF, as in the HTML"
    (cdests.map (·.size) == .ok 2 && htmlLinks cdoc == #["ref-probe2020", "s"] &&
      pdfLinks cout == #["ref-probe2020", "s"])
  t "a citation: its destination opens at its reference-list entry's line, not the page top"
    (match cdests, lineWith cout "Alice" with
     | .ok ds, some entry => ds[0]?.any fun (_, d) => opensAt fs cgeom d entry
     | _, _ => false)
  t "a reference to a label written after its heading: its destination opens at the heading"
    (match cdests, lineWith cout "One" with
     | .ok ds, some heading => ds[1]?.any fun (_, d) => opensAt fs cgeom d heading
     | _, _ => false)
  t "a citation and a reference: every navigation reaches a destination the file defines"
    ((PdfDests.ofBytes cpdf).map (·.isEmpty) == .ok true)
  -- The document's top, where HTML reads it for a fragment no anchor claims (§7.4.6.4).
  for frag in ["top", "Top", ""] do
    let (tdoc, _) := elabStr (dvDoc pre ("First page words.\\newpage\\href{#" ++ frag ++
      "}{Back to the top.}"))
    let tout := layoutOf fs tdoc
    let tgeom := Layout.Geom.ofPage tdoc.page
    let tdest := linkDestination (Pdf.write tgeom fs tout.pages tdoc.info)
    t s!"a link to '#{frag}': it opens at the first page's top"
      (match tdest with
       | .ok (some (0, ds)) =>
         ds[1]? == some (.name "XYZ") && ds[2]? == some (.int 0) &&
           ds[3]?.bind Obj.sp? == some (tgeom.pageH + 2 * tgeom.bleed)
       | _ => false)
  let (adoc, _) := elabStr (dvDoc pre ("Words.\\newpage\\hypertarget{top}{TARGET words.}" ++
    "\\href{#top}{Up.}"))
  let aout := layoutOf fs adoc
  t "a link to '#top' where an anchor claims it: it lands on that anchor"
    ((linkDestination (Pdf.write (Layout.Geom.ofPage adoc.page) fs aout.pages adoc.info)).map
      (·.map (·.1)) == .ok (some 1))
  -- A link landing nowhere ships its text unlinked, named once for the PDF.
  let (ddoc, _) := elabStr (dvDoc pre
    "\\hyperlink{missing}{Nowhere.} \\hyperlink{missing}{Again.}")
  let dout := layoutOf fs ddoc
  let dpdf := Pdf.write (Layout.Geom.ofPage ddoc.page) fs dout.pages ddoc.info
  t "a link landing nowhere: the PDF carries no annotation for it"
    ((PdfCensus.census dpdf).map (·.linkAnnots) == .ok 0)
  t "a link landing nowhere: named once for the PDF"
    ((dout.diags.filter fun d => d.code == "W0326" && d.output == some .pdf).size == 1)
  -- A link holding a reference keeps the enclosing link alone, as the web page does.
  let (odoc, _) := elabStr (dvDoc "" ("\\section{One}\\label{s}" ++
    "\\href{https://example.org/}{see Section \\ref{s}}"))
  let oout := layoutOf fs odoc
  let opdf := Pdf.write (Layout.Geom.ofPage odoc.page) fs oout.pages odoc.info
  t "a reference inside a link: the enclosing link alone ships, in both artifacts"
    (htmlLinks odoc == #[] && pdfLinks oout == #[] &&
      (PdfCensus.census opdf).map (·.linkAnnots) == .ok 1)
  -- A label written right after its heading names the heading; any other label or target its line.
  let (hdoc, _) := elabStr (dvDoc "" ("\\section{One}\\hypertarget{h}{}\\label{a}Target words here." ++
    "\\par Later words.\\label{s}\\par\\paragraph{Run-in.}\\label{r}Run words.\\par " ++
    "See \\ref{a}, \\ref{s}, \\ref{r} and \\hyperlink{h}{there}."))
  let hout := layoutOf fs hdoc
  let hgeom := Layout.Geom.ofPage hdoc.page
  let hdests := linkDestinations (Pdf.write hgeom fs hout.pages hdoc.info)
  let landsOn (i : Nat) (text : String) : Bool :=
    match hdests, lineWith hout text with
    | .ok ds, some line => ds[i]?.any fun (_, d) => opensAt fs hgeom d line
    | _, _ => false
  t "a label written right after its heading: its destination opens at the heading"
    (landsOn 0 "One")
  t "a label later under its heading, or after a run-in heading: it opens at its own line"
    (landsOn 1 "Later words" && landsOn 2 "Run-in")
  t "a target after a heading: its destination opens at its own line" (landsOn 3 "Target words")
  let headings := elemNodesList (· == "h2") #[] (docNodesOf hdoc).toList
  let headingIds := headings.flatMap (attrValuesOf (fun _ => true) "id")
  t s!"the web page sets the label written right after its heading in the heading, alone ({headingIds})"
    (headingIds.contains "a" && ["h", "s", "r"].all (!headingIds.contains ·) &&
      ["h", "s", "r"].all (attrValuesOf (fun _ => true) "id"
        (Html.elem "body" (docNodesOf hdoc) #[])).contains)
  -- A float's label opens at the float's top: a caption standing above, a picture's ink.
  let (fdoc, _) := elabStr (dvDoc "" ("See Table~\\ref{t} and Figure~\\ref{p}.\\par" ++
    "\\begin{table}[h]\\caption{Table caption words.}\\label{t}" ++
    "\\begin{tabular}{ll}Cell&Cell\\\\\\end{tabular}\\end{table}" ++
    "\\begin{figure}[h]\\begin{tikzpicture}\\draw (0,0) rectangle (3,1);\\end{tikzpicture}" ++
    "\\caption{Figure caption words.}\\label{p}\\end{figure}"))
  let fout := layoutOf fs fdoc
  let fgeom := Layout.Geom.ofPage fdoc.page
  let fdests := linkDestinations (Pdf.write fgeom fs fout.pages fdoc.info)
  t "a caption standing above: its float's label opens at the caption"
    (match fdests, lineWith fout "Table caption" with
     | .ok ds, some cap => ds[0]?.any fun (_, d) => opensAt fs fgeom d cap
     | _, _ => false)
  let ink := (fout.pages.flatMap (·.inks))[0]?
  t "a picture standing first: its float's label opens at the picture's top"
    (match fdests, ink with
     | .ok ds, some k =>
       let tolerance := ((spPerPt + 999) / 1000).toNat
       ds[1]?.any fun (_, d) => d[1]? == some (.name "XYZ") &&
         (match d[2]?.bind Obj.sp?, d[3]?.bind Obj.sp? with
          | some x, some y =>
            (x - (k.topLeft.1 + fgeom.bleed)).natAbs ≤ tolerance &&
              (y - (fgeom.pageH + fgeom.bleed - k.topLeft.2)).natAbs ≤ tolerance
          | _, _ => false)
     | _, _ => false)
  -- A deck's stages answer to the names its web deck's do: frames, steps, routes, section pages.
  let deckSrc := "\\documentclass{beamer}\n\\title{Deck Title}\n\\begin{document}\n\\maketitle\n" ++
    "\\section{Divider}\n\\begin{frame}{Intro}\n\\href{#1}{one} \\href{#1.2}{step} " ++
    "\\href{#titlepage}{title} \\href{#section-0}{divider} \\href{#intro}{intro} " ++
    "\\href{#intro-2}{second} \\href{#aside}{aside}\n\n\\pause\nLater words.\n\\end{frame}\n" ++
    "\\begin{frame}[standout]{Aside}Aside words.\\end{frame}\n\\end{document}\n"
  let (ddoc', dds) := elabStr deckSrc
  let dout' := layoutOf fs ddoc'
  let danchors := Layout.anchorIndex dout'.pages
  let htmlDs := (HtmlDoc.emitTree {} ddoc').2.2
  t s!"a deck's stage names: the web deck resolves each ({htmlDs.filter (·.code == "W0326") |>.map (·.message)})"
    (dds.all (·.code != "W0301") && htmlDs.all (·.code != "W0326"))
  t s!"a deck's stage names: each lands in the PDF ({pdfLinks dout'})"
    (pdfLinks dout' == htmlLinks ddoc' && (htmlLinks ddoc').size == 7 &&
      (pdfLinks dout').all fun f => (Layout.landing? danchors dout'.pages f).isSome)
  t "a deck's stage names: a step's route lands on that step's page"
    (match Layout.landing? danchors dout'.pages "1.2", Layout.landing? danchors dout'.pages "1.1" with
     | some a, some b => a.page == b.page + 1
     | _, _ => false)
  -- Sections sharing a title claim numbered anchors, the same in both artifacts.
  let (sdoc, _) := elabStr (dvDoc pre ("\\href{#twin-2}{To the second.}\\section{Twin}Words." ++
    "\\newpage\\section{Twin}TARGET words.\\section{}Untitled."))
  let sout := layoutOf fs sdoc
  let sgeom := Layout.Geom.ofPage sdoc.page
  let spdf := Pdf.write sgeom fs sout.pages sdoc.info
  t "sections sharing a title: a link to the second's numbered anchor lands on its page"
    (htmlLinks sdoc == #["twin-2"] && pdfLinks sout == #["twin-2"] &&
      (linkDestination spdf).map (·.map (·.1)) == .ok (pageWith sout "TARGET"))
  t "sections sharing a title: every navigation reaches a destination the file defines"
    ((PdfDests.ofBytes spdf).map (·.isEmpty) == .ok true)
  -- A citation links to its entry only where a reference list sets the entry.
  let skip := "@misc{a, author = {Ash, Ada}, title = {Alpha Notes}, year = {2001},\n\
    options = {skipbib}}\n@misc{b, author = {Birch, Bo}, title = {Beta Notes}, year = {2002}}\n"
  let (kdoc, _) := bibBuild ("\\documentclass{article}\n\\usepackage[style=numeric]{biblatex}\n" ++
    "\\addbibresource{s.bib}\n\\begin{document}\nCite \\cite{a} and \\cite{b}.\n" ++
    "\\printbibliography\n\\end{document}\n") #[("s", skip)]
  let kout := layoutOf fs kdoc
  let kpdf := Pdf.write (Layout.Geom.ofPage kdoc.page) fs kout.pages kdoc.info
  t "a citation of an entry no list sets: unlinked in both artifacts, the listed one linked"
    (htmlLinks kdoc == #["ref-b"] && pdfLinks kout == #["ref-b"] &&
      (PdfCensus.census kpdf).map (·.linkAnnots) == .ok 1)
  deckDestinationChecks ref fs
