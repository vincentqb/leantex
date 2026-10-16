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

private def sortedUnique (xs : Array String) : Array String :=
  (xs.qsort (· < ·)).foldl (fun acc x => if acc.back? == some x then acc else acc.push x) #[]

/-- The in-page fragments a document's HTML links to, each once; a note's mark and back-link are
the endnote list's own apparatus. -/
private def htmlFragments (doc : Ir.Doc) : Array String :=
  sortedUnique ((elemAttrsList (· == "a") #[] (docNodesOf doc).toList).filterMap fun (_, attrs) =>
    match HtmlDoc.attrOf? attrs "href", HtmlDoc.attrOf? attrs "role" with
    | some h, role =>
      if h.startsWith "#" && role != some "doc-noteref" && role != some "doc-backlink" then
        some (h.drop 1).toString
      else none
    | none, _ => none)

/-- The in-page fragments a laid-out document links to, each once: its runs' and block links' and
its outline's. -/
private def pdfFragments (out : Layout.Out) : Array String :=
  let frag (u : String) : Option String := if u.startsWith "#" then some (u.drop 1).toString else none
  let runs := out.pages.foldl (init := #[]) fun acc p =>
    p.lines.foldl (init := acc ++ p.links.filterMap (frag ·.target)) fun acc l =>
      l.segs.foldl (init := acc) fun acc s => match s with
        | .run _ _ (some u) .. => (frag u).elim acc acc.push
        | _ => acc
  sortedUnique (runs ++ out.outline.filterMap (·.fragment))

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
    navPdf "" "/Dest [3 0 R /Fit] /AA << /E << /S /GoTo /D (gone) >> >>", [.undefined])]

/-- A target is zero-ink metadata tied to the line that ships it; every link navigates by the final
page order to a destination the file defines, in every corpus file; and a cross-reference links in
the PDF exactly where it links in the HTML. -/
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
    let linked ← if htmlFragments a.doc == pdfFragments a.out then pure (pdfFragments a.out)
      else do
        let ffs ← fixtureFontSet fs mathSet shipped a.doc
        pure (pdfFragments (fittedOf ffs a.doc a.geom none (← corpusStore a.doc (some ffs))).out)
    t s!"pdf destinations {a.name}: the PDF links exactly the in-page targets the HTML links \
({htmlFragments a.doc} against {linked})"
      (htmlFragments a.doc == linked)
    let anchors := Layout.anchorIndex a.out.pages
    t s!"pdf destinations {a.name}: every in-page link the pages carry lands"
      ((pdfFragments a.out).all fun f => (Layout.landing? anchors a.out.pages f).isSome)
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
    (cdests.map (·.size) == .ok 2 && htmlFragments cdoc == #["ref-probe2020", "s"] &&
      pdfFragments cout == #["ref-probe2020", "s"])
  t "a citation: its destination opens at its reference-list entry's line, not the page top"
    (match cdests, lineWith cout "Alice" with
     | .ok ds, some entry => ds[0]?.any fun (_, d) => opensAt fs cgeom d entry
     | _, _ => false)
  t "a reference: its destination opens at the line its label stands on"
    (match cdests, lineWith cout "Some words" with
     | .ok ds, some labelled => ds[1]?.any fun (_, d) => opensAt fs cgeom d labelled
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
  -- An enclosing link wins over a cross-reference inside it, as no anchor nests in the HTML.
  let (odoc, _) := elabStr (dvDoc "" ("\\section{One}\\label{s}" ++
    "\\href{https://example.org/}{see Section \\ref{s}}"))
  let oout := layoutOf fs odoc
  let opdf := Pdf.write (Layout.Geom.ofPage odoc.page) fs oout.pages odoc.info
  t "a reference inside a link: the enclosing link alone ships, in both artifacts"
    (htmlFragments odoc == #[] && pdfFragments oout == #[] &&
      (PdfCensus.census opdf).map (·.linkAnnots) == .ok 1)
  -- Sections sharing a title claim numbered anchors, the same in both artifacts.
  let (sdoc, _) := elabStr (dvDoc pre ("\\href{#twin-2}{To the second.}\\section{Twin}Words." ++
    "\\newpage\\section{Twin}TARGET words.\\section{}Untitled."))
  let sout := layoutOf fs sdoc
  let sgeom := Layout.Geom.ofPage sdoc.page
  let spdf := Pdf.write sgeom fs sout.pages sdoc.info
  t "sections sharing a title: a link to the second's numbered anchor lands on its page"
    (htmlFragments sdoc == #["twin-2"] && pdfFragments sout == #["twin-2"] &&
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
    (htmlFragments kdoc == #["ref-b"] && pdfFragments kout == #["ref-b"] &&
      (PdfCensus.census kpdf).map (·.linkAnnots) == .ok 1)
