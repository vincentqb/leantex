module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Dim
open LeanTex.Core.PdfRead (Obj)

/-- Resolve the link's destination through the actual PDF page references.
An annotation holding a URI fragment is not an internal PDF destination
(ISO 32000-2 §§12.3.2, 12.6.4.2). -/
private def linkDestination (pdf : ByteArray) :
    Except String (Option (Nat × Array Obj)) := do
  let es ← PdfRead.objects pdf
  let pages := es.val.filter (fun e => PdfCensus.kindOf e.val == .page)
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
            return (pages.findIdx? (·.num == n)).map (·, ds)
  return none

private def pageWith (out : Layout.Out) (text : String) : Option Nat :=
  out.pages.findIdx? fun p => p.lines.any (fun l => hasStr (lineText l) text)

private def pageGeometry (out : Layout.Out) :=
  out.pages.map fun p => p.lines.filterMap fun l =>
    if l.furniture then none else some (l.x, l.y, l.setWidth, lineText l)

/-- A target is zero-ink metadata tied to the line that actually ships it.
Links before the target, a target in a continued paragraph, and targets in
columns all navigate using the final page order. The guard reads PDF objects,
not the writer's URL field; target neutrality is checked on shipped lines. -/
def pdfDestinationChecks (ref : IO.Ref (List String))
    (fs : Font.FontSet) : IO Unit := do
  let t := check ref
  let pre := "\\usepackage{hyperref,paracol}\n" ++
    "\\page{width=260pt,height=220pt,hmargin=24pt,vmargin=24pt}\n"
  let longText := String.join (List.replicate 24 "Earlier words occupy the available lines. ")
  let longColumn := String.join (List.replicate 24 "Earlier column words.\\par ")
  let targets : Array (String × String × String) := #[
    ("paragraph", "\\newpage\\hypertarget{destination}{TARGET words.}",
      "\\newpage TARGET words."),
    ("box", "\\newpage\\hypertarget{destination}{\\begin{minipage}{.6\\textwidth}" ++
      "TARGET words.\\par More words.\\end{minipage}}",
      "\\newpage\\begin{minipage}{.6\\textwidth}TARGET words.\\par More words.\\end{minipage}"),
    ("continued paragraph", "\\newpage " ++ longText ++
      "\\hypertarget{destination}{TARGET words.}",
      "\\newpage " ++ longText ++ "TARGET words."),
    ("word boundary", "\\newpage A\\hypertarget{destination}{V} TARGET words.",
      "\\newpage AV TARGET words."),
    ("standalone label", "\\newpage\\label{destination}TARGET words.",
      "\\newpage TARGET words."),
    ("table cell", "\\newpage\\begin{tabular}{ll}First&" ++
      "\\hypertarget{destination}{TARGET}\\\\Next&Last\\end{tabular}",
      "\\newpage\\begin{tabular}{ll}First&TARGET\\\\Next&Last\\end{tabular}"),
    ("column", "\\newpage\\begin{paracol}{2}Left.\\switchcolumn " ++
      "\\hypertarget{destination}{TARGET words.}\\end{paracol}",
      "\\newpage\\begin{paracol}{2}Left.\\switchcolumn TARGET words.\\end{paracol}"),
    ("overflowing left column", "\\newpage\\begin{paracol}{2}" ++ longColumn ++
      "\\switchcolumn\\hypertarget{destination}{TARGET words.}\\end{paracol}",
      "\\newpage\\begin{paracol}{2}" ++ longColumn ++
      "\\switchcolumn TARGET words.\\end{paracol}"),
    ("overflowing right column", "\\newpage\\begin{paracol}{2}" ++
      "\\hypertarget{destination}{TARGET words.}\\switchcolumn " ++ longColumn ++
      "\\end{paracol}",
      "\\newpage\\begin{paracol}{2}TARGET words.\\switchcolumn " ++ longColumn ++
      "\\end{paracol}")
  ]
  for (name, target, bare) in targets do
    let link := "\\hyperlink{destination}{Jump to target.}\\par "
    let (doc, ds) := elabStr (dvDoc pre (link ++ target))
    let out := layoutOf fs doc
    let bareOut := layoutOf fs (elabStr (dvDoc pre (link ++ bare))).1
    t s!"{name}: target adds neither ink nor a break or kern"
      (pageGeometry out == pageGeometry bareOut &&
        shippedBodyGlyphs out == shippedBodyGlyphs bareOut)
    t s!"{name}: target and link elaborate without unknown-command recovery"
      (ds.all fun d => !["W0301", "W0302"].contains d.code)
    let pdf := Pdf.write (Layout.Geom.ofPage doc.page) fs out.pages doc.info
    let dest := linkDestination pdf
    t s!"{name}: the PDF link reaches the page carrying the target"
      (pageWith out "TARGET" != none &&
        dest.map (·.map (·.1)) == .ok (pageWith out "TARGET"))
    let line := (pageWith bareOut "TARGET").bind fun i =>
      bareOut.pages[i]?.bind fun p => p.lines.find? (fun l => hasStr (lineText l) "TARGET")
    t s!"{name}: the PDF destination opens at the target line's ink"
      (match dest, line with
       | .ok (some (_, ds)), some line =>
         let geom := Layout.Geom.ofPage doc.page
         -- PDF coordinates are rounded to a millipoint, independently read
         -- from the emitted numeric objects; the line is from the bare control.
         let tolerance := (spPerPt + 999) / 1000
         ds[1]? == some (.name "XYZ") && ds[4]? == some .null &&
           (match ds[2]?.bind Obj.sp?, ds[3]?.bind Obj.sp? with
            | some x, some y =>
              (x - (line.x + geom.bleed)).natAbs ≤ tolerance.toNat &&
                (y - (geom.pageH + geom.bleed - line.y +
                  (Layout.segsInk fs line.segs).1)).natAbs ≤ tolerance.toNat
            | _, _ => false)
       | _, _ => false)
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
