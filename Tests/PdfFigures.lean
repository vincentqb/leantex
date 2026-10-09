module

public import Tests.GfxMatrix

public section

open LeanTex.Core

namespace Tests.PdfFigures

open Tests.GfxMatrix

def ops0 (fig : Gfx.Figure Empty) : Array Pdf.ContentOp :=
  GfxPdf.emit (fun _ => 0) (fun _ e => nomatch e) pdfPlace fig

def table (fig : Gfx.Figure Empty) : Array Pdf.FigRes := Pdf.collectList #[] (ops0 fig).toList

def named (fig : Gfx.Figure Empty) : Array Pdf.ContentOp := Pdf.nameOps (table fig) (ops0 fig)

def isForm : Pdf.FigRes → Bool
  | .form _ _ => true
  | .extG _ _ => false
  | .pattern _ => false
  | .shading _ => false

def isPattern : Pdf.FigRes → Bool
  | .pattern _ => true
  | .form _ _ => false
  | .extG _ _ => false
  | .shading _ => false

end Tests.PdfFigures

open Tests.PdfFigures Tests.GfxMatrix in
/-- **The figure-resource table over the synthetic matrix**, asserted over
the typed operators: renaming moves no mark (`Pdf.nameOps_marks_id`,
executed), every name the renamed operators spell is a place in the table
(`Pdf.nameOps_names_covers`), every occurrence of a name names one resource
(`Pdf.nameOps_occ_agree`); a symbol used twice is one form both uses name;
equal requests share one entry; and two gradients that differ only in a
stop colour's PDF rider are two patterns, because requests compare field
by field. Invented geometry. -/
def pdfFiguresChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (name, fig) in cases do
    let tb := table fig
    let ops := named fig
    t s!"figure resources {name}: renaming moves no mark"
      (GfxPdf.readMarks pdfPlace ops == GfxPdf.readMarks pdfPlace (ops0 fig))
    t s!"figure resources {name}: every name is a place in the table"
      ((Pdf.namesList ops.toList).all (· < tb.size))
    let occ := Pdf.occList ops.toList
    t s!"figure resources {name}: one name, one resource"
      (occ.all fun p => occ.all fun q => p.1 != q.1 || decide (p.2 = q.2))
    t s!"figure resources {name}: the writer's walk is the occurrence list"
      (Pdf.occInto #[] ops.toList == occ.toArray)
  let some (_, f5) := cases[5]? | t "figure resources: cases" false
  t "figure resources: a symbol used twice is one form both uses name"
    (((table f5).filter isForm).size == 1 &&
      (match named f5 with
       | #[.xobject _ a .symbol _, .xobject _ b .symbol _] => a == b
       | _ => false))
  let g (c : Ir.Color) : Gfx.Gradient :=
    .linear (0, 0) (Dim.pt 10, 0) #[{ offset := 0, color := c }, { offset := 65536, color := blue }]
      Gfx.Affine.unit
  let fillG (c : Ir.Color) : Gfx.Node Empty :=
    .draw square (some { paint := .gradient (g c), rule := .nonzero, alpha := Gfx.Alpha.opaque }) none
  let twice := figure #[fillG red, fillG red]
  t "figure resources: equal requests share one entry"
    (((table twice).filter isPattern).size == 1)
  let redCmyk : Ir.Color := { red with pdfModel := some (.cmyk "0" "1" "1" "0") }
  let riders := figure #[fillG red, fillG redCmyk]
  t "figure resources: the stop colours' screen values agree, their PDF riders do not"
    (redCmyk == red && ((table riders).filter isPattern).size == 2)

open Tests.GfxMatrix in
/-- **The document writer spells the figure-resource table**: a page whose
inks name an ExtGState, a shading pattern and forms (the matrix's
gradient, alpha group and symbol figures) writes one resources object the
page names, every name its content stream and its forms spell resolves in
that dictionary, and every form names the same resources — read back
through the engine's own reader. Invented geometry. -/
def pdfFigureWriterChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let figs := #[1, 4, 5].filterMap fun i => (cases[i]?).map (·.2)
  let inks : Array Layout.InkOut := figs.map fun f =>
    { fig := f, place := { flipY := true, dx := Dim.pt 50, dy := Dim.pt 300 }, leaf := none }
  let pages : Array Layout.PageOut := #[{ inks := inks }]
  let geom : Layout.Geom := {}
  let pdf := Pdf.write geom oneFace pages
  match PdfRead.objects pdf with
  | .error e => t s!"figure writer: the file reads back: {e}" false
  | .ok objects =>
    let es := objects.val
    let obj (n : Nat) : PdfRead.Obj := ((es.find? (·.num == n)).map (·.val)).getD .null
    let table := Pdf.tableOf geom oneFace pages {} #[]
    let res := obj table.resId
    t "figure writer: the page names the one resources object"
      ((es.find? fun e => e.val.get? "Type" == some (.name "Page")).any fun e =>
        e.val.get? "Resources" == some (.ref table.resId 0))
    let group (key : String) : Array (String × PdfRead.Obj) := match res.get? key with
      | some (.dict d) => d
      | _ => #[]
    t "figure writer: the resources hold the table's ExtGStates, patterns and forms"
      (!(group "ExtGState").isEmpty && !(group "Pattern").isEmpty &&
        (group "XObject").any (·.1.startsWith "Fm"))
    let content := (es.filterMap fun e => if e.val.get? "Type" == none && e.stream.isSome &&
        e.val.get? "Subtype" == none then
        (PdfRead.decodeStream e.val (e.stream.getD ByteArray.empty)).toOption else none)
    let names (b : ByteArray) : Array String :=
      (((String.fromUTF8? b).getD "").splitOn " ").toArray.filter fun w =>
        ["/GS", "/P", "/Fm"].any fun p => w.startsWith p && w.length > p.length &&
          (w.drop p.length).toString.all Char.isDigit
    let known := (group "ExtGState" ++ group "Pattern" ++ group "XObject").map (·.1)
    let forms := es.filter fun e => e.val.get? "Subtype" == some (.name "Form")
    let formContent := forms.filterMap fun e =>
      (PdfRead.decodeStream e.val (e.stream.getD ByteArray.empty)).toOption
    t "figure writer: every name a stream spells is a resource"
      ((content ++ formContent).all fun b => (names b).all fun n => known.contains (n.drop 1).toString)
    t "figure writer: some stream names a figure resource"
      ((content ++ formContent).any fun b => !(names b).isEmpty)
    t "figure writer: every form names the shared resources"
      (!forms.isEmpty && forms.all fun e => e.val.get? "Resources" == some (.ref table.resId 0))
    t "figure writer: the alpha group's form is an isolated transparency group"
      (forms.any fun e => match e.val.get? "Group" with
        | some g => g.get? "S" == some (.name "Transparency") && g.get? "I" == some (.bool true)
        | none => false)
