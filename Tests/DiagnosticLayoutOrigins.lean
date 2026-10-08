module

public import Tests.Artifact
public import LeanTex.Cli.Render

public section

open LeanTex.Core LeanTex.Cli

namespace DiagnosticLayoutOrigins

/-- Equality of a location intentionally ignores expansion metadata. These
guards also read the exact command and origin stack carried to shipment. -/
private def sameSource (actual : Option Span) (expected : Span) : Bool :=
  actual.any fun s =>
    s == expected && s.pos.command == expected.pos.command &&
      s.pos.origins == expected.pos.origins

private def sourceAt (file : String) (line col : Nat) (command : String) : Span :=
  { file, pos := { line, col, command := some command } }

private def run (fs : Font.FontSet) (geom : Layout.Geom) (doc : Ir.Doc)
    (sites : Array (String × Span) := #[]) : Layout.Out :=
  Layout.run geom fs none doc (pictureSpans := Layout.pictureSpansForPdf doc sites)

private def parse (fs : Font.FontSet) (file source : String) :=
  let raws := (Parse.parse file (Lex.lex file source).1).1
  let prepared := Elab.prepare file raws
  let geom := Layout.Geom.ofPage (Elab.run file source).1.page
  let (doc, ds, sites) := Elab.runPrepared file prepared
    (picMetric := Layout.labelMetric geom fs)
  (doc, ds, sites.images, prepared.sourceTriggers)

private def picture : String :=
  "\\begin{tikzpicture}\\fill (0,0) rectangle (40,1);\\end{tikzpicture}"

end DiagnosticLayoutOrigins

/-- Diagnostic attribution is metadata: use the exact box/line that raised
the deficit, preserve expansion evidence, and leave Layout.Out paint and the
driver's PDF bytes unchanged. Missing source evidence stays missing rather
than borrowing a neighbouring declaration. All source here is invented. -/
def diagnosticLayoutOriginChecks (ref : IO.Ref (List String))
    (fs : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {
    pageW := Dim.pt 160, pageH := Dim.pt 400, hmargin := Dim.pt 12, vmargin := Dim.pt 12
    fontSize := Dim.pt 10, justify := false, hyphenate := false }
  let first : Span := {
    file := "line-origin.tex"
    pos := { line := 2, col := 1, command := some "\\wideword"
             origins := [{ id := 7, name := "wideword" }] } }
  let second := { first with pos := {
    first.pos with line := 5, command := some "\\otherword"
                   origins := [{ id := 13, name := "otherword" }] } }
  let word := Ir.Inline.text ("".pushn 'W' 96)
  let content := #[.located first #[word], .linebreak {}, .located second #[word]]
  let doc : Ir.Doc := { body := #[.para content] }
  let out := Layout.run geom fs none doc
  let overfull := out.diags.filter (·.kind == .W0005)
  t "layout origins: body overflow keeps each line's command and expansion"
    (overfull.size == 2 &&
      overfull.any (fun d => DiagnosticLayoutOrigins.sameSource d.span first &&
        d.trigger == first.pos.command) &&
      overfull.any (fun d => DiagnosticLayoutOrigins.sameSource d.span second &&
        d.trigger == second.pos.command))
  let notes : Ir.Doc := { body := #[.para #[.text "Note", .footnote (some 1) content]] }
  let noteOut := Layout.run geom fs none notes
  let noteDiags := noteOut.diags.filter (·.kind == .W0005)
  t "layout origins: footnote overflow keeps commands after generated mark insertion"
    (noteDiags.size == 2 &&
      noteDiags.any (fun d => DiagnosticLayoutOrigins.sameSource d.span first &&
        d.trigger == first.pos.command) &&
      noteDiags.any (fun d => DiagnosticLayoutOrigins.sameSource d.span second &&
        d.trigger == second.pos.command))
  t "layout origins: overflow CLI human and JSON retain the written command"
    (overfull.any fun d =>
      (Render.human false d).startsWith "⚠ [W0005] - line-origin.tex:2:1 - \\wideword\n" &&
      hasStr (Render.porcelainDiag d) "\"trigger\":\"\\\\wideword\"")
  let bare := Ir.eraseLocations doc
  let bareOut := Layout.run geom fs none bare
  t "layout origins: line metadata preserves shipped paint and PDF bytes"
    (reprStr out.pages == reprStr bareOut.pages &&
      driverPdf fs geom doc out == driverPdf fs geom bare bareOut)
  t "layout origins: absent overflow evidence does not borrow a command"
    ((bareOut.diags.filter (·.kind == .W0005)).size == 1 &&
      (bareOut.diags.filter (·.kind == .W0005)).all fun d =>
      d.span.isNone && d.trigger.isNone &&
        d.message == "2 overfull lines (no feasible break)")
  let pictureSource :=
    "\\documentclass{article}\\pictures{tool=none}\\begin{document}\n" ++
    DiagnosticLayoutOrigins.picture ++ "\n" ++ DiagnosticLayoutOrigins.picture ++
    "\n\\end{document}"
  let (picDoc, picDs, picSites, _) := DiagnosticLayoutOrigins.parse fs "picture-origin.tex" pictureSource
  let picGeom := Layout.Geom.ofPage picDoc.page
  let pics := DiagnosticLayoutOrigins.run fs picGeom picDoc picSites
  let picDiags := pics.diags.filter (·.kind == .W0335)
  t "layout origins: identical unlabelled pictures keep distinct opening sites"
    (picDs.all (·.severity != .error) && picSites.size == 2 && picDiags.size == 2 &&
      picDiags.any (fun d =>
        DiagnosticLayoutOrigins.sameSource d.span
          (DiagnosticLayoutOrigins.sourceAt "picture-origin.tex" 2 1 "\\begin") &&
        d.trigger == some "\\begin") &&
      picDiags.any (fun d =>
        DiagnosticLayoutOrigins.sameSource d.span
          (DiagnosticLayoutOrigins.sourceAt "picture-origin.tex" 3 1 "\\begin") &&
        d.trigger == some "\\begin"))
  let plainPics := Layout.run picGeom fs none picDoc
  t "layout origins: picture metadata preserves shipped paint and PDF bytes"
    (reprStr pics.pages == reprStr plainPics.pages &&
      driverPdf fs picGeom picDoc pics == driverPdf fs picGeom picDoc plainPics)
  let secondPicture := DiagnosticLayoutOrigins.sourceAt "picture-origin.tex" 3 1 "\\begin"
  let sparse := DiagnosticLayoutOrigins.run fs picGeom picDoc (picSites.extract 1 2)
  let sparseDiags := sparse.diags.filter (·.kind == .W0335)
  t "layout origins: a missing picture site cannot shift the next picture's source"
    (sparseDiags.size == 2 &&
      (sparseDiags.filter fun d => d.span.isNone && d.trigger.isNone).size == 1 &&
      (sparseDiags.filter fun d =>
        DiagnosticLayoutOrigins.sameSource d.span secondPicture &&
        d.trigger == some "\\begin").size == 1)
  let hidden := { picDoc with body := #[
    .para #[.text "Prefix"], .only #["html"] #[picDoc.body[0]!], picDoc.body[1]!] }
  let hiddenOut := DiagnosticLayoutOrigins.run fs picGeom hidden picSites
  let hiddenDiags := hiddenOut.diags.filter (·.kind == .W0335)
  t "layout origins: PDF filtering preserves authored picture ordinals"
    (hiddenDiags.size == 1 && hiddenDiags.all fun d =>
      DiagnosticLayoutOrigins.sameSource d.span secondPicture && d.trigger == some "\\begin")
  let steps := { picDoc with docClass := .slides, body := #[
    .frame #[] false .top false (picDoc.body.push
      (.onSteps { first := 2, last := none } #[.para #[.text "Next step"]]))] }
  let stepOut := DiagnosticLayoutOrigins.run fs picGeom steps picSites
  let stepDiags := stepOut.diags.filter (·.kind == .W0335)
  t "layout origins: overlay replay keeps one source per authored picture"
    (stepOut.pages.size == 2 && stepDiags.size == 2 &&
      [2, 3].all fun line =>
        (stepDiags.filter fun d =>
          DiagnosticLayoutOrigins.sameSource d.span
            (DiagnosticLayoutOrigins.sourceAt "picture-origin.tex" line 1 "\\begin") &&
          d.trigger == some "\\begin").size == 1)
  let (picShrinkDoc, picShrinkDs, picShrinkSites, _) := DiagnosticLayoutOrigins.parse fs
    "picture-shrink-origin.tex"
    ("\\documentclass{article}\\pictures{tool=none}\\begin{document}\nLead.\n\n" ++
      "\\vspace{20pt minus 8pt}\n" ++ DiagnosticLayoutOrigins.picture ++ "\n\\end{document}")
  let roomyGeom := Layout.Geom.ofPage picShrinkDoc.page
  let roomy := Layout.run roomyGeom fs none picShrinkDoc
  let bottom := roomy.pages.foldl (fun y p =>
    p.fills.foldl (fun y f => max y (f.y + f.h)) y) 0
  let tightGeom := { roomyGeom with pageH := bottom + roomyGeom.vmargin - Dim.pt 4 }
  let picShrinkOut := DiagnosticLayoutOrigins.run fs tightGeom picShrinkDoc picShrinkSites
  let picShrinkDiags := picShrinkOut.diags.filter (·.kind == .N0200)
  t "layout origins: a picture that consumes shrink retains its opening source"
    (picShrinkDs.all (·.severity != .error) && picShrinkOut.pages.size == 1 &&
      picShrinkDiags.size == 1 && picShrinkDiags.all fun d =>
        DiagnosticLayoutOrigins.sameSource d.span
          (DiagnosticLayoutOrigins.sourceAt "picture-shrink-origin.tex" 5 1 "\\begin") &&
        d.trigger == some "\\begin")
  let shrinkSource :=
    "\\documentclass{article}\\page{height=127pt,margin=20pt}" ++
    "\\newcommand{\\firstline}{First.}\\newcommand{\\secondline}{Second.}" ++
    "\\newcommand{\\thirdline}{Third.}\\begin{document}\n" ++
    "\\firstline\n\n\\vspace{20pt minus 8pt}\n\\secondline\n\n" ++
    "\\vspace{20pt minus 8pt}\n\\thirdline\n\\end{document}"
  let (shrinkDoc, shrinkDs, _, triggers) :=
    DiagnosticLayoutOrigins.parse fs "shrink-origin.tex" shrinkSource
  let shrinkGeom := Layout.Geom.ofPage shrinkDoc.page
  let shrunk := Layout.run shrinkGeom fs none shrinkDoc
  let shrinkDiags := (shrunk.diags.filter (·.kind == .N0200)).map triggers.attribute
  t "layout origins: shrink reports the box that actually increased the deficit"
    (shrinkDs.all (·.severity != .error) && shrunk.pages.size == 1 && shrinkDiags.size == 1 &&
      shrinkDiags.all fun d =>
        d.span.any (fun s => s.file == "shrink-origin.tex" && s.pos.line == 8 && s.pos.col == 1) &&
        d.trigger == some "\\thirdline")
  t "layout origins: shrink CLI emits the exact authored macro call"
    (shrinkDiags.any fun d =>
      hasStr (Render.porcelainDiag d) "\"file\":\"shrink-origin.tex\"" &&
      hasStr (Render.porcelainDiag d) "\"line\":8" &&
      hasStr (Render.porcelainDiag d) "\"trigger\":\"\\\\thirdline\"" &&
      hasStr (Render.human false d) "shrink-origin.tex:8:1 - \\thirdline")
  let unlocatedShrink := Ir.eraseLocations shrinkDoc
  let unlocatedOut := Layout.run shrinkGeom fs none unlocatedShrink
  t "layout origins: shrink metadata preserves shipped paint and PDF bytes"
    (reprStr shrunk.pages == reprStr unlocatedOut.pages &&
      driverPdf fs shrinkGeom shrinkDoc shrunk ==
        driverPdf fs shrinkGeom unlocatedShrink unlocatedOut)
  t "layout origins: unlocated shrink remains unattributed"
    ((unlocatedOut.diags.filter (·.kind == .N0200)).size == 1 &&
      (unlocatedOut.diags.filter (·.kind == .N0200)).all fun d =>
      d.span.isNone && d.trigger.isNone)
  let later := DiagnosticLayoutOrigins.sourceAt "shrink-origin.tex" 10 1 "\\shortline"
  let columns := { shrinkDoc with body := #[.columns #[
    (.share, shrinkDoc.body), (.share, #[.para #[.located later #[.text "Short."]]])]] }
  let columnOut := Layout.run shrinkGeom fs none columns
  let columnDiags := (columnOut.diags.filter (·.kind == .N0200)).map triggers.attribute
  let bareColumns := Ir.eraseLocations columns
  let bareColumnOut := Layout.run shrinkGeom fs none bareColumns
  t "layout origins: a later short column cannot steal the shrink source"
    (columnOut.pages.size == 1 && columnDiags.size == 1 && columnDiags.all fun d =>
      d.span.any (fun s => s.file == "shrink-origin.tex" && s.pos.line == 8 && s.pos.col == 1) &&
      d.trigger == some "\\thirdline")
  t "layout origins: column provenance preserves shipped paint and PDF bytes"
    (reprStr columnOut.pages == reprStr bareColumnOut.pages &&
      driverPdf fs shrinkGeom columns columnOut ==
        driverPdf fs shrinkGeom bareColumns bareColumnOut)
