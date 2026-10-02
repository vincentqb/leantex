import Tests.FontMath

open LeanTex.Core

namespace Tests

/-- The resolver rewrites listing captions and formatted bibliography items,
so alphabet losses there must be named beside the fallback each artifact ships. -/
def mathAlphaRegionChecks (ref : IO.Ref (List String)) (fs : Font.FontSet) : IO Unit := do
  let family := fs.math.bind (fs.fonts[·]?) |>.map (·.family) |>.getD "math face"
  let (sample, _) := elabStr "\\pagestyle{empty}$\\mathcal{A}\\mathcal{A}$"
  let content : Array Ir.Inline ← match sample.body[0]? with
    | some (Ir.Block.para content) => pure content
    | _ => throw (IO.userError "math alphabet region witness did not elaborate a paragraph")
  let regions : Array (String × Ir.Block) := #[
    ("listing caption", .verbatim none "" { caption := some (1, content) }),
    ("bibliography item", .bibliography "" none
      #[{ key := "synthetic", marker := none, content := content }])]
  let notes (ds : Array Diag) := (ds.filter (·.code == "N0018")).map (·.subject)
  for (region, block) in regions do
    let label := "math alphabet " ++ region
    let raw := { sample with body := #[block] }
    let (resolved, ads) := Ir.resolveMathAlphas fs.mathAlphabets family raw
    let geom := Layout.Geom.ofPage raw.page
    let direct := Layout.run geom fs none raw
    let (_, body, hds) := HtmlDoc.emitTree { fonts := some fs } raw
    check ref (label ++ " belongs to the alphabet census")
      (Ir.missingMathAlphas fs.mathAlphabets raw == #[.cal])
    check ref (label ++ " ships ordinary italic from the math face")
      ((bodyGlyphs direct).filter (fun p => p.1 == 6) == #[(6, '𝐴'), (6, '𝐴')])
    check ref (label ++ " ships ordinary italic in typed MathML")
      (mathTextLeavesList #[] body.toList == #[("𝐴", ""), ("𝐴", "")])
    check ref (label ++ " IR names repeated alphabet loss once")
      (notes ads == #[some "math-alpha:cal"])
    check ref (label ++ " Layout names repeated alphabet loss once")
      (notes direct.diags == #[some "math-alpha:cal"])
    check ref (label ++ " HTML names repeated alphabet loss once")
      (notes hds == #[some "math-alpha:cal"])
    check ref (label ++ " resolution leaves no alphabet debt")
      ((Ir.missingMathAlphas fs.mathAlphabets resolved).isEmpty &&
        (Ir.resolveMathAlphas fs.mathAlphabets family resolved).2.isEmpty)

/-- Public backend entries own normalization. Calling them on raw IR must
ship the same glyphs and MathML as an explicit IR resolution, with the
whole-alphabet diagnostic charged once. -/
def mathAlphaEntryChecks (ref : IO.Ref (List String)) : IO Unit := do
  let fs ← mathTextFaces
  let family := fs.math.bind (fs.fonts[·]?) |>.map (·.family) |>.getD "math face"
  let bold := "font-family: var(--font-body); font-weight: 700"
  -- The nested symbol loss is pinned by mathSymbolResetAccountingChecks;
  -- mathChecks pins unsupported calligraphic fallback to ordinary italic.
  let rows : Array (String × Array (Nat × Char) × Array (String × String) ×
      Array (Option String)) := #[
    ("\\symbf{A}", #[(6, '𝐀')], #[("𝐀", "")], #[]),
    ("\\mathbf{A}", #[(1, 'A')], #[("A", bold)], #[]),
    ("\\mathbf{A\\symsf{5}A}", #[(1, 'A'), (6, '5'), (1, 'A')],
      #[("A", bold), ("5", ""), ("A", bold)], #[some "math-alpha:sf"]),
    ("\\mathcal{A}\\mathcal{A}", #[(6, '𝐴'), (6, '𝐴')],
      #[("𝐴", ""), ("𝐴", "")], #[some "math-alpha:cal"])]
  let notes (ds : Array Diag) := (ds.filter (·.code == "N0018")).map (·.subject)
  for (source, glyphs, leaves, subjects) in rows do
    let label := "math alphabet entry " ++ source
    let (raw, ds) := elabStr ("\\pagestyle{empty}$" ++ source ++ "$")
    check ref (label ++ " elaborates without recovery")
      (!ds.any fun d => d.severity == .error || d.code == "W0012")
    let (resolved, ads) := Ir.resolveMathAlphas fs.mathAlphabets family raw
    let geom := Layout.Geom.ofPage raw.page
    let direct := Layout.run geom fs none raw
    let prepared := Layout.run geom fs none resolved
    let (_, body, hds) := HtmlDoc.emitTree { fonts := some fs } raw
    let (_, preparedBody, phds) := HtmlDoc.emitTree { fonts := some fs } resolved
    check ref (label ++ " ships the declared faces and scalars")
      (bodyGlyphs direct == glyphs)
    check ref (label ++ " ships the declared typed MathML")
      (mathTextLeavesList #[] body.toList == leaves)
    check ref (label ++ " public Layout agrees with explicit resolution")
      (Pdf.write geom fs direct.pages raw.info {} direct.outline ==
        Pdf.write geom fs prepared.pages raw.info {} prepared.outline)
    check ref (label ++ " public HTML agrees with explicit resolution")
      (body.map (Html.render · 0) == preparedBody.map (Html.render · 0))
    check ref (label ++ " Layout names each missing alphabet once")
      (notes direct.diags == subjects && notes (ads ++ prepared.diags) == subjects)
    check ref (label ++ " HTML names each missing alphabet once")
      (notes hds == subjects && notes (ads ++ phds) == subjects)
    check ref (label ++ " already resolved entries add no alphabet note")
      ((notes prepared.diags).isEmpty && (notes phds).isEmpty)
  mathAlphaRegionChecks ref fs

end Tests
