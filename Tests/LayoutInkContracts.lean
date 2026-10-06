import LeanTex.Core.Layout.InkContract
import Tests.Support

namespace Tests.LayoutInkContracts

open LeanTex.Core

private def inkContractPicture (content : Array Ir.Inline) : Ir.Pic.Picture :=
  { declared := some ((Dim.pt (-50), Dim.pt (-20)), (Dim.pt 100, Dim.pt 40))
    shapes := #[.label 0 0 content .black 1000 .center] }

private def inkContractDoc (pic : Ir.Pic.Picture) : Ir.Doc :=
  { body := #[.picture pic]
    tokens := ({} : Ir.Tokens).declare "topskip" {} }

private def named (out : Layout.Out) (code : DiagCode) (content : Array Ir.Inline) : Bool :=
  out.diags.any fun d => d.kind == code && d.subject == some (Ir.plainText content)

private def labelPaintedText (out : Layout.Out) : String :=
  String.ofList ((bodyGlyphs out).toList.map (·.2))

private def placement (out : Layout.Out) :=
  (bodyLines out).map fun line =>
    (line.x, line.y, line.size, line.setWidth,
      line.segs.filterMap fun seg => match seg with
      | .run idx _ _ w glyphs size _ _ raise _ _ => some (idx, w, glyphs, size, raise)
      | .image _ _ _ | .rule _ _ _ _ | .decoration _ _ _ _ _
        | .poly _ _ | .gap _ _ | .decoratedGap _ _ _ => none)

/-- Exercise the production boundary, starting from a real producer result.
The two integrity guards are tested by deleting that result's line or
shrinking its reservation. No witness constructs a diagnostic. The
unresolved-outline case changes only the external font answer. -/
def boundaryWitness (fs : Font.FontSet) (code : DiagCode) : Array Diag :=
  let geom : Layout.Geom := {}
  let source : Span := {
    file := "label.tex"
    pos := {
      line := 7
      col := 4
      origins := [⟨2, "caption"⟩]
      command := some "\\node" } }
  let content : Array Ir.Inline := #[.located source #[.text "Label"]]
  let xHeight := fs.body.xHeight * geom.fontSize / fs.body.unitsPerEm
  let result := Layout.labelResult fs {} geom xHeight none content .black 1000
  let reserved := Layout.pictureLabelBox fs {} geom xHeight 0 0 content 1000 .center
  let finish := Layout.finishLabel fs none ⟨0, 0, 0, 0⟩ 0 0 content .center
  match code with
  | .W0394 =>
    let unknown := { fs with fonts := fs.fonts.map fun f =>
      { f with inkExtent := Thunk.mk fun _ => #[] } }
    (Layout.run geom unknown none (inkContractDoc (inkContractPicture content))).diags
  | .E0395 => (finish { result with line? := none } reserved).diags
  | .W0396 => (finish result ((0, 0), (0, 0))).diags
  | _ => #[]

/-- Checks over actual shipped pages. Font arguments come from the committed
fixture corpus; changing only outline answers models that external boundary. -/
def layoutInkChecks (record : String → Bool → IO Unit) (serif sans : Font.Font) : IO Unit := do
  let fs : Font.FontSet := { fonts := #[serif, sans], index := #[((1, 400, false), 1)] }
  let geom : Layout.Geom := {}
  let run (fonts : Font.FontSet) (content : Array Ir.Inline) :=
    Layout.run geom fonts none (inkContractDoc (inkContractPicture content))
  let accent : Array Ir.Inline := #[.text "É"]
  let out := run fs accent
  let metric := Layout.labelMetric geom fs {} accent 1000
  let baseline := Ir.Pic.labelBaseline 0 .center metric
  let alignment := Ir.Pic.labelInkBox 0 0 .center metric
  let glyphBox := Ir.Pic.labelGlyphBox 0 0 .center metric
  let actualHi := (serif.gid 'É').bind fun gid => (serif.yExtent gid).map fun e =>
    e.2 * geom.fontSize / serif.unitsPerEm
  record "the old cap-box obligation is false on a shipped accented label"
    (labelPaintedText out == "É" && match actualHi with
      | none => false
      | some hi =>
        baseline + hi > alignment.2.2 &&
        !(out.diags.any fun d => d.subject == some (Ir.plainText accent)) &&
        baseline + hi ≤ glyphBox.2.2)
  record "the accented label ships one measured line"
    ((bodyLines out).size == 1 && !(named out .W0394 accent))

  let unresolved : Font.Font := { serif with inkExtent := Thunk.mk fun _ => #[] }
  let unknownFonts := { fs with fonts := #[unresolved, sans] }
  let unknown := run unknownFonts accent
  record "a shipped unresolved glyph has W0394 with its label subject"
    (labelPaintedText unknown == "É" && named unknown .W0394 accent)
  record "missing outline evidence changes no glyph placement in a declared box"
    (placement unknown == placement out)
  let source : Span := {
    file := "label.tex"
    pos := {
      line := 7
      col := 4
      origins := [⟨3, "outer"⟩, ⟨8, "caption"⟩]
      command := some "\\node" } }
  let later : Span := { file := "label.tex", pos := { line := 12, col := 9 } }
  let located : Array Ir.Inline :=
    #[.located source accent, .linebreak {}, .located later #[.text "later"]]
  let locatedOut := run unknownFonts located
  record "missing outlines retain the source of the line actually emitted"
    (locatedOut.diags.any fun d =>
      d.kind == .W0394 && d.subject == some (Ir.plainText located) &&
        d.span == some source)
  record "missing-outline accounting retains macro ancestry and the control token"
    (locatedOut.diags.any fun d =>
      d.kind == .W0394 && d.span.any fun s =>
        s.pos.origins == source.pos.origins && s.pos.command == source.pos.command)
  record "line truncation retains the emitted line's source"
    (locatedOut.diags.any fun d =>
      d.kind == .W0328 && d.subject == some (Ir.plainText located) &&
        d.span == some source)

  let mixed : Array Ir.Inline :=
    #[.styled .sans #[.styled (.size "Huge") #[.text "É"]], .text "x"]
  let mixedOut := run unknownFonts mixed
  record "a larger measured glyph cannot hide a smaller unresolved glyph"
    (labelPaintedText mixedOut == "Éx" && named mixedOut .W0394 mixed &&
      (bodyLines mixedOut).any fun line =>
        line.segs.any fun seg => match seg with
        | .run idx _ _ _ _ size _ _ _ _ _ => idx == 1 && size > geom.fontSize
        | .image _ _ _ | .rule _ _ _ _ | .decoration _ _ _ _ _
          | .poly _ _ | .gap _ _ | .decoratedGap _ _ _ => false)
  record "known mixed-face and mixed-size glyphs need no unresolved warning"
    (labelPaintedText (run fs mixed) == "Éx" && !(named (run fs mixed) .W0394 mixed))

  let wrapped : Array Ir.Inline := #[.text "alpha", .linebreak {}, .text "beta"]
  let wrappedOut := run fs wrapped
  record "the real two-line producer names first-line truncation"
    (labelPaintedText wrappedOut == "alpha" && named wrappedOut .W0328 wrapped)
  record "wrapping never suppresses an unresolved-outline diagnostic"
    (named (run unknownFonts wrapped) .W0328 wrapped &&
      named (run unknownFonts wrapped) .W0394 wrapped)

  for blank in #[#[], #[.text ""], #[.text "   "], #[.styled .bold #[.text " "]]] do
    let blankOut := run fs blank
    record "textually blank labels are silent and paint no glyph"
      (labelPaintedText blankOut == "" && blankOut.diags.isEmpty)

  let missing : Array Ir.Inline := #[.text (String.singleton (Char.ofNat 0x10ffff))]
  let missingOut := run fs missing
  record "the real glyph refusal is preserved and supplies the label key"
    (labelPaintedText missingOut == "" && named missingOut .E0405 missing)
  record "an existing glyph refusal is not counted twice as an absent label"
    (!(named missingOut .E0395 missing))
  let locatedMissing : Array Ir.Inline := #[.located source missing]
  record "naming a producer refusal preserves its original source span"
    ((run fs locatedMissing).diags.any fun d =>
      d.kind == .E0405 && d.subject == some (Ir.plainText locatedMissing) &&
        d.span == some source)

  let sibling : Array Ir.Inline := #[.text "omega"]
  let pic : Ir.Pic.Picture :=
    { (inkContractPicture accent) with shapes := #[
      .label 0 0 accent .black 1000 .center,
      .rect 0 0 (Dim.pt 1) (Dim.pt 1) .black,
      .label (Dim.pt 20) (Dim.pt 10) sibling .black 1000 .center] }
  let siblingOut := Layout.run geom unknownFonts none (inkContractDoc pic)
  record "later shapes preserve the earlier label's keyed loss"
    (labelPaintedText siblingOut == "Éomega" &&
      named siblingOut .W0394 accent && named siblingOut .W0394 sibling)

  let pagesDoc : Ir.Doc :=
    { (inkContractDoc (inkContractPicture accent)) with body := #[
      .picture (inkContractPicture accent), .pagebreak, .picture (inkContractPicture sibling)] }
  let pagesOut := Layout.run geom unknownFonts none pagesDoc
  record "page closure and later pictures preserve unresolved label accounts"
    (pagesOut.pages.size == 2 &&
      named pagesOut .W0394 accent && named pagesOut .W0394 sibling)

  for code in #[DiagCode.W0394, .E0395, .W0396] do
    let ds := boundaryWitness fs code
    record s!"the real label decision fires {code.code} at its own failing input"
      (ds.any fun d => d.kind == code && d.subject == some "Label")
    record s!"{code.code} retains complete provenance at its production boundary"
      (ds.any fun d => d.kind == code && d.span.any fun s =>
        s.file == "label.tex" && s.pos.line == 7 && s.pos.col == 4 &&
          s.pos.origins == [⟨2, "caption"⟩] && s.pos.command == some "\\node")

/-- Load the committed fonts and run the shipped-page and guard checks from
the diagnostic suite, whose witness registry consumes the same decisions. -/
def fixtureChecks (ref : IO.Ref (List String)) : IO Unit := do
  let load (name : String) : IO Font.Font := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => return f
    | .error e => throw (IO.userError e)
  layoutInkChecks (check ref) (← load "SourceSerifPro-Regular.otf")
    (← load "FiraSans-Regular.otf")

end Tests.LayoutInkContracts
