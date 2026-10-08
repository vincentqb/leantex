import Tests.Support

open LeanTex.Core

/-! Frame heading invariant: an explicit IR heading inside a frame belongs
to that frame's body. For a short body, its preceding text, heading and
following text ship together, under the frame's ground, vertical
distribution and footer. Only headings outside frames open slide dividers.

This is the contract of `Ir.Block.section`, including headings supplied by
a second surface reader. It is not a claim that Beamer's metadata-only
`\section`, `\subsection` or `\subsubsection` commands paint headings:
a synthetic default-Beamer LuaLaTeX probe, without section hooks, leaves
the same one-page raster when those declarations are inserted in a frame. -/

namespace FrameHeadingScope

/-- Synthetic IR, shared with the rendered-PDF acceptance probe. Both the
progress-divider path and its fallback see the same three local headings;
the empty chrome variant also exercises the frame reader without a band. -/
def doc (progress footer : Bool) (valign : Ir.VAlign)
    (levels : Array Ir.HeadingLevel := #[1, 2, 3]) : Ir.Doc :=
  let base := (elabStr (deck169 "\\theme{moloch}" "")).1
  let palette := if progress then base.palette else
    (["progressfg", "progressbg", "sectionprogressfg", "sectionprogressbg"].foldl
      Ir.Palette.erase base.palette)
  let palette := palette.declare "bg" { r := 237, g := 246, b := 249 }
  let prologue := if footer then #[Ir.Block.framefoot #[.text "Frame footer"]] else #[]
  let body := #[Ir.Block.para #[.text "Before"]] ++
    levels.map (fun level => .section level true none #[.text s!"Heading {level}"]) ++
    #[Ir.Block.para #[.text "After"]]
  { base with
    palette := palette
    chrome := if footer then { footerRight := some .frameNumber } else {}
    body := prologue ++ #[.frame #[.text "Frame title"] false valign false body] }

private def hasClass (attrs : Array (String × String)) (cls : String) : Bool :=
  attrs.any fun (key, value) => key == "class" && (value.splitOn " ").contains cls

mutual

private def frameNodesOne (acc : Array Html.Node) : Html.Node → Array Html.Node
  | .elem tag attrs kids =>
    if tag == "section" && hasClass attrs "slide" then acc.push (.elem tag attrs kids)
    else frameNodesList acc kids.toList
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc

private def frameNodesList (acc : Array Html.Node) : List Html.Node → Array Html.Node
  | [] => acc
  | node :: rest => frameNodesList (frameNodesOne acc node) rest

end

/-- Direct frame children, including the declared distribution spacers.
The header and footer have their own assertions; local headings must
remain children of the same stage as the surrounding paragraphs. -/
private def bodyShape : Html.Node → Array (String × String)
  | .elem _ _ kids => kids.filterMap fun node => match node with
    | .elem tag attrs _ =>
      if tag == "div" && hasClass attrs "fill" then
        some ("fill", ((attrs.find? (·.1 == "style")).map (·.2)).getD "")
      else if tag == "p" || tag == "h2" || tag == "h3" || tag == "h4" then
        some (tag, (nodeTextOne "" node).trimAscii.toString)
      else none
    | .text _ => none
    | .style _ => none
    | .script _ _ => none
  | .text _ => #[]
  | .style _ => #[]
  | .script _ _ => #[]

private def expectedShape (valign : Ir.VAlign) (levels : Array Ir.HeadingLevel) :
    Array (String × String) :=
  let (above, below) := Ir.VAlign.shares valign
  let spacer (n : Nat) := if n == 0 then #[] else #[("fill", s!"flex-grow: {n}")]
  let leading := spacer above
  let trailing := spacer below
  let headings := levels.map (fun level => (s!"h{Ir.headingRank level}", s!"Heading {level}"))
  leading ++ #[("p", "Before")] ++ headings ++ #[("p", "After")] ++ trailing

private def markedLines (out : Layout.Out) (marks : Array String) : Array Layout.LineOut :=
  (allLines out).filter fun line => marks.contains (lineText line).trimAscii.toString

private def groundOn (geom : Layout.Geom) (color : Ir.Color) (page : Layout.PageOut) : Bool :=
  let want := geom.ground color
  page.fills.any fun fill =>
    fill.x == want.x && fill.y == want.y && fill.w == want.w &&
    fill.h == want.h && fill.color == want.color

end FrameHeadingScope

/-- Artifact guard for local levels 1–3, separately and together: frame
membership, paint order, ground, footer ink and body distribution in
`Layout.Out`, and heading rank, containment and spacer shares in the
typed HTML tree. Top-level divider behavior remains independently pinned. -/
def frameHeadingScopeChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  for progress in [false, true] do
    for footer in [false, true] do
      for levels in [#[1], #[2], #[3], #[1, 2, 3]] do
        let marks := #["Before"] ++ levels.map (fun n => s!"Heading {n}") ++ #["After"]
        let mut positions : Array (Array Dim.Sp) := #[]
        let mut titleYs : Array (Option Dim.Sp) := #[]
        for valign in [Ir.VAlign.top, .center, .bottom] do
          let label := s!"frame heading scope {progress}/{footer}/{levels}/{repr valign}"
          let doc := FrameHeadingScope.doc progress footer valign levels
          let out := layoutOf fonts doc
          let (_, html, _) := HtmlDoc.emitTree {} doc
          let stages := FrameHeadingScope.frameNodesList #[] html.toList
          let ink := FrameHeadingScope.markedLines out marks
          t (label ++ " ships the whole short body on its frame")
            (out.pages.size == 1 && out.pages[0]!.frame == some 1 &&
             ink.map (fun line => (lineText line).trimAscii.toString) == marks)
          t (label ++ " keeps its ground")
            (out.pages.size == 1 && FrameHeadingScope.groundOn
              (Layout.Geom.ofPage doc.page) { r := 237, g := 246, b := 249 } out.pages[0]!)
          let wantFoot := if footer then #[("Frame footer", "1")] else #[]
          t (label ++ " keeps its footer in both artifacts")
            (pdfFoots out == wantFoot && slideFootsList #[] html.toList == wantFoot &&
             (allLines out).any (fun line =>
               (lineText line).trimAscii.toString == "Frame footer") == footer)
          t (label ++ " keeps typed headings and spacers inside one HTML stage")
            (stages.size == 1 &&
             FrameHeadingScope.bodyShape stages[0]! == FrameHeadingScope.expectedShape valign levels)
          positions := positions.push (ink.map (·.y))
          titleYs := titleYs.push (((allLines out).find? fun line =>
            (lineText line).trimAscii.toString == "Frame title").map (·.y))
        t s!"frame heading scope {progress}/{footer}/{levels} distributes the whole body"
          (positions.size == 3 && positions.all (·.size == marks.size) &&
           (List.range marks.size).all (fun i =>
             positions[0]![i]! < positions[1]![i]! &&
             positions[1]![i]! < positions[2]![i]! &&
             positions[1]![i]! - positions[0]![i]! == positions[1]![0]! - positions[0]![0]! &&
             positions[2]![i]! - positions[1]![i]! == positions[2]![0]! - positions[1]![0]!) &&
           titleYs[0]!.isSome && titleYs[0]! == titleYs[1]! && titleYs[1]! == titleYs[2]!)
    -- A title frame's ground differs from the deck's: opening a divider
    -- here would visibly replace it even if its text happened to fit.
    let base := FrameHeadingScope.doc progress false .golden #[1]
    let ground : Ir.Color := { r := 231, g := 242, b := 222 }
    let doc := { base with palette := base.palette.declare "titlepagebg" ground }
    let out := layoutOf fonts doc
    let (_, html, _) := HtmlDoc.emitTree {} doc
    let stages := FrameHeadingScope.frameNodesList #[] html.toList
    t s!"frame heading scope preserves the distinct title-frame ground {progress}"
      (out.pages.size == 1 && FrameHeadingScope.groundOn
        (Layout.Geom.ofPage doc.page) ground out.pages[0]! &&
       stages.size == 1 && (match stages[0]! with
         | .elem _ attrs _ => FrameHeadingScope.hasClass attrs "title-page"
         | .text _ => false
         | .style _ => false
         | .script _ _ => false) &&
       FrameHeadingScope.bodyShape stages[0]! == FrameHeadingScope.expectedShape .golden #[1])
    for level in [1, 2, 3] do
      let base := FrameHeadingScope.doc progress true .center
      let doc := { base with body := #[
        .framefoot #[.text "Frame footer"],
        .frame #[] false .center false #[.para #[.text "First frame"]],
        .section level true none #[.text "Divider"],
        .frame #[] false .center false #[.para #[.text "Second frame"]]] }
      let out := layoutOf fonts doc
      t s!"frame heading scope preserves top-level divider {progress}/{level}"
        (out.pages.size == 3 && out.pages[0]!.frame == some 1 &&
         out.pages[1]!.frame.isNone && out.pages[1]!.foot.isNone &&
         out.pages[2]!.frame == some 2 &&
         (out.pages[1]!.lines.map fun line => (lineText line).trimAscii.toString) == #["Divider"] &&
         pdfFoots out == #[("Frame footer", "1"), ("Frame footer", "2")])
  -- `ChromeSlot.sectionTitle` names the enclosing top-level section.
  -- A local heading must not leak that state into the following frame.
  let base := FrameHeadingScope.doc true true .center
  let doc := { base with
    chrome := { footerLeft := some .sectionTitle }
    body := #[
      .section 1 true none #[.text "Outer section"],
      .frame #[] false .center false #[
        .para #[.text "Before"], .section 1 true none #[.text "Local heading"], .para #[.text "After"]],
      .frame #[] false .center false #[.para #[.text "Next frame"]]] }
  let out := layoutOf fonts doc
  let (_, html, _) := HtmlDoc.emitTree {} doc
  t "frame heading scope preserves the top-level section footer across frames"
    (out.pages.size == 3 && pdfFoots out == #[("Outer section", ""), ("Outer section", "")] &&
     slideFootsList #[] html.toList == #[("Outer section", ""), ("Outer section", "")])
