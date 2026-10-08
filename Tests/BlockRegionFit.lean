module

public import LeanTex.Core.Font
import LeanTex.Core.Layout
import LeanTex.Core.Elab

open LeanTex.Core

namespace Tests.BlockRegionFit

private def check (ref : IO.Ref (List String)) (name : String) (ok : Bool) : IO Unit :=
  unless ok do ref.modify (name :: ·)

private def outerColor : Ir.Color := { r := 221, g := 238, b := 255 }
private def innerColor : Ir.Color := { r := 242, g := 211, b := 178 }
private def blueBar : Ir.Color := { r := 32, g := 64, b := 96 }
private def brownBar : Ir.Color := { r := 112, g := 64, b := 32 }

private def isSurface (fill : Layout.Fill) : Bool :=
  #[outerColor, innerColor, blueBar, brownBar].contains fill.color

private def lineText (line : Layout.LineOut) : String :=
  String.ofList (line.segs.toList.flatMap Layout.Seg.glyphChars)

private def bodyText (out : Layout.Out) : Array String :=
  (out.pages.flatMap (·.lines) |>.filter (!·.furniture) |>.map lineText).filter
    (fun text => !text.isEmpty)

private def hasText (page : Layout.PageOut) (text : String) : Bool :=
  page.lines.any fun line => !line.furniture && lineText line == text

private def insideMedium (geom : Layout.Geom) (fill : Layout.Fill) : Bool :=
  0 < fill.w && 0 < fill.h && 0 ≤ fill.x && 0 ≤ fill.y &&
    fill.x + fill.w ≤ geom.pageW && fill.y + fill.h ≤ geom.pageH

/-- beamer's colour boxes are `\textwidth` wide at every depth: a child
shares its parent's reach and stands at least the parent's inset inside it
above and below. -/
private def encloses (pad : Dim.Sp) (outer inner : Layout.Fill) : Bool :=
  0 < pad && outer.x == inner.x && outer.w == inner.w && outer.y + pad ≤ inner.y &&
    inner.y + inner.h + pad ≤ outer.y + outer.h

/-- Judge the child's entire painted extent, including its title bar.
Checking only the body rectangle misses the ancestor's lost top inset. -/
private def parentInsets (page : Layout.PageOut) (pad : Dim.Sp)
    (childBar : Ir.Color) : Bool :=
  page.fills.all fun child =>
    if child.color == innerColor || child.color == childBar then
      page.fills.any fun outer => outer.color == outerColor && encloses pad outer child
    else true

/-- A painted title meets its painted body through `\nointerlineskip
\vskip-0.5pt` (beamerinnerthemedefault.sty): the body overlaps it by half
a point. -/
private def titleJoins (page : Layout.PageOut) (bodyColor barColor : Ir.Color) : Bool :=
  page.fills.all fun bar =>
    if bar.color == barColor then
      page.fills.any fun body =>
        body.color == bodyColor && bar.x == body.x && bar.w == body.w &&
          bar.y + bar.h == body.y + Ir.blockSeam
    else true

/-- Invented feasible two-line counterexample: a titleless parent at a
tight page edge must reserve the child's complete title bar before fitting. -/
public def titleSource : String :=
  "\\documentclass{article}\n" ++
  "\\fonts{body=\"Source Serif Pro\",mono=\"Source Code Pro\",math=\"Fira Math\"}\n" ++
  "\\output{formats=pdf}\n" ++
  "\\page{width=220pt,height=100pt,hmargin=10pt,vmargin=1pt,fontsize=10pt}\n" ++
  "\\palette{fg=#101010,bg=#FFFFFF,blockbodybg=#DDEEFF," ++
    "examplebodybg=#F2D3B2,exampletitlebg=#204060}\n" ++
  "\\begin{document}\n\\begin{block}{}\n\\begin{exampleblock}{HEAD}\nBODY\n" ++
  "\\end{exampleblock}\n\\end{block}\n\\end{document}\n"

private def rowNames : Array String :=
  (List.range 16).toArray.map fun i =>
    "R" ++ (if i + 1 < 10 then "0" else "") ++ toString (i + 1) ++ "gyp"

/-- Invented combined counterexample: finite paragraph stretch acts both
while nested surfaces are open and after their final fragment has closed.
The following paragraph forces that closed fragment to be distributed. -/
public def closedFlushSource : String :=
  "\\documentclass{article}\n" ++
  "\\fonts{body=\"Source Serif Pro\",mono=\"Source Code Pro\",math=\"Fira Math\"}\n" ++
  "\\output{formats=pdf}\n" ++
  "\\page{width=220pt,height=128pt,hmargin=10pt,vmargin=6pt,fontsize=10pt}\n" ++
  "\\palette{fg=#101010,bg=#FFFFFF,blockbodybg=#DDEEFF,examplebodybg=#F2D3B2," ++
    "blocktitlebg=#204060,exampletitlebg=#704020}\n" ++
  "\\flushbottom\n\\setlength{\\parskip}{4pt plus 4pt}\n" ++
  "\\begin{document}\nPROLOGUE\n\\begin{block}{OUTER}\n\\begin{exampleblock}{INNER}\n" ++
  String.join (rowNames.toList.map (· ++ "\\par\n")) ++
  "\\end{exampleblock}\n\\end{block}\nEPILOGUE\n\\end{document}\n"

/-- Zero paragraph skip exposes the rule-neighbour path after a filled
region closes. The nested variant closes both regions before the rule, so
the outer surface's accumulated padding must remain reserved. -/
public def closedRuleSource (nested : Bool) : String :=
  "\\documentclass{article}\n" ++
  "\\fonts{body=\"Source Serif Pro\",mono=\"Source Code Pro\",math=\"Fira Math\"}\n" ++
  "\\output{formats=pdf}\n" ++
  "\\page{width=220pt,height=200pt,hmargin=10pt,vmargin=10pt,fontsize=10pt}\n" ++
  "\\palette{fg=#101010,bg=#FFFFFF,blockbodybg=#DDEEFF,examplebodybg=#F2D3B2}\n" ++
  "\\setlength{\\parskip}{0pt}\n\\setlength{\\parindent}{0pt}\n" ++
  "\\begin{document}\n\\begin{block}{}\n" ++
  (if nested then "\\begin{exampleblock}{}\n" else "") ++
  "BODY\n" ++
  (if nested then "\\end{exampleblock}\n" else "") ++
  "\\end{block}\n\\rule{20pt}{1pt}\\par\nAFTER\n\\end{document}\n"

/-- A plain peer must not erase a closed box's painted depth. `pos = "b"`
ties last baselines, `"t"` aligns first baselines, and `""` leaves position
unspecified. `boxFirst` swaps column order; `nested` adds one inset surface.
The rule spans both columns. -/
public def closedColumnRuleSource (nested boxFirst : Bool) (pos : String := "b") : String :=
  let openCol := "\\begin{minipage}" ++
    (if pos.isEmpty then "" else "[" ++ pos ++ "]") ++ "{90pt}"
  let peer := openCol ++ "PEER\\end{minipage}"
  let boxed := openCol ++ "\\begin{block}{}\n" ++
    (if nested then "\\begin{exampleblock}{}\n" else "") ++
    "BODY\n" ++
    (if nested then "\\end{exampleblock}\n" else "") ++
    "\\end{block}\\end{minipage}"
  let row := if boxFirst then boxed ++ "\\hfill\n" ++ peer
    else peer ++ "\\hfill\n" ++ boxed
  "\\documentclass{article}\n" ++
  "\\fonts{body=\"Source Serif Pro\",mono=\"Source Code Pro\",math=\"Fira Math\"}\n" ++
  "\\output{formats=pdf}\n" ++
  "\\page{width=220pt,height=200pt,hmargin=10pt,vmargin=10pt,fontsize=10pt}\n" ++
  "\\palette{fg=#101010,bg=#FFFFFF,blockbodybg=#DDEEFF,examplebodybg=#F2D3B2}\n" ++
  "\\setlength{\\parskip}{0pt}\n\\setlength{\\parindent}{0pt}\n" ++
  "\\begin{document}\n" ++ row ++
  "\\par\n\\rule{200pt}{1pt}\\par\nAFTER\n\\end{document}\n"

/-- An inherited rule band is not a column contribution. The following
rule exposes its clearance if an empty column enters the row's join.
Nonpainting rules and padded empty bodies are deliberate contributions. -/
public def emptyColumnSource (pos : String) (contents : Array String) : String :=
  let openCol := "\\begin{minipage}" ++
    (if pos.isEmpty then "" else "[" ++ pos ++ "]") ++ "{90pt}"
  let row := String.intercalate "\\hfill\n" (contents.toList.map fun content =>
    openCol ++ content ++ "\\end{minipage}")
  "\\documentclass{article}\n" ++
  "\\fonts{body=\"Source Serif Pro\",mono=\"Source Code Pro\",math=\"Fira Math\"}\n" ++
  "\\output{formats=pdf}\n" ++
  "\\page{width=220pt,height=200pt,hmargin=10pt,vmargin=10pt,fontsize=10pt}\n" ++
  "\\palette{fg=#101010,bg=#FFFFFF,blockbodybg=#DDEEFF}\n" ++
  "\\setlength{\\parskip}{0pt}\n\\setlength{\\parindent}{0pt}\n" ++
  "\\begin{document}\n\\rule{120pt}{1pt}\\par\n" ++ row ++
  "\\par\n\\rule{200pt}{1pt}\\par\nAFTER\n\\end{document}\n"

private def followingRules (out : Layout.Out) : Array Layout.LineOut :=
  out.pages.flatMap (·.lines) |>.filter fun line =>
    !line.furniture && line.segs.size == 1 && line.segs.all fun
      | .rule w thickness raise _ =>
        w == Dim.pt 200 && thickness == Dim.pt 1 && raise == 0
      | _ => false

/-- These assertions read final `Layout.Out` rectangles and text, not the
IR dump or the region fitter's intermediate measurements. Presence and
conservation prevent dropping a title, body, or surface from passing. -/
public def titleChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let (doc, diags) := Elab.run "block-region-title.tex" titleSource
  let geom := Layout.Geom.ofPage doc.page
  let out := Layout.run geom fonts none doc
  let fills := out.pages.flatMap (·.fills)
  let pad := Layout.titledPaddingOf fonts geom
  check ref "block region title: source and layout have no loss"
    ((diags ++ out.diags).all (·.severity == .note))
  check ref "block region title: feasible title and body survive on one page"
    (out.pages.size == 1 && bodyText out == #["HEAD", "BODY"])
  check ref "block region title: all three surfaces survive once"
    (#[outerColor, innerColor, blueBar].all fun color =>
      (fills.filter (·.color == color)).size == 1)
  check ref "block region title: complete painted extent stays inside the medium"
    ((fills.filter isSurface).all (insideMedium geom))
  check ref "block region title: parent pads both child title and body"
    (out.pages.all fun page => parentInsets page pad blueBar)
  check ref "block region title: child title joins its body"
    (out.pages.all fun page => titleJoins page innerColor blueBar)

/-- Distribution must retain painted reach after a region closes. The
body floor comes from the real shipment's resolved furniture geometry;
the rectangles being judged come from the public final layout entry.
No expected page count or font-specific coordinates prescribe a reflow. -/
public def closedFlushChecks (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit := do
  let (doc, diags) := Elab.run "block-region-closed-flush.tex" closedFlushSource
  let geom := Layout.Geom.ofPage doc.page
  let out := Layout.run geom fonts none doc
  let floor := (Layout.ship geom fonts none doc).geom.bodyBottom
  let pad := Layout.titledPaddingOf fonts geom
  let fills := out.pages.flatMap (·.fills)
  let surfacePages := out.pages.filter fun page => page.fills.any (·.color == outerColor)
  check ref "block region flush: source and layout have no loss"
    ((diags ++ out.diags).all (·.severity == .note))
  check ref "block region flush: all source lines survive once in order"
    (bodyText out == #["PROLOGUE", "OUTER", "INNER"] ++ rowNames ++ #["EPILOGUE"])
  check ref "block region flush: nested surfaces spill and titles appear once"
    (surfacePages.size > 1 && #[blueBar, brownBar].all fun color =>
      (fills.filter (·.color == color)).size == 1)
  check ref "block region flush: every row retains both enclosing surfaces"
    (rowNames.all fun text => out.pages.any fun page =>
      hasText page text &&
        #[outerColor, innerColor].all fun color =>
          (page.fills.filter (·.color == color)).size == 1 &&
            page.lines.any fun line => lineText line == text && page.fills.any fun fill =>
              fill.color == color && fill.x ≤ line.x &&
                line.x + line.setWidth ≤ fill.x + fill.w &&
                fill.y < line.y && line.y < fill.y + fill.h)
  check ref "block region flush: full child title and body retain parent padding"
    (out.pages.all fun page => parentInsets page pad brownBar)
  check ref "block region flush: both title-body seams join"
    (out.pages.all fun page =>
      titleJoins page outerColor blueBar && titleJoins page innerColor brownBar)
  check ref "block region flush: every painted fragment stays inside the medium"
    ((fills.filter isSurface).all (insideMedium geom))
  check ref "block region flush: every painted fragment respects the body floor"
    ((fills.filter isSurface).all fun fill => fill.y + fill.h ≤ floor)
  let closedPages := out.pages.filter (hasText · "R16gyp")
  check ref "block region flush: closed final fragment clears the footer baseline"
    (closedPages.size == 1 && closedPages.all fun page =>
      page.lines.any (·.furniture) &&
        #[outerColor, innerColor].all fun color => page.fills.any fun fill =>
          fill.color == color && page.lines.all fun line =>
            !line.furniture || fill.y + fill.h < line.y)
  check ref "block region flush: following paragraph is outside the closed paint"
    (out.pages.all fun page => page.lines.all fun line =>
      if !line.furniture && lineText line == "EPILOGUE" then
        (page.fills.filter isSurface).all fun fill => fill.y + fill.h < line.y
      else true)

/-- Closing a filled region reserves its complete painted bottom even
when the following paragraph contains only a rule. Read the rule's top
edge from its shipped segment; zero skip permits contact, never overlap.
Conservation and presence keep dropped ink or a spurious page break from
making this feasible same-page separation pass vacuously. -/
public def closedRuleChecks (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit := do
  for (name, nested) in #[("single", false), ("nested", true)] do
    let label := s!"block region rule/{name}"
    let (doc, diags) := Elab.run s!"block-region-rule-{name}.tex" (closedRuleSource nested)
    let geom := Layout.Geom.ofPage doc.page
    let out := Layout.run geom fonts none doc
    let fills := out.pages.flatMap (·.fills)
    let colors := if nested then #[outerColor, innerColor] else #[outerColor]
    let rules := out.pages.flatMap (·.lines) |>.filter fun line =>
      !line.furniture && Layout.ruleOnly line.segs
    check ref (label ++ ": source and layout have no loss")
      ((diags ++ out.diags).all (·.severity == .note))
    check ref (label ++ ": both words survive once in order on one page")
      (out.pages.size == 1 && bodyText out == #["BODY", "AFTER"])
    check ref (label ++ ": every closed surface survives once inside the medium")
      ((fills.filter isSurface).size == colors.size && colors.all fun color =>
        let surfaces := fills.filter (·.color == color)
        surfaces.size == 1 && surfaces.all (insideMedium geom))
    check ref (label ++ ": following rule survives once with its declared dimensions")
      (rules.size == 1 && rules.all fun line =>
        line.segs.size == 1 && line.segs.all fun
          | .rule w thickness raise _ =>
            w == Dim.pt 20 && thickness == Dim.pt 1 && raise == 0
          | _ => false)
    check ref (label ++ ": following rule starts below every closed surface")
      (out.pages.all fun page => page.lines.all fun line =>
        if !line.furniture && Layout.ruleOnly line.segs then
          line.segs.all fun
            | .rule _ thickness raise _ =>
              (page.fills.filter isSurface).all fun fill =>
                fill.y + fill.h ≤ line.y - raise - thickness
            | _ => false
        else true)

/-- The column join must retain every closed surface's physical bottom,
both with aligned baselines and with the default top placement. Swapping
column order guards against selecting either tied column alone. -/
public def closedColumnRuleChecks (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit := do
  for (posName, pos) in #[("last", "b"), ("first", "t"), ("top-default", "")] do
    for (nestName, nested) in #[("single", false), ("nested", true)] do
      for (orderName, boxFirst) in #[("peer-first", false), ("box-first", true)] do
        let label := s!"block region column rule/{posName}/{nestName}/{orderName}"
        let (doc, diags) := Elab.run
          s!"block-region-column-rule-{posName}-{nestName}-{orderName}.tex"
          (closedColumnRuleSource nested boxFirst pos)
        let geom := Layout.Geom.ofPage doc.page
        let out := Layout.run geom fonts none doc
        let fills := out.pages.flatMap (·.fills)
        let colors := if nested then #[outerColor, innerColor] else #[outerColor]
        let lines := out.pages.flatMap (·.lines) |>.filter (!·.furniture)
        let peers := lines.filter (fun line => lineText line == "PEER")
        let bodies := lines.filter (fun line => lineText line == "BODY")
        let rules := lines.filter (fun line => Layout.ruleOnly line.segs)
        let words := if boxFirst then #["BODY", "PEER", "AFTER"] else #["PEER", "BODY", "AFTER"]
        check ref (label ++ ": source and layout have no loss")
          ((diags ++ out.diags).all (·.severity == .note))
        check ref (label ++ ": all three words survive once in order on one page")
          (out.pages.size == 1 && bodyText out == words)
        -- A colour box aligns by its TeX reference, its bottom edge at `[b]`
        -- (a box of depth zero), as lualatex places it. At `[t]` a minipage
        -- opening on the block's `\medskipamount` aligns its top in TeX; the
        -- engine aligns the box's first band, so only order is held there.
        let pad := Layout.titledPaddingOf fonts geom
        let outer := fills.filter (·.color == outerColor)
        check ref (label ++ ": column order and requested alignment survive")
          (peers.size == 1 && bodies.size == 1 && peers.all fun peer =>
            bodies.all fun body =>
              (pos != "b" || outer.any (fun f => f.y + f.h == peer.y)) &&
              (if boxFirst then body.x < peer.x else peer.x < body.x))
        check ref (label ++ ": every closed surface survives once inside the medium")
          ((fills.filter isSurface).size == colors.size && colors.all fun color =>
            let surfaces := fills.filter (·.color == color)
            surfaces.size == 1 && surfaces.all (insideMedium geom))
        check ref (label ++ ": following rule spans every surface once at its declared size")
          (rules.size == 1 && rules.all fun line =>
            line.segs.size == 1 && line.segs.all fun
              | .rule w thickness raise _ =>
                w == Dim.pt 200 && thickness == Dim.pt 1 && raise == 0 &&
                  (fills.filter isSurface).all fun fill =>
                    line.x - pad ≤ fill.x && fill.x + fill.w ≤ line.x + w + pad
              | _ => false)
        check ref (label ++ ": following rule starts below every closed surface")
          (out.pages.all fun page => page.lines.all fun line =>
            if !line.furniture && Layout.ruleOnly line.segs then
              line.segs.all fun
                | .rule _ thickness raise _ =>
                  (page.fills.filter isSurface).all fun fill =>
                    fill.y + fill.h ≤ line.y - raise - thickness
                | _ => false
            else true)

/-- Empty peers leave the final rule at the position obtained by omitting
them, across every box alignment and both source orders. Surface and strut
controls prevent treating absence of glyphs as absence of a contribution.
An entirely empty row preserves the preceding page band. -/
public def emptyColumnChecks (ref : IO.Ref (List String))
    (fonts : Font.FontSet) : IO Unit := do
  for (posName, pos) in #[("top", ""), ("first", "t"), ("last", "b"), ("center", "c")] do
    let read (name : String) (contents : Array String) : IO Layout.Out := do
      let (doc, diags) := Elab.run s!"empty-column-{posName}-{name}.tex"
        (emptyColumnSource pos contents)
      let out := Layout.run (Layout.Geom.ofPage doc.page) fonts none doc
      check ref s!"empty column/{posName}/{name}: source and layout have no loss"
        ((diags ++ out.diags).all (·.severity == .note))
      pure out
    let omitted ← read "omitted" #[]
    let empty ← read "all-empty" #["", ""]
    check ref s!"empty column/{posName}: all-empty row preserves source and page"
      (omitted.pages.size == 1 && empty.pages.size == 1 &&
        bodyText omitted == #["AFTER"] && bodyText empty == #["AFTER"])
    check ref s!"empty column/{posName}: all-empty row preserves opening band"
      ((followingRules omitted).size == 1 && (followingRules empty).size == 1 &&
        (followingRules empty).map (·.y) == (followingRules omitted).map (·.y))
    for (kind, content) in #[("text", "PEER"),
        ("empty-fill", "\\begin{block}{}\\end{block}"),
        ("strut", "\\rule{0pt}{30pt}")] do
      let reference ← read (kind ++ "-only") #[content]
      let refRules := followingRules reference
      check ref s!"empty column/{posName}/{kind}: reference rule survives once"
        (refRules.size == 1)
      if kind == "empty-fill" then
        let surfaces := reference.pages.flatMap (·.fills) |>.filter (·.color == outerColor)
        check ref s!"empty column/{posName}: deliberately empty body retains padding"
          (surfaces.size == 1 && surfaces.all fun fill =>
            fill.h == Layout.titledPaddingOf fonts { fontSize := Dim.pt 10 })
      if kind == "strut" then
        check ref s!"empty column/{posName}: nonpainting strut reserves declared height"
          (reference.pages.any fun page => page.lines.any fun line =>
            !line.furniture && line.segs.isEmpty &&
              line.regionExtent == some (Dim.pt 30, 0))
      for (orderName, contents) in
          #[("empty-first", #["", content]), ("empty-last", #[content, ""])] do
        let label := s!"empty column/{posName}/{kind}/{orderName}"
        let out ← read (kind ++ "-" ++ orderName) contents
        check ref (label ++ ": all source words survive once on one page")
          (out.pages.size == 1 && reference.pages.size == 1 &&
            bodyText out == (if kind == "text" then #["PEER", "AFTER"] else #["AFTER"]))
        check ref (label ++ ": empty peer leaves following rule unchanged")
          ((followingRules out).size == 1 &&
            (followingRules out).map (·.y) == refRules.map (·.y))
        check ref (label ++ ": empty peer leaves content baselines unchanged")
          ((out.pages.flatMap (·.lines) |>.filter (!·.furniture) |>.map (·.y)) ==
            (reference.pages.flatMap (·.lines) |>.filter (!·.furniture) |>.map (·.y)))
        check ref (label ++ ": empty peer preserves complete surface extent")
          ((out.pages.flatMap (·.fills) |>.filter isSurface |>.map fun f => (f.y, f.h)) ==
            (reference.pages.flatMap (·.fills) |>.filter isSurface |>.map fun f => (f.y, f.h)))

/-- Bounded artifact guards for complete nested title fitting and finite
flush-bottom distribution over open and closed surface fragments, plus
closed-surface clearance before a rule-only paragraph, including column joins
and empty-column neutrality. -/
public def checks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  titleChecks ref fonts
  closedFlushChecks ref fonts
  closedRuleChecks ref fonts
  closedColumnRuleChecks ref fonts
  emptyColumnChecks ref fonts

end Tests.BlockRegionFit
