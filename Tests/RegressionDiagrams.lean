module

public import Tests.RegressionSupport
public import Tests.CancelAlignment

public section

open LeanTex.Core

namespace Tests.RegressionDiagrams

private def routeNoteChecks (ref : IO.Ref (List String)) (a : Regression.Artifact) :
    IO Unit := do
  let t := fun name => check ref ("route-note: " ++ name)
  let chars := fun n => String.ofList (MathMl.nodeChars #[] n).toList
  let lines := bodyLines a.out
  let paths := a.out.pages.flatMap pageDraws
  let rects := paths.filterMap fun (g, _, _) => match g with
    | .rect x y w h => some (x, y, w, h)
    | _ => none
  let pictures := (elemNodesList (· == "svg") #[] a.body.toList).filter fun n =>
    nodeAttr "class" n == "picture"
  t "one native diagram with four station borders" (rects.size == 4)
  t "one typed SVG picture" (pictures.size == 1)
  for svg in pictures do
    t "picture preserves visible overflow" (nodeAttr "overflow" svg == "visible")
    let labels := elemNodesOne (· == "foreignObject") #[] svg
    t "all four labels retain their own carriers" (labels.size == 4)
    for (native, leaves, schema) in #[
        ("Seed′", "Seed′", "msup"), ("Stage𝑟", "Stage𝑟", "msub"),
        ("Ratio37", "Ratio37", "mfrac"), ("Root√𝑧", "Root𝑧", "msqrt")] do
      let selected := lines.filter fun l => lineText l false == native
      let carriers := labels.filter fun n => chars n == leaves
      t s!"{native} ships exactly once in layout and HTML"
        (selected.size == 1 && carriers.size == 1)
      for carrier in carriers do
        t s!"{native} keeps {schema} inside its text label"
          ((elemNodesOne (· == schema) #[] carrier).size == 1)
        t s!"{native} retains a zero-strut carrier and a visible label font"
          (match carrier with
          | .elem _ attrs #[.elem "div" _ #[.elem "math" outer
              #[.elem "mpadded" padded #[.elem "mrow" inner _]]]] =>
            HtmlDoc.attrOf? attrs "overflow" == some "visible" &&
            HtmlDoc.attrOf? outer "style" == some "font-size: 0; font-family: inherit" &&
            HtmlDoc.attrOf? padded "height" == some "0px" &&
            HtmlDoc.attrOf? padded "depth" == some "0px" &&
            HtmlDoc.attrOf? inner "style" == some s!"font-size: {(Dim.pt 10).toBpString}px"
          | _ => false)
      for line in selected do
        let one : Layout.Out := { pages := #[{ lines := #[line] }], diags := #[] }
        let glyphs := shippedBodyGlyphs one
        t s!"{native} preserves the leading text glyph"
          (glyphs[0]?.map (·.scalar) == native.toList.head?)
        match ShippedInk.targetInk a.fonts glyphs with
        | .error e => t s!"{native} has measurable native ink: {e}" false
        | .ok ink =>
          t s!"{native} fits its measured station border"
            ((rects.filter fun (x, y, w, h) =>
              x < ink.left && ink.right < x + w &&
                y < -ink.top && -ink.bottom < y + h).size == 1)
        if schema == "msup" || schema == "msub" then
          let script := if schema == "msup" then '′' else '𝑟'
          t s!"{native} has a smaller script on the correct side of its baseline"
            (glyphs[0]?.any fun first =>
              (glyphs.filter (·.scalar == script)).size == 1 &&
                glyphs.any fun g => g.scalar == script && g.size < first.size &&
                  (if schema == "msup" then g.y < first.y else first.y < g.y))
        if schema == "mfrac" then
          t "ratio numerator is above its denominator with a painted fraction bar"
            ((glyphs.find? (·.scalar == '3')).any fun n =>
              (glyphs.find? (·.scalar == '7')).any fun d =>
                n.y < d.y && (metricRuleSegs one).any fun (w, h, raise, _) =>
                  w > 0 && h > 0 && n.y < line.y - raise && line.y - raise < d.y)
        if schema == "msqrt" then
          t "root retains both the native radical glyph and its overbar"
            (glyphs.any (·.scalar == '√') &&
              (metricRuleSegs one).any fun (w, h, _, _) => w > 0 && h > 0)

    let pt? := fun s => do
      let (n, d) ← Decl.parseDecimal s
      return Dim.pt n / (d : Int)
    let svgPaths := elemNodesOne (· == "path") #[] svg
    let svgShafts := svgPaths.filterMap fun n => do
      if nodeAttr "fill" n != "none" then none else
        match (nodeAttr "d" n).splitOn " " |>.filter (· != "") with
        | ["M", x, y, "L", u, v] =>
          return (nodeAttr "stroke" n, (← pt? x), (← pt? y), (← pt? u), (← pt? v))
        | _ => none
    -- pgf's `to` head is two curves through the apex, so its apex, then its wings.
    let svgHeads := svgPaths.filterMap fun n => do
      if nodeAttr "stroke-linecap" n != "round" then none else
        match ((nodeAttr "d" n).replace "," " ").splitOn " " |>.filter (· != "") with
        | ["M", u, v, "C", _, _, _, _, x, y, "C", _, _, _, _, w, z] =>
          return (nodeAttr "stroke" n, (← pt? x), (← pt? y),
            (← pt? u), (← pt? v), (← pt? w), (← pt? z))
        | _ => none
    let nativeShafts := paths.filterMap fun (g, _, st) => do
      let stroke ← st
      let color ← paintColor? stroke.paint
      match g with
      | .path subs => match (subpathSegs subs).toList with
        | [.line x y u v] => some (color.css, x, y, u, v)
        | _ => none
      | _ => none
    let nativeHeads := paths.filterMap fun (g, fl, st) => do
      if !isTipDraw fl st then none else
      let color ← paintColor? (← st).paint
      match g with
      | .path #[{ start := (u, v), segs := #[.cubic _ _ (x, y), .cubic _ _ (w, z)], closed := false }] =>
        some (color.css, x, y, u, v, w, z)
      | _ => none
    let aims := #[
      ("#ff0000", (1 : Int), (0 : Int)), ("#0000ff", 0, -1),
      ("#00ff00", 1, 0), ("#00ff00", -1, 0), ("#000000", 0, 1)]
    for (backend, shafts, heads, slack) in
        #[("native", nativeShafts, nativeHeads, Dim.Length.quantum),
          ("HTML", svgShafts, svgHeads, 132 * Dim.Length.quantum)] do
      t s!"{backend} ships five shafts and five heads"
        (shafts.size == 5 && heads.size == 5)
      for (color, dx, dy) in aims do
        -- Each SVG point rounds on its own, so a level direction is level within that rounding.
        let points := fun (x y : Dim.Length) =>
          (if dx == 0 then x.abs ≤ slack else x * dx > 0) &&
          (if dy == 0 then y.abs ≤ slack else y * dy > 0)
        let matching := heads.filter fun (c, x, y, u, v, w, z) =>
          c == color && points (2 * x - u - w) (2 * y - v - z)
        t s!"{backend} {color} arrow points ({dx},{dy})" (matching.size == 1)
        for (_, x, y, u, v, w, z) in matching do
          -- Native coordinates round below one sp; SVG points below 0.001pt (66 sp) each.
          t s!"{backend} {color} head meets its shaft and has two wings"
            ((u - x) * (z - y) != (w - x) * (v - y) &&
              shafts.any fun (c, sx, sy, ex, ey) =>
                c == color && points (ex - sx) (ey - sy) &&
                min x (min u w) ≤ ex + slack && ex ≤ max x (max u w) + slack &&
                min y (min v z) ≤ ey + slack && ey ≤ max y (max v z) + slack)

  let reductions := lines.filter fun l => lineText l false == "𝑢+𝑥√𝑦0𝑔+𝑣"
  t "the complete reduction ships once" (reductions.size == 1)
  let cancels := (elemNodesList (· == "mpadded") #[] a.body.toList).filter fun n =>
    nodeAttr "data-cancel-metric" n == "measured"
  t "HTML cancellation receives measured placement" (cancels.size == 1)
  t "HTML never substitutes the unmeasured cancellation fallback"
    (!(elemAttrsList (fun _ => true) #[] a.body.toList).any fun (_, attrs) =>
      HtmlDoc.attrOf? attrs "data-cancel-metric" == some "unmeasured")
  for line in reductions do
    let one : Layout.Out := { pages := #[{ lines := #[line] }], diags := #[] }
    match CancelAlignment.measure a.fonts one "0𝑔" with
    | .error e => t ("cancellation is measurable: " ++ e) false
    | .ok w =>
      let polys := ShippedInk.polygonsAt line
      t "cancel target ink follows the forward diagonal" w.alongRay
      t "cancel target clears the tip by the math font gap" w.clearsTip
      t "cancel target clears the full shaft and head wings" (w.clearsMarks polys)
      let glyphs := shippedBodyGlyphs one
      t "cancellation reserves room between its unchanged neighbors"
        (match ShippedInk.targetInk a.fonts (glyphs.filter (·.scalar == '𝑢')),
            ShippedInk.targetInk a.fonts (glyphs.filter (·.scalar == '𝑣')) with
        | .ok left, .ok right =>
          left.right < w.ink.left && w.ink.right < right.left &&
            polys.all fun p => (ShippedInk.polygonHull p).any fun b =>
              left.right < b.left && b.right < right.left
        | _, _ => false)
      for cancel in cancels do
        t "measured HTML keeps the fraction, radical and multi-glyph target"
          (chars cancel == "𝑥𝑦0𝑔" &&
            (elemNodesOne (· == "mfrac") #[] cancel).size == 1 &&
            (elemNodesOne (· == "msqrt") #[] cancel).size == 1 &&
            (elemNodesOne (· == "polygon") #[] cancel).size == 2)
        let readPlacement : Option Bool := do
          let anchor ← glyphs.find? (·.scalar == '𝑢')
          let first ← w.glyphs[0]?
          let em := anchor.size.units
          let css := fun n key => cssProperty (nodeAttr "style" n) key
          let .elem _ _ #[_, value, overlay] := cancel | none
          let vx ← readOffset em value
          let vy ← readEm em (nodeAttr "voffset" value)
          let ox ← readOffset em overlay
          let oy ← readEm em (nodeAttr "voffset" overlay)
          let #[svg] := elemNodesOne (· == "svg") #[] overlay | none
          let [x0, y0, width, height] ←
            ((nodeAttr "viewBox" svg).splitOn " ").mapM String.toInt? | none
          let sw ← readEm em (← css svg "width")
          let sh ← readEm em (← css svg "height")
          if width ≤ 0 || height ≤ 0 || sw ≤ 0 || sh ≤ 0 then none else do
            let painted ← (elemNodesOne (· == "polygon") #[] svg).mapM fun poly =>
              (((nodeAttr "points" poly).splitOn " ").mapM fun (p : String) => do
                let [x, y] := p.splitOn "," | none
                let px ← x.toInt?
                let py ← y.toInt?
                return (Dim.Length.ofUnits (ox + (px - x0) * sw / width),
                  Dim.Length.ofUnits (oy + sh - (py - y0) * sh / height))).map List.toArray
            let .ok tip := CancelAlignment.arrowTip painted | none
            -- Em spellings, viewport scaling and integer division add at most six unit roundings.
            let k : Int := (em + 1999999) / 2000000 + 1
            let eps := 6 * k * Dim.Length.quantum
            return chars value == "0𝑔" &&
              ["width", "height", "depth"].all (fun k => nodeAttr k value == "0") &&
              nodeAttr "preserveAspectRatio" svg == "none" &&
              css svg "vertical-align" == some "baseline" &&
              (tip.1 - Dim.Length.ofUnits vx - (w.tip.1 - first.x)).abs ≤ eps &&
              (tip.2 - Dim.Length.ofUnits vy - (w.tip.2 + first.y)).abs ≤ eps
        t "HTML target and painted arrow retain their native relative placement"
          (readPlacement == some true)

private def fieldSheetChecks (ref : IO.Ref (List String)) (a : Regression.Artifact) :
    IO Unit := do
  let t := fun name => check ref ("field-sheet: " ++ name)
  let lines := bodyLines a.out
  let native := String.intercalate "\n" (lines.toList.map lineText)
  let text := nodeTextList "" a.body.toList
  for phrase in #["Sorting procedure", "wide tray", "spare envelope",
      "Sort the round pieces first.", "Count the square pieces second.",
      "shape reference", "Packing reminder", "Read the field guide",
      "After the insert and reminder, return every piece to the tray."] do
    t s!"included article content survives both artifacts: {phrase}"
      (hasStr native phrase && hasStr text phrase)
  let headings := elemNodesList (fun tag => tag == "h1" || tag == "h2") #[] a.body.toList
  t "Markdown heading joins the article after its title"
    (headings.map (nodeTextOne "") ==
      #["A field sheet for paper shapes", "Sorting procedure"])
  t "Markdown emphasis and list stay structural"
    ((elemNodesList (· == "strong") #[] a.body.toList).any (fun n =>
        nodeTextOne "" n == "wide tray") &&
      (elemNodesList (· == "em") #[] a.body.toList).any (fun n =>
        nodeTextOne "" n == "spare envelope") &&
      (elemNodesList (· == "ul") #[] a.body.toList).any fun n =>
        (elemNodesOne (· == "li") #[] n).map (nodeTextOne "") ==
          #["Sort the round pieces first.", "Count the square pieces second."])
  let contentLine := lines.find? (fun l => hasStr (lineText l) "wide tray")
  t "included bold and italic select the bundled style faces"
    (contentLine.any fun l =>
      let glyphs := shippedBodyGlyphs { pages := #[{ lines := #[l] }], diags := #[] }
      String.ofList ((glyphs.filter (·.face == 1)).toList.map (·.scalar)) == "widetray" &&
        String.ofList ((glyphs.filter (·.face == 2)).toList.map (·.scalar)) == "spareenvelope")
  let boxes := (elemNodesList (· == "section") #[] a.body.toList).filter fun n =>
    match n with
    | .elem _ attrs _ => HtmlDoc.attrOf? attrs "class" == some "tcolorbox"
    | _ => false
  t "tcolorbox remains one titled box" (boxes.size == 1)
  for box in boxes do
    t "box title remains bold and separate from its body"
      ((elemNodesOne (· == "header") #[] box).any fun n =>
        (elemNodesOne (· == "strong") #[] n).map (nodeTextOne "") ==
          #["Packing reminder"])
    t "box body keeps its small text and structured fraction over a radical"
      ((elemNodesOne (fun tag => tag == "span" || tag == "p") #[] box).any (fun n => match n with
        | .elem _ attrs _ => HtmlDoc.attrOf? attrs "class" == some "size-small" &&
            hasStr (nodeTextOne "" n) "Keep the folded pieces"
        | _ => false) &&
        (elemNodesOne (· == "mfrac") #[] box).any fun n =>
          String.ofList (MathMl.nodeChars #[] n).toList == "5𝑞" &&
            (elemNodesOne (· == "msqrt") #[] n).size == 1)
    t "underlined HTML link includes all three word spaces"
      ((elemNodesOne (· == "u") #[] box).any fun n =>
        match n with
        | .elem _ _ #[.elem "a" attrs #[.text label]] =>
          label == "Read the field guide" &&
            HtmlDoc.attrOf? attrs "href" == some "https://example.org/field-guide"
        | _ => false)
  t "Markdown link keeps its own destination"
    ((elemNodesList (· == "a") #[] a.body.toList).any fun n => match n with
      | .elem _ attrs _ => nodeTextOne "" n == "shape reference" &&
          HtmlDoc.attrOf? attrs "href" == some "https://example.org/shapes"
      | _ => false)
  let title := lines.find? (fun l => lineText l false == "Packingreminder")
  let linkLines := lines.filter (fun l => lineText l == "Read the field guide")
  t "native box title is bold, followed by a smaller linked phrase"
    (title.any fun heading =>
      let titleGlyphs := shippedBodyGlyphs
        { pages := #[{ lines := #[heading] }], diags := #[] }
      titleGlyphs[0]?.any fun first =>
        titleGlyphs.all (·.face == 1) && linkLines.size == 1 && linkLines.all fun l =>
          let glyphs := shippedBodyGlyphs { pages := #[{ lines := #[l] }], diags := #[] }
          heading.y < l.y && !glyphs.isEmpty && glyphs.all (·.size < first.size))
  let paints := lines.flatMap fun l => Id.run do
    let mut x := l.x
    let mut result := #[]
    for s in l.segs do
      if let .decoration .underline w h raise _ := s then
        result := result.push (x, l.y - raise - h, w, h)
      x := x + s.advance
    return result
  for l in linkLines do
    let glyphs := shippedBodyGlyphs { pages := #[{ lines := #[l] }], diags := #[] }
    t "native linked letters keep the destination"
      (!glyphs.isEmpty && glyphs.all (·.link == some "https://example.org/field-guide"))
    let gaps := Id.run do
      let mut x := l.x
      let mut result := #[]
      for s in l.segs do
        match s with
        | .gap w true | .decoratedGap w true _ =>
          if w > 0 && glyphs.any (·.x < x) && glyphs.any (·.x > x) then
            result := result.push (x, w)
        | _ => pure ()
        x := x + s.advance
      return result
    t "linked phrase supplies three interior spaces" (gaps.size == 3)
    for (x, w) in gaps do
      let mid := x + w / 2
      t "layout paints underline through each linked space"
        (paints.any fun (px, py, pw, ph) =>
          px ≤ mid && mid < px + pw && ph > 0 && l.y < py && py < l.y + l.size / 2)
      match readArtifact a.pdf with
      | .error e => t ("PDF underline is readable: " ++ e) false
      | .ok pages =>
        let px := a.geom.bleed + mid
        let py := a.geom.bleed + a.geom.pageH - l.y
        t "PDF paints underline through each linked space"
          (pages.any fun page => page.boxes.any fun b =>
            b.kind == "fill" && b.x0 ≤ px && px < b.x1 &&
              py - l.size / 2 < b.y0 && b.y1 < py)
  match PdfRead.objects a.pdf with
  | .error e => t ("PDF link annotations are readable: " ++ e) false
  | .ok es =>
    let mut uris := #[]
    for e in es.val do
      if PdfCensus.kindOf e.val == .page then
        if let .arr annots := PdfCensus.deref es.val ((e.val.get? "Annots").getD .null) then
          for raw in annots do
            let annot := PdfCensus.deref es.val raw
            if PdfCensus.kindOf annot == .annot "Link" then
              let action := PdfCensus.deref es.val ((annot.get? "A").getD .null)
              if let some uri := action.get? "URI" then uris := uris.push uri
    for url in #["https://example.org/shapes", "https://example.org/field-guide"] do
      t s!"PDF retains link destination {url}"
        (uris.contains (.str ("(" ++ url ++ ")").toUTF8))
  let skipped := a.diags.filter (·.kind == .W0103)
  let decoration := a.diags.filter (·.kind == .W0104)
  t "only the unsupported tcolorbox package declaration is allowlisted"
    (skipped.size == 1 && skipped.all fun d =>
      d.triggerText == some "\\usepackage" &&
        d.message == "package 'tcolorbox' is not supported; skipped")
  t "only the four requested box decoration keys are named, one each"
    (decoration.size == 4 && decoration.all fun d => d.triggerText == some "\\begin" &&
      ["enhanced", "arc", "colback", "colframe"].any fun k =>
        d.subject == some s!"param:\\begin\{fieldpanel}:{k}")

end Tests.RegressionDiagrams

def Tests.RegressionDiagrams.cases : Array Tests.Regression.Case := #[
  { path := "testdata/regression/diagrams/route-note.tex"
    check := Tests.RegressionDiagrams.routeNoteChecks },
  { path := "testdata/regression/diagrams/field-sheet.tex"
    warnings := #[.W0103, .W0104], check := Tests.RegressionDiagrams.fieldSheetChecks }]
