import Tests.Support
import Tests.CancelAlignment

open LeanTex.Core

mutual

private def superscriptTextOne (want : String) : Html.Node → Bool
  | .elem tag _ kids =>
    (tag == "msup" && (kids[1]?.map (nodeTextOne "")).getD "" == want) ||
      superscriptTextList want kids.toList
  | .text _ | .style _ | .script _ _ => false

private def superscriptTextList (want : String) : List Html.Node → Bool
  | [] => false
  | n :: ns => superscriptTextOne want n || superscriptTextList want ns

end

/-- A cancellation target reaches both shipped surfaces as a script, even
inside a colour declaration expanded from a macro in an alignment. The
operand and the neighbouring mathematics keep their glyphs and scripts:
neither the annotation nor its surrounding declaration can flatten a row. -/
def cancelReportChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let pre := "\\usepackage{amsmath,xcolor,cancel}\n" ++
    "\\newcommand{\\tint}[1]{{\\color{red}#1}}\n"
  let cases : List (String × String × Option String) := [
    ("inline", "$\\cancelto{7}{x} + y^2$", none),
    ("alignment", "\\begin{align*}a &= \\cancelto{7}{x} + y^2\\end{align*}", none),
    ("declared colour", "\\begin{align*}a &= {\\color{red}\\cancelto{7}{x}} + y^2\\end{align*}", some "red"),
    ("macro colour", "\\begin{align*}a &= \\tint{\\cancelto{7}{x}} + y^2\\end{align*}", some "red"),
    ("nested colour", "\\begin{align*}a &= {\\color{red}\\textcolor{blue}{\\cancelto{7}{x}}} + y^2\\end{align*}", some "blue")]
  for (label, body, colour) in cases do
    let (doc, ds) := elabStr (dvDoc pre body)
    let out := layoutOf fonts doc
    let segs := (bodyLines out).flatMap (·.segs)
    let runs := segs.filterMap fun s => match s with
      | .run _ _ _ _ glyphs _ _ _ raise _ _ =>
        some (String.ofList (glyphs.toList.map (·.2.1)), raise)
      | _ => none
    t s!"cancel report: {label} keeps the target above the operand"
      (runs.any fun (text, raise) => text == "7" && raise > 0)
    let text := String.join (runs.toList.map (·.1))
    t s!"cancel report: {label} preserves the operand and neighbouring script"
      (hasStr text "𝑥" && hasStr text "𝑦" &&
        runs.any fun (text, raise) => text == "2" && raise > 0)
    t s!"cancel report: {label} needs no math recovery"
      (!(ds.any fun d => d.code == "W0389" || d.code == "W0012"))
    let (_, tree, _) := HtmlDoc.emitTree { fonts := some fonts } doc
    t s!"cancel report: {label} gives HTML the target as a superscript"
      (superscriptTextList "7" tree.toList)
    t s!"cancel report: {label} gives HTML the neighbouring script"
      (superscriptTextList "2" tree.toList)
    let fg := (Ir.Design.ofDoc doc).fg
    let ink := (colour.bind doc.palette.resolve).getD fg
    t s!"cancel report: {label} colours the annotation and keeps the outer scope"
      (segs.all fun s => match s with
        | .run _ c _ _ glyphs _ _ _ _ _ _ =>
          glyphs.all fun (_, scalar, _) =>
            if scalar == '𝑥' || scalar == '7' then c == ink
            else if scalar == '𝑦' || scalar == '2' then c == fg else true
        | .poly _ c => c == ink
        | _ => true)

  -- A colour switch is not ink. Judge the colours the shipped glyphs,
  -- marks and rules use, including restored scopes and CancelColor's value.
  let colourCases : List (String × String × String × Bool × Bool) := [
    ("shadowed math colour", "", "${\\color{red}\\textcolor{blue}{\\cancelto{7}{x}}}$", false, false),
    ("shadowed formula colour", "", "{\\color{red}$\\textcolor{blue}{\\cancelto{7}{x}}$}", false, false),
    ("empty colour scope", "", "$\\color{blue}{\\color{red}\\,}\\cancelto{7}{x}$", false, false),
    ("restored neighbour", "", "$\\color{red}{\\color{blue}\\cancelto{7}{x}}y$", true, false),
    ("restored scripts", "", "$\\color{red}{\\color{blue}\\cancelto{7}{x}}^{2}_{3}$", true, false),
    ("inherited mark colour", "", "$\\color{red}\\cancelto{\\textcolor{blue}{7}}{\\textcolor{blue}{x}}$", true, true),
    ("CancelColor value", "\\renewcommand{\\CancelColor}{\\color{blue}}",
      "$\\color{red}\\cancelto{7}{\\textcolor{blue}{x}}$", false, false),
    ("scoped target colour", "\\renewcommand{\\CancelColor}{\\color{red}}",
      "$\\color{blue}\\cancelto{\\textcolor{blue}{7}}{x}$", true, true),
    ("fraction rule", "", "$\\color{red}\\frac{\\textcolor{blue}{\\cancelto{7}{x}}}{\\textcolor{blue}{y}}$", true, false),
    ("ruleless fraction", "", "$\\color{red}\\genfrac{}{}{0pt}{}{\\textcolor{blue}{\\cancelto{7}{x}}}{\\textcolor{blue}{y}}$", false, false),
    ("invisible delimiters", "", "$\\color{red}\\left.\\textcolor{blue}{\\cancelto{7}{x}}\\right.$", false, false)]
  for (label, hook, body, redInk, redMarks) in colourCases do
    let (doc, ds) := elabStr (dvDoc (pre ++ hook) body)
    let segs := (bodyLines (layoutOf fonts doc)).flatMap (·.segs)
    let red := doc.palette.resolve "red"
    let blue := doc.palette.resolve "blue"
    let inks := segs.filterMap fun s => match s with
      | .run _ c _ _ glyphs _ _ _ _ _ _ =>
        if glyphs.any (fun (_, ch, _) => !ch.isWhitespace) then some c else none
      | .poly pts c => if pts.isEmpty then none else some c
      | .rule w h _ c => if w > 0 && h > 0 then some c else none
      | .gap _ _ | .decoratedGap _ _ _ | .decoration _ _ _ _ _ | .image _ _ _ => none
    t s!"cancel contrast: {label} witnesses the colours actually shipped"
      (red.isSome && blue.isSome && inks.any (fun c => some c == blue) &&
        (inks.any (fun c => some c == red)) == redInk &&
        inks.all (fun c => some c == red || some c == blue))
    let glyphs := segs.flatMap fun s => match s with
      | .run _ c _ _ gs _ _ _ _ _ _ => gs.map fun (_, ch, _) => (ch, c)
      | _ => #[]
    t s!"cancel contrast: {label} preserves operand, target and mark scopes"
      (glyphs.any (fun (ch, c) => ch == '𝑥' && some c == blue) &&
        glyphs.any (fun (ch, c) => ch == '7' && some c == blue) &&
        glyphs.all (fun (ch, c) => if ch == '𝑥' || ch == '7' then some c == blue else true) &&
        segs.any (· matches .poly ..) &&
        segs.all (fun s => match s with
          | .poly _ c => some c == (if redMarks then red else blue)
          | _ => true))
    t s!"cancel contrast: {label} warns exactly when low-contrast ink ships"
      ((ds.any (·.code == "W0315")) == redInk &&
        !(ds.any fun d => d.code == "W0012" || d.code == "W0389"))

/-- The marks themselves reach the page as ink, reserve horizontal room,
and contribute their vertical bounds. Package options affect those
shipped marks and their value, without changing the operand's colour. -/
def cancelGeometryChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let build (opts hook body : String) :=
    let (doc, ds) := elabStr (dvDoc
      s!"\\usepackage\{xcolor}\\usepackage[{opts}]\{cancel}{hook}" body)
    (doc, layoutOf fonts doc, ds)
  for (cmd, count) in [("cancel", 1), ("bcancel", 1), ("xcancel", 2), ("cancelto{7}", 2)] do
    let (_, out, ds) := build "" "" s!"$\\{cmd}\{x}$"
    let polys := (bodyLines out).flatMap fun l => l.segs.filterMap fun s => match s with
      | .poly pts _ => some pts
      | _ => none
    t s!"cancel geometry: {cmd} ships its nonzero marks"
      (polys.size == count && polys.all fun pts =>
        match pts[0]?, pts[1]?, pts[2]? with
        | some a, some b, some c => (b.1 - a.1) * (c.2 - a.2) != (c.1 - a.1) * (b.2 - a.2)
        | _, _, _ => false)
    t s!"cancel geometry: {cmd} needs no recovery" (!ds.any (·.code == "W0012"))
  let nextX (opts cmd : String) : Option Dim.Sp :=
    let (_, out, _) := build opts "" s!"$\\{cmd}\{x}y$"
    ((bodyLines out).flatMap metricRunsAt).findSome? fun (s, x) =>
      if s == "𝑦" then some x else none
  -- cancel.sty defaults to \hidewidth; only makeroom selects \hfil.
  for cmd in ["cancel", "bcancel", "xcancel", "cancelto{7}"] do
    t s!"cancel geometry: {cmd} defaults to overlap"
      (match nextX "" cmd, nextX "overlap" cmd with
        | some defaultX, some overlap => defaultX == overlap
        | _, _ => false)
  t "cancel geometry: makeroom holds the annotation before the next atom"
    (match nextX "makeroom" "cancelto{7}", nextX "overlap" "cancelto{7}" with
      | some room, some overlap => room > overlap
      | _, _ => false)
  let (doc, out, _) := build "" "\\renewcommand{\\CancelColor}{\\color{blue}}"
    "$\\cancelto{7}{x}+y$"
  let blue := doc.palette.resolve "blue"
  let segs := (bodyLines out).flatMap (·.segs)
  t "cancel geometry: CancelColor paints every mark and the value"
    (blue.isSome && segs.any (· matches .poly ..) &&
      segs.all fun s => match s with
        | .poly _ c => some c == blue
        | .run _ c _ _ glyphs _ _ _ _ _ _ =>
          glyphs.all fun (_, scalar, _) =>
            if scalar == '7' then some c == blue
            else if scalar == '𝑥' || scalar == '𝑦' then c == (Ir.Design.ofDoc doc).fg else true
        | _ => true)
  let box := Layout.lineExtent fonts 1000 0 0 0 1000 1000
    #[.poly #[(0, -300), (100, 900), (200, 0)] (Ir.Design.ofDoc doc).fg]
  t "cancel geometry: polygon bounds enter the shipped line's vertical extent"
    (box.above == 900 && box.below == 300 && box.inkAbove == 900 && box.inkBelow == 300)

/-- Ordinary strikes stay inside the control band's corner-to-corner box;
arrows stay inside the full `Math.cancelEnvelope`, including perpendicular
wings beyond that box. The control is a shipped `Layout.Out` band, and the
following glyph supplies the actual style's font rule. Zero-area operands,
all four math sizes, both room modes and both rule weights share the same
judge, which rejects a vertex escaping any one edge or a missing mark.
`Math.cancelGeom_envelope_between` supplies the universal reservation bound.
Clearance compares absolute positions after accumulating segment advances;
`CancelAlignment.checks` independently holds the target to its forward ray
and resolved font gap. -/
def cancelBoxChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let polygonsAt := ShippedInk.polygonPens
  let polygons (l : Layout.LineOut) := (polygonsAt l).map (·.2)
  let glyphX (l : Layout.LineOut) (g : String) : Option Dim.Sp :=
    (metricRunsAt l).findSome? fun (s, x) => if s == g then some x else none
  let glyphsAt (l : Layout.LineOut) :=
    shippedBodyGlyphs { pages := #[{ lines := #[l] }], diags := #[] }
  let targetGlyphs (l : Layout.LineOut) := (glyphsAt l).filter (·.scalar == '7')
  let inside (bounds : ShippedInk.InkBounds)
      (polys : Array (Array (Dim.Sp × Dim.Sp))) : Bool :=
    !polys.isEmpty && polys.all fun pts =>
      (ShippedInk.polygonHull pts).any fun mark =>
        bounds.left ≤ mark.left && mark.right ≤ bounds.right &&
          bounds.bottom ≤ mark.bottom && mark.top ≤ bounds.top
  -- Outline hulls conservatively enclose ink. Require a positive gap on
  -- either axis against every mark; touching hulls do not count as clear.
  let clearsInk (ink : ShippedInk.InkBounds)
      (placed : Array (Array (Dim.Sp × Dim.Sp))) : Bool :=
    !placed.isEmpty && placed.all fun pts =>
      (ShippedInk.polygonHull pts).any fun mark =>
        mark.right < ink.left || ink.right < mark.left ||
          mark.top < ink.bottom || ink.top < mark.bottom
  let arrowClearsTarget (l : Layout.LineOut) : Bool :=
    (targetGlyphs l).size == 1 &&
      match ShippedInk.targetInk fonts (targetGlyphs l) with
      | .ok ink => clearsInk ink (ShippedInk.polygonsAt l)
      | .error _ => false
  -- Compensated kerns preserve every other pen and the logical advance.
  -- Increasing the run's raise moves its ink upward in the hull coordinates.
  let moveTarget (l : Layout.LineOut) (dx dy : Dim.Sp) : Layout.LineOut :=
    { l with segs := l.segs.flatMap fun seg => match seg with
      | .run face color link w glyphs size leading underline raise ground attr =>
        if String.ofList (glyphs.toList.map (·.2.1)) == "7" then
          #[.gap dx false,
            .run face color link w glyphs size leading underline (raise + dy) ground attr,
            .gap (-dx) false]
        else #[seg]
      | _ => #[seg] }
  let shapes := [("square", "x"), ("wide", "abcdefabcdef"), ("tall", "\\int"),
    ("fraction", "\\frac{x}{\\frac{z}{w}}"), ("empty", "")]
  let sizes := [("text", "$", "$"), ("display", "\\[", "\\]"),
    ("script", "$z^{", "}$"), ("scriptscript", "$z^{z^{", "}}$")]
  for (shape, struck) in shapes do
    for (size, before, after) in sizes do
      for opts in ["makeroom", "makeroom,thicklines", "overlap", "overlap,thicklines"] do
        let build (cmd : String) :=
          let (doc, ds) := elabStr (dvDoc s!"\\usepackage[{opts}]\{cancel}"
            s!"{before}\\{cmd}\{{struck}}y{after}")
          (bodyLines (layoutOf fonts doc), ds)
        let label := s!"{shape}/{size}/{opts}"
        let (control, _) := build "cancel"
        let some controlLine := control[0]? |
          t s!"cancel box: {label} ships the control line" false
          continue
        let some band := (polygons controlLine)[0]? |
          t s!"cancel box: {label} ships the control band" false
          continue
        let #[style] := (glyphsAt controlLine).filter (·.scalar == '𝑦') |
          t s!"cancel box: {label} ships one style witness" false
          continue
        let some font := fonts.fonts[style.face]? |
          t s!"cancel box: {label} resolves the style face" false
          continue
        let some math := font.math |
          t s!"cancel box: {label} has the font's MATH constants" false
          continue
        let rule := math.overbarRuleThickness * style.size / (font.unitsPerEm : Int) *
          (if hasStr opts "thicklines" then 2 else 1)
        t s!"cancel box: {label} has a positive font rule"
          (font.unitsPerEm > 0 && rule > 0)
        let some first := band[0]? |
          t s!"cancel box: {label} control band has vertices" false
          continue
        let (x0, y0, x1, y1) := band.foldl
          (fun (x0, y0, x1, y1) (x, y) => (min x0 x, min y0 y, max x1 x, max y1 y))
          (first.1, first.2, first.1, first.2)
        for cmd in ["cancel", "bcancel", "xcancel", "cancelto{7}"] do
          let (lines, ds) := build cmd
          t s!"cancel box: {label}/{cmd} sets one line without recovery"
            (lines.size == 1 && !ds.any (fun d => d.code == "W0012" || d.code == "W0389"))
          let some line := lines[0]? | continue
          let placed := polygonsAt line
          let polys := placed.map (·.2)
          let points := polys.flatten
          let (left, bottom, right, top) := if cmd == "cancelto{7}" then
              Math.cancelEnvelope x0 y0 x1 y1 rule
            else (x0, y0, x1, y1)
          let bounds : ShippedInk.InkBounds := { left, bottom, right, top }
          t s!"cancel box: {label}/{cmd} ships every mark inside both axes"
            (inside bounds polys)
          -- Mutate actual emitted polygons against the fixed expected box.
          -- One sp is the coordinate grid, not a perceptual tolerance.
          for (edge, escaped) in [("left", (left - 1, bottom)),
              ("right", (right + 1, bottom)), ("bottom", (left, bottom - 1)),
              ("top", (left, top + 1))] do
            let mutant := polys.mapIdx fun n pts =>
              if n == 0 then pts.mapIdx (fun i p => if i == 0 then escaped else p)
              else pts
            t s!"cancel box: {label}/{cmd} rejects escape through {edge}"
              (!inside bounds mutant)
          t s!"cancel box: {label}/{cmd} rejects missing marks"
            (!inside bounds #[] && !inside bounds (polys.push #[]))
          t s!"cancel box: {label}/{cmd} keeps its marks and diagonal corners"
            (if cmd == "cancelto{7}" then
              (polys.size == 1 || polys.size == 2) && points.contains (x1, y1)
            else if cmd == "xcancel" then
              polys.size == 2 && points.contains (x0, y0) && points.contains (x1, y1) &&
                points.contains (x0, y1) && points.contains (x1, y0)
            else
              polys.size == 1 && points.contains (x0, if cmd == "cancel" then y0 else y1) &&
                points.contains (x1, if cmd == "cancel" then y1 else y0))
          if cmd == "cancelto{7}" then
            t s!"cancel box: {label} arrow clears its target"
              (arrowClearsTarget line)
          if hasStr opts "makeroom" then
            t s!"cancel box: {label}/{cmd} holds every mark before the next atom"
              (match glyphX line "𝑦" with
                | some yx => placed.all fun (pen, pts) =>
                    pts.all fun (x, _) => line.x ≤ pen + x && pen + x ≤ yx
                | none => false)

  -- The operand still inks x after negative kerns make its advance negative.
  -- Nonempty vertices alone do not witness the filled arrowhead's ink.
  let area2 (pts : Array (Dim.Sp × Dim.Sp)) : Int :=
    pts.zipIdx.foldl (fun acc (p, n) =>
      let q := pts[(n + 1) % pts.size]!
      acc + p.1 * q.2 - p.2 * q.1) 0
  for (size, before, after) in sizes do
    for opts in ["makeroom", "makeroom,thicklines", "overlap", "overlap,thicklines"] do
      let label := s!"negative advance/{size}/{opts}"
      let (doc, ds) := elabStr (dvDoc s!"\\usepackage[{opts}]\{cancel}"
        s!"{before}\\cancelto\{7}\{x\\!\\!\\!\\!\\!\\!}y{after}")
      let lines := bodyLines (layoutOf fonts doc)
      t s!"cancel box: {label} sets one line without recovery"
        (lines.size == 1 && !ds.any (fun d => d.code == "W0012" || d.code == "W0389"))
      let some line := lines[0]? | continue
      t s!"cancel box: {label} preserves the operand and target"
        ((glyphX line "𝑥").isSome && (glyphX line "7").isSome)
      t s!"cancel box: {label} ships a nonzero filled arrowhead"
        ((polygons line).back?.any fun pts => area2 pts != 0)

  -- Move a decoded contour vertex strictly inside the actual arrowhead.
  -- A single nonzero polygon outlines this fixture's 7: an interior head
  -- neighbourhood around its contour vertex contains painted glyph ink,
  -- unlike a hull-centre overlap which could sit in a glyph's empty region.
  -- Two carrier glyphs expose a forgotten polygon pen even for a broad,
  -- thick arrowhead; their actual advances determine the displacement.
  for (shape, struck) in [("square", "x"), ("wide", "abcdefabcdef"),
      ("steep", "\\frac{x}{\\frac{z}{w}}")] do
    for opts in ["makeroom", "makeroom,thicklines", "overlap", "overlap,thicklines"] do
      let label := s!"clearance adversary/{shape}/{opts}"
      let (doc, ds) := elabStr (dvDoc s!"\\usepackage[{opts}]\{cancel}"
        s!"$zz^\{\\cancelto\{7}\{{struck}}y}$")
      let lines := bodyLines (layoutOf fonts doc)
      t s!"cancel box: {label} sets one line without recovery"
        (lines.size == 1 && !ds.any (fun d => d.code == "W0012" || d.code == "W0389"))
      let some line := lines[0]? | continue
      let #[g] := targetGlyphs line |
        t s!"cancel box: {label} ships one target glyph" false
        continue
      let .ok ink := ShippedInk.targetInk fonts #[g] |
        t s!"cancel box: {label} has decoded target ink" false
        continue
      let some font := fonts.fonts[g.face]? | continue
      let some cmds := font.inkSrc.get.cmdsAt g.glyph |
        t s!"cancel box: {label} decodes its contour" false
        continue
      let some (Ink.Cmd.move gx gy) := cmds[0]? |
        t s!"cancel box: {label} starts at a contour vertex" false
        continue
      let outline := cmds.flatMap ShippedInk.outlinePoints
      t s!"cancel box: {label} witnesses a single painted polygon"
        (font.unitsPerEm > 0 && cmds.size ≥ 3 && area2 outline != 0 &&
          (cmds.extract 1 cmds.size).all (fun cmd => match cmd with
            | .line _ _ => true
            | _ => false))
      let placed := ShippedInk.polygonsAt line
      let #[head] := placed.filter (·.size == 3) |
        t s!"cancel box: {label} ships one triangular head" false
        continue
      let some headInk := ShippedInk.polygonHull head | continue
      let (cx, cy) := head.foldl (fun (x, y) p => (x + p.1, y + p.2)) (0, 0)
      let inside := (cx / 3, cy / 3)
      let sides : Array Int := head.zipIdx.map fun (p, i) =>
        let q := head[(i + 1) % head.size]!
        (q.1 - p.1) * (inside.2 - p.2) - (q.2 - p.2) * (inside.1 - p.1)
      t s!"cancel box: {label} chooses strict head interior"
        (sides.all (· > 0) || sides.all (· < 0))
      let dx := inside.1 - (g.x + gx * g.size / (font.unitsPerEm : Int))
      let dy := inside.2 - (-g.y + gy * g.size / (font.unitsPerEm : Int))
      let moved := moveTarget line dx dy
      t s!"cancel box: {label} moves only target ink in both axes"
        (dx != 0 && dy != 0 &&
          targetGlyphs moved == #[{ g with x := g.x + dx, y := g.y - dy }] &&
          ShippedInk.targetInk fonts (targetGlyphs moved) == .ok (ink.shift dx dy) &&
          ShippedInk.polygonsAt moved == placed &&
          (glyphsAt moved).filter (·.scalar != '7') == (glyphsAt line).filter (·.scalar != '7'))
      let wrongOrigin := (polygons line).map fun pts =>
        pts.map fun (x, y) => (line.x + x, y - line.y)
      t s!"cancel box: {label} distinguishes polygon pen from line origin"
        ((polygonsAt line).any (fun (pen, _) => pen > line.x) &&
          clearsInk (ink.shift dx dy) wrongOrigin)
      t s!"cancel box: {label} accepts clear ink and rejects painted overlap"
        (arrowClearsTarget line && !arrowClearsTarget moved)

      -- A vertically clear target need not clear the arrow horizontally.
      -- The gap comes from the actual target face; zero gap must fail.
      let gap := font.math.map (fun m =>
        m.overbarVerticalGap * g.size / (font.unitsPerEm : Int)) |>.getD 0
      let centredX := (headInk.left + headInk.right - ink.left - ink.right) / 2
      let touching := moveTarget line centredX (headInk.top - ink.bottom)
      let above := moveTarget line centredX (headInk.top + gap - ink.bottom)
      t s!"cancel box: {label} accepts positive vertical clearance with horizontal overlap"
        (gap > 0 && arrowClearsTarget above &&
          ink.left + centredX < headInk.right && headInk.left < ink.right + centredX)
      t s!"cancel box: {label} rejects touching ink hulls"
        (!arrowClearsTarget touching)
