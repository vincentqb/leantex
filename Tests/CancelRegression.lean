module

public import Tests.Support
public import Tests.CancelAlignment

public section

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

/-- A cancellation target reaches both artifacts as a script, even inside a macro-expanded colour
declaration in an alignment, and no annotation flattens a row. -/
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
    t s!"cancel script: {label} keeps the target above the operand"
      (runs.any fun (text, raise) => text == "7" && raise > 0)
    let text := String.join (runs.toList.map (·.1))
    t s!"cancel script: {label} preserves the operand and neighbouring script"
      (hasStr text "𝑥" && hasStr text "𝑦" &&
        runs.any fun (text, raise) => text == "2" && raise > 0)
    t s!"cancel script: {label} needs no math recovery"
      (!(ds.any fun d => d.code == "W0389" || d.code == "W0012"))
    let (_, tree, _) := HtmlDoc.emitTree { fonts := some fonts } doc
    t s!"cancel script: {label} gives HTML the target as a superscript"
      (superscriptTextList "7" tree.toList)
    t s!"cancel script: {label} gives HTML the neighbouring script"
      (superscriptTextList "2" tree.toList)
    let fg := (Ir.Design.ofDoc doc).fg
    let ink := (colour.bind doc.palette.resolve).getD fg
    t s!"cancel script: {label} colours the annotation and keeps the outer scope"
      (segs.all fun s => match s with
        | .run _ c _ _ glyphs _ _ _ _ _ _ =>
          glyphs.all fun (_, scalar, _) =>
            if scalar == '𝑥' || scalar == '7' then c == ink
            else if scalar == '𝑦' || scalar == '2' then c == fg else true
        | .poly _ c => c == ink
        | _ => true)

  -- A colour switch is not ink: the shipped glyphs', marks' and rules' colours are judged.
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
      | .rule w h _ c _ => if w > 0 && h > 0 then some c else none
      | .gap _ _ | .decoratedGap _ _ _ | .decoration _ _ _ _ _ _ | .image _ _ _ _ _ _ => none
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

/-- The marks reach the page as ink, reserve horizontal room and contribute their vertical bounds;
package options change the marks, not the operand's colour. -/
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
  let nextX (opts cmd : String) : Option Dim.Length :=
    let (_, out, _) := build opts "" s!"$\\{cmd}\{x}y$"
    ((bodyLines out).flatMap metricRunsAt).findSome? fun (s, x) =>
      if s == "𝑦" then some x else none
  -- cancel.sty defaults to `\hidewidth`; only makeroom selects `\hfil`.
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
  let q (n : Int) : Dim.Length := n * Dim.Length.quantum
  let box := Layout.lineExtent fonts (q 1000) 0 0 0 1000 (q 1000)
    #[.poly #[(0, q (-300)), (q 100, q 900), (q 200, 0)] (Ir.Design.ofDoc doc).fg]
  t "cancel geometry: polygon bounds enter the shipped line's vertical extent"
    (box.above == q 900 && box.below == q 300 && box.inkAbove == q 900 && box.inkBelow == q 300)

/-- Strikes and arrows ship at cancel.sty's slopes, over zero-area operands, all four math sizes,
both room modes and both rule weights. -/
def cancelBoxChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  let polygonsAt := ShippedInk.polygonPens
  let polygons (l : Layout.LineOut) := (polygonsAt l).map (·.2)
  let glyphX (l : Layout.LineOut) (g : String) : Option Dim.Length :=
    (metricRunsAt l).findSome? fun (s, x) => if s == g then some x else none
  let glyphsAt (l : Layout.LineOut) :=
    shippedBodyGlyphs { pages := #[{ lines := #[l] }], diags := #[] }
  let targetGlyphs (l : Layout.LineOut) := (glyphsAt l).filter (·.scalar == '7')
  -- Outline hulls enclose ink conservatively, so clearance needs a positive gap.
  let clearsInk (ink : ShippedInk.InkBounds)
      (placed : Array (Array (Dim.Length × Dim.Length))) : Bool :=
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
  let moveTarget (l : Layout.LineOut) (dx dy : Dim.Length) : Layout.LineOut :=
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
        for cmd in ["cancel", "bcancel", "xcancel", "cancelto{7}"] do
          let (lines, ds) := build cmd
          t s!"cancel box: {label}/{cmd} sets one line without recovery"
            (lines.size == 1 && !ds.any (fun d => d.code == "W0012" || d.code == "W0389"))
          let some line := lines[0]? | continue
          let placed := polygonsAt line
          let polys := placed.map (·.2)
          let slopes := if cmd == "cancelto{7}" then Math.cancelVectorSlopes
            else Math.cancelSlashSlopes
          -- A band's first edge runs along its centre line; the head's first vertex is the tip.
          let strokes := polys.filter (·.size == 4)
          t s!"cancel box: {label}/{cmd} ships cancel.sty's marks"
            (if cmd == "cancelto{7}" then
              (polys.size == 1 || polys.size == 2) && (polys.filter (·.size == 3)).size == 1
            else polys.size == (if cmd == "xcancel" then 2 else 1) && strokes.size == polys.size)
          t s!"cancel box: {label}/{cmd} strokes stand at cancel.sty's slopes"
            (strokes.all fun pts => match pts[0]?, pts[1]? with
              | some a, some b =>
                let dx := (b.1 - a.1).units
                let dy := (b.2 - a.2).units
                dx > 0 && dy != 0 && (cmd == "xcancel" || (cmd == "bcancel") == (dy < 0)) &&
                  slopes.any fun (run, rise) =>
                    (dx * (rise : Int) - dy.natAbs * (run : Int)).natAbs ≤ 64
              | _, _ => false)
          if cmd == "xcancel" then
            let rise (pts : Array (Dim.Length × Dim.Length)) : Dim.Length :=
              match pts[0]?, pts[1]? with
              | some a, some b => b.2 - a.2
              | _, _ => 0
            t s!"cancel box: {label} crosses a rising and a falling stroke"
              (strokes.any (rise · > 0) && strokes.any (rise · < 0))
          if cmd == "cancelto{7}" then
            t s!"cancel box: {label} arrow clears its target"
              (arrowClearsTarget line)
          if hasStr opts "makeroom" then
            -- A band's corner stands off its centre line, an arrowhead's barb up to half its back.
            let slack := if cmd == "cancelto{7}" then Math.cancelHeadHalf true
              else Math.cancelRule true
            t s!"cancel box: {label}/{cmd} holds every mark before the next atom"
              (match glyphX line "𝑦" with
                | some yx => placed.all fun (pen, pts) =>
                    pts.all fun (x, _) =>
                      line.x ≤ pen + x + Dim.Length.ofUnits slack &&
                        pen + x ≤ yx + Dim.Length.ofUnits slack
                | none => false)

  -- Nonempty vertices alone do not witness the filled arrowhead's ink.
  let areaInt (pts : Array (Int × Int)) : Int :=
    pts.zipIdx.foldl (fun acc (p, n) =>
      let q := pts[(n + 1) % pts.size]!
      acc + p.1 * q.2 - p.2 * q.1) 0
  let area2 (pts : Array (Dim.Length × Dim.Length)) : Int :=
    areaInt (pts.map fun (x, y) => (x.units, y.units))
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

  -- A head neighbourhood around a contour vertex holds glyph ink, unlike a hull-centre overlap.
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
        (font.unitsPerEm > 0 && cmds.size ≥ 3 && areaInt outline != 0 &&
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

      -- A vertically clear target need not clear the arrow horizontally; zero gap fails.
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
