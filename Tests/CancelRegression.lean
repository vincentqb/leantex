import Tests.Support

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
      | .gap _ _ | .image _ _ _ => none
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

/-- The artifact realisation of `Math.cancelGeom_polys_between`: on the
shipped page no cancel polygon leaves its reserved box, and under
`makeroom` none crosses into the following atom. The clamp is load-bearing
— before it, a strike far wider than tall put an arrowhead and shaft vertex
above the box (`cancelHead 0 0 1000 100 20` reached `(919, 122)` over a
100sp-tall box). The polygon coordinates are read off `Layout.Out`, the
shipped page, not an IR dump. -/
def cancelBoxChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← mathSetOf oneFace
  -- Fail-first, now guarded: the raw geometry over a wide, short box. Every
  -- vertex of the head and of a drawn shaft lies inside the box.
  let inBox (p : Int × Int) : Bool := 0 ≤ p.1 && p.1 ≤ 1000 && 0 ≤ p.2 && p.2 ≤ 100
  t "cancel box: arrowhead stays in a wide short box"
    ((Math.cancelHead 0 0 1000 100 20).all inBox)
  t "cancel box: arrow shaft stays in a wide short box"
    ((Math.cancelShaft 0 0 1000 100 20).all inBox)
  let build (body : String) : Layout.Out :=
    layoutOf fonts (elabStr
      (dvDoc "\\usepackage{xcolor}\\usepackage[makeroom]{cancel}" body)).1
  let polyAbs (l : Layout.LineOut) : Array Dim.Sp :=
    (l.segs.flatMap fun s => match s with
      | .poly pts _ => pts
      | _ => #[]).map fun (px, _) => l.x + px
  let glyphX (l : Layout.LineOut) (g : String) : Option Dim.Sp :=
    (metricRunsAt l).findSome? fun (s, x) => if s == g then some x else none
  -- A plain strike reserves exactly its box under makeroom: every vertex is
  -- between the construct origin and the following atom, never past it.
  for cmd in ["cancel", "bcancel", "xcancel"] do
    let out := build s!"$\\{cmd}\{x}y$"
    match (bodyLines out).find? (·.segs.any (· matches .poly ..)) with
    | some l =>
      match glyphX l "𝑦" with
      | some yx =>
        let ps := polyAbs l
        t s!"cancel box: {cmd} strike stays in its box, clear of the neighbour"
          (!ps.isEmpty && ps.all fun ax => l.x ≤ ax && ax ≤ yx)
      | none => t s!"cancel box: {cmd} line carries the neighbour" false
    | none => t s!"cancel box: {cmd} ships a strike polygon" false
  -- `\cancelto`: the arrow's shaft and head sit left of the value it points
  -- at, clear of the value and of the following atom.
  let out := build "$\\cancelto{7}{x}y$"
  match (bodyLines out).find? (·.segs.any (· matches .poly ..)) with
  | some l =>
    match glyphX l "7", glyphX l "𝑦" with
    | some vx, some yx =>
      let ps := polyAbs l
      t "cancel box: cancelto arrow stays left of its value and the neighbour"
        (!ps.isEmpty && ps.all fun ax => l.x ≤ ax && ax ≤ vx && ax < yx)
    | _, _ => t "cancel box: cancelto ships its value and neighbour" false
  | none => t "cancel box: cancelto ships an arrow polygon" false
