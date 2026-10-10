module

public import Tests.TikzShapes

public section

open LeanTex.Core LeanTex.Cli Tests.TikzCoverage

/-- The head a one-segment arrow ships and the shaft it ends, in layout
coordinates: the shaft's two ends, then the head's geometry, fill and
stroke. -/
def arrowParts (oneFace : Font.FontSet) (src : String) :
    Option ((Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) × Gfx.Geom × Option Gfx.Fill × Option Gfx.Stroke) :=
  match (drawsOf oneFace src).toList with
  | [(.path shaft, none, some _), (head, fl, st)] =>
    match (subpathSegs shaft).toList with
    | [.line x0 y0 x1 y1] => some ((x0, y0, x1, y1), head, fl, st)
    | _ => none
  | _ => none

/-- **Every tip is its own declaration.** The invariant whose absence drew
every head as one straight-sided triangle: a tip is what pgf declares it to
be — the `->` shorthand's head is pgf's `to` (pgfcorearrows.code.tex, `<->
/.tip = {To}`), a stroked curve at 0.8 of the line width with round caps
whose apex and cap reach the path's end, or arrows.meta's Computer Modern
arrow where the document loads arrows.meta; `latex` is a filled shape with
curved sides, its apex on the end; `stealth` a filled dart with its notch at
the line's end; arrows.meta's `Latex` filled and stroked, its mitred apex
on the end. Each shaft stops where its tip's line end stands. Read off
`Layout.Out`, against pgf's own arithmetic; invented content. -/
def tikzTipChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let lw : Dim.Sp := Ir.Pic.thinWidth
  let a : Dim.Sp := Dim.pt 28 / 100 + lw * 3 / 10
  let near (x y : Dim.Sp) (tol : Nat := 3) : Bool := (x - y).natAbs ≤ tol
  let line := "(0,0) -- (1,0);"
  -- `->`: pgf's `to`.
  match arrowParts oneFace (picDoc "" ("\\draw[->] " ++ line)) with
  | some ((x0, _, x1, _), .path #[sub], none, some st) =>
    let tipEnd := Dim.pt 21 / 100 + lw * 625 / 1000
    let ends := x0 + Dim.mm 10
    t "to: the shorthand's head is stroked, round, at 0.8 of the line width, two curves"
      (st.cap == .round && st.join == .round && st.width == lw * 8 / 10 && !sub.closed &&
        sub.segs.size == 2)
    t "to: its apex and its round cap reach the path's end"
      (match (sub.segs[0]? : Option Gfx.Seg) with
       | some (.cubic _ _ (ax, _)) => near (ax + st.width / 2) ends
       | _ => false)
    t "to: the shaft stops at the head's origin, its tip end short of the end"
      (near x1 (ends - tipEnd))
  | _ => t "to: the shorthand ships a shaft and a stroked head" false
  -- `<-` is `->` on the side run the other way (`reversedTip_exact`, here
  -- through the whole statement reader): the same head at the same point,
  -- the shaft between the same two points, run backwards.
  for (tipSpec, fwdSpec) in [("<-", "->"), ("latex-", "-latex"), ("stealth-", "-stealth")] do
    match arrowParts oneFace (picDoc "" s!"\\draw[{tipSpec}] (0,0) -- (1,0.5);"),
        arrowParts oneFace (picDoc "" s!"\\draw[{fwdSpec}] (1,0.5) -- (0,0);") with
    | some ((a0, b0, a1, b1), h, f, s), some ((c0, d0, c1, d1), h', f', s') =>
      t s!"reversed tip: '{tipSpec}' draws the head '{fwdSpec}' draws on the side run backwards"
        (h == h' && f == f' && s == s' && a0 == c1 && b0 == d1 && a1 == c0 && b1 == d0)
    | _, _ => t s!"reversed tip: '{tipSpec}' and '{fwdSpec}' each ship a shaft and a head" false
  -- With arrows.meta loaded, the shorthand is its Computer Modern arrow.
  let metaDoc := picDoc "" ("\\draw[->] " ++ line) "\\usepackage{tikz}\n\\usetikzlibrary{arrows.meta}\n"
  t "Computer Modern Rightarrow: arrows.meta names no unknown command and no loss"
    ((elabStr metaDoc).2.all fun d => d.code != "W0301" && d.code != "W0334")
  match arrowParts oneFace metaDoc with
  | some ((x0, _, x1, _), .path #[sub], none, some st) =>
    let ends := x0 + Dim.mm 10
    t "Computer Modern Rightarrow: stroked at the line width, round, two curves"
      (st.cap == .round && st.width == lw && sub.segs.size == 2)
    t "Computer Modern Rightarrow: its apex half a line width short of the end, the shaft a line width"
      (match (sub.segs[0]? : Option Gfx.Seg) with
       | some (.cubic _ _ (ax, _)) => near ax (ends - lw / 2) && near x1 (ends - lw)
       | _ => false)
  | _ => t "Computer Modern Rightarrow: the shorthand ships a shaft and a stroked head" false
  -- tikz-cd loads arrows.meta itself (tikzlibrarycd.code.tex), so a document
  -- that loads the package, or its library, draws every `->` as one that
  -- names arrows.meta does.
  let metaArrow := arrowParts oneFace metaDoc
  for (how, pre) in [("the tikz-cd package", "\\usepackage{tikz-cd}\n"),
      ("the package with options", "\\usepackage[all]{tikz-cd}\n"),
      ("the cd library", "\\usepackage{tikz}\n\\usetikzlibrary{positioning, cd}\n")] do
    t s!"Computer Modern Rightarrow: {how} draws the shorthand as arrows.meta does"
      (metaArrow.isSome && arrowParts oneFace (picDoc "" ("\\draw[->] " ++ line) pre) == metaArrow)
  t "to: a library that loads no arrows.meta keeps pgf's own head"
    (arrowParts oneFace (picDoc "" ("\\draw[->] " ++ line) "\\usepackage{tikz}\n\\usetikzlibrary{calc}\n")
      == arrowParts oneFace (picDoc "" ("\\draw[->] " ++ line)) &&
      arrowParts oneFace (picDoc "" ("\\draw[->] " ++ line)) != metaArrow)
  -- `latex`: filled, curved sides, its apex on the end.
  match arrowParts oneFace (picDoc "" ("\\draw[-latex] " ++ line)) with
  | some ((x0, _, x1, _), .path #[sub], some _, none) =>
    let ends := x0 + Dim.mm 10
    t "latex: filled with curved sides, closed"
      (sub.closed && (sub.segs.filter (· matches .cubic ..)).size == 2)
    t "latex: its apex on the end, the shaft stopping nine units short"
      (near sub.start.1 ends && near x1 (ends - 9 * a))
  | _ => t "latex: the tip ships a shaft and a filled head" false
  -- `stealth`: a filled dart, its notch where the shaft stops.
  match arrowParts oneFace (picDoc "" ("\\draw[-stealth] " ++ line)) with
  | some ((x0, _, x1, _), .path #[sub], some _, none) =>
    let ends := x0 + Dim.mm 10
    t "stealth: a filled dart, its apex on the end, its notch at the shaft's end"
      (sub.closed && sub.segs.size == 3 && near sub.start.1 ends && near x1 (ends - 5 * a) &&
        match (sub.segs[1]? : Option Gfx.Seg) with
        | some (.line (nx, _)) => near nx x1
        | _ => false)
  | _ => t "stealth: the tip ships a shaft and a filled head" false
  -- arrows.meta's `Latex`: filled and stroked, its mitred apex on the end.
  match arrowParts oneFace (picDoc "" ("\\draw[-Latex] " ++ line)) with
  | some ((x0, _, _, _), .path #[sub], some _, some st) =>
    let len := Dim.pt 3 + lw * 45 / 10
    let wid := len * 75 / 100
    let alw := min lw (len / 5)
    let lwF : Float := (alw.toNat.toFloat) / 65536
    let ratio : Float := (len.toNat.toFloat) / (wid.toNat.toFloat)
    let front : Float := lwF * Float.sqrt (1 + 9 * ratio * ratio)
    let sp (x : Float) : Dim.Sp := (x * 65536).round.toInt64.toInt
    let ends := x0 + Dim.mm 10
    t "Latex: filled and stroked at its line width, mitred, curved"
      (st.join == .miter && st.width == alw && sub.closed &&
        (sub.segs.filter (· matches .cubic ..)).size == 2)
    t "Latex: its apex half the front miter short of the end"
      (near sub.start.1 (ends - sp (front / 2)) 4)
  | _ => t "Latex: the tip ships a shaft and a filled, stroked head" false
