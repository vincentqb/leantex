module

public import Tests.TikzCoverage

public section

open LeanTex.Core LeanTex.Cli Tests.TikzCoverage

/-- A picture's stroked paths as segment lists in layout coordinates. -/
def strokedSegs (oneFace : Font.FontSet) (src : String) : Array (Array Ir.Pic.PathSeg) :=
  (drawsOf oneFace src).filterMap fun (g, _, st) => match g, st with
    | .path subs, some _ => some (subpathSegs subs)
    | _, _ => none

/-- Two coordinates within the rounding two separately rounded offsets can
differ by. -/
def near2 (a b : Dim.Sp) : Bool := decide (a - b ≤ 2 ∧ b - a ≤ 2)

/-- **A path's long tail draws what TikZ's path keys say.** The invariant
whose absence sent a picture to the boundary for one key: `rounded
corners` turns every corner with pgf's curve (`\pgfprocess@@specialround`:
the sides stop `r` short, the controls 0.5522847 of the way in); a scope
transforms the coordinates its statements spell — shift, scale and rotate
composed in the order written — and sets keys for them, both ending with
the scope; `arc` continues the path along an ellipse; `shorten` stops the
path short of its ends, its tip where it stops; and the opacity keys set
the paints' own alphas. Read off `Layout.Out` and the typed SVG, each
against its explicit spelling or pgf's own arithmetic. Invented content. -/
def tikzLongTailChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- Rounded corners: the corner is a curve, the sides stop r short of it.
  let r := Dim.mm 2
  let corner := picDoc "" "\\draw[rounded corners=2mm] (0,0) -- (2,0) -- (2,1);"
  t "rounded corners: no loss is named" (lossesOf corner).isEmpty
  t "rounded corners: a corner is a line, a curve and a line, the curve r from the corner"
    (match (strokedSegs oneFace corner).toList with
     | [segs] => match segs.toList with
       | [.line x0 _ x1 _, .cubic cx0 cy0 _ _ _ _ cx1 cy1, .line _ _ _ y3] =>
         -- The corner stands 2 cm right of the start; y grows downward.
         let cornerX := x0 + Dim.mm 20
         near2 x1 (cornerX - r) && near2 cx0 (cornerX - r) && near2 cx1 cornerX &&
           near2 (cy0 - cy1) r && near2 (cy0 - y3) (Dim.mm 10)
       | _ => false
     | _ => false)
  let box := picDoc "" "\\draw[rounded corners] (0,0) rectangle (2,1);"
  t "rounded corners: a rectangle turns all four corners"
    ((lossesOf box).isEmpty && match (strokedSegs oneFace box).toList with
      | [segs] => (segs.filter fun s => s matches .cubic ..).size == 4
      | _ => false)
  -- Scopes.
  let inScope (opts body : String) := picDoc "" ("\\begin{scope}[" ++ opts ++ "]" ++ body ++
    "\\end{scope}\\draw (0,0) -- (0,0.5);")
  let plain (body : String) := picDoc "" (body ++ "\\draw (0,0) -- (0,0.5);")
  for (name, opts, body, explicit) in #[
      ("shift", "shift={(1,0)}", "\\draw (0,0) -- (1,0);", "\\draw (1,0) -- (2,0);"),
      ("xshift and yshift", "xshift=1cm, yshift=5mm", "\\draw (0,0) -- (1,0);",
        "\\draw (1,0.5) -- (2,0.5);"),
      ("scale", "scale=2", "\\draw (0,0) -- (1,1);", "\\draw (0,0) -- (2,2);"),
      ("rotate", "rotate=90", "\\draw (0,0) -- (1,0);", "\\draw (0,0) -- (0,1);"),
      ("composed in the order written", "shift={(1,0)}, rotate=90", "\\draw (0,0) -- (1,0);",
        "\\draw (1,0) -- (1,1);"),
      ("a node's point", "shift={(1,1)}", "\\node at (0,0) {A};", "\\node at (1,1) {A};"),
      ("a relative coordinate turns with it", "rotate=90", "\\draw (0,0) -- ++(1,0);",
        "\\draw (0,0) -- (0,1);")] do
    let w := inScope opts body
    let e := plain explicit
    t s!"scope: {name}: no loss is named" (lossesOf w).isEmpty
    t s!"scope: {name}: ships the explicit page" ((shownOf oneFace w).close (shownOf oneFace e))
  let grid : Ir.Color := { r := 42, g := 111, b := 78 }
  let styled := picDoc "" "\\begin{scope}[grid, thick]\\draw (0,0) -- (1,0);\\end{scope}\\draw (0,1) -- (1,1);"
  t "scope: its keys set its statements' strokes, and end with it"
    ((lossesOf styled).isEmpty && (shownOf oneFace styled).strokes ==
      #[(grid, Ir.Pic.thickWidth), (Ir.Color.black, Ir.Pic.thinWidth)])
  -- Arcs: from the current point along the circle, its end the next point.
  let arc := picDoc "" "\\draw (0,0) arc (0:90:1) -- (-1,2);"
  t "arc: no loss is named" (lossesOf arc).isEmpty
  t "arc: a quarter circle ends a radius up and a radius back, where the path goes on"
    (match (strokedSegs oneFace arc).toList with
     | [segs] => match segs.toList with
       | [.cubic x0 y0 _ _ _ _ x1 y1, .line lx ly _ _] =>
         near2 (x0 - x1) (Dim.mm 10) && near2 (y0 - y1) (Dim.mm 10) && lx == x1 && ly == y1
       | _ => false
     | _ => false)
  -- Shorten.
  for (name, written, explicit) in #[
      ("the end", "\\draw[shorten >=2mm] (0,0) -- (1,0);", "\\draw (0,0) -- (0.8,0);"),
      ("the start", "\\draw[shorten <=2mm] (0,0) -- (1,0);", "\\draw (0.2,0) -- (1,0);"),
      ("the end, its tip where it stops", "\\draw[->, shorten >=2mm] (0,0) -- (1,0);",
        "\\draw[->] (0,0) -- (0.8,0);")] do
    let w := picDoc "" written
    t s!"shorten: {name}: no loss is named" (lossesOf w).isEmpty
    t s!"shorten: {name}: ships the explicit page"
      ((shownOf oneFace w).close (shownOf oneFace (picDoc "" explicit)))
  -- Opacity: the paints' own alphas, on the page and in the typed SVG.
  let alphaOf (src : String) : Array (Option Nat × Option Nat) :=
    (drawsOf oneFace src).map fun (_, fl, st) =>
      (fl.map (·.alpha.val), st.map (·.alpha.val))
  let faded := picDoc "" "\\draw[opacity=0.5] (0,0) -- (1,0);"
  t "opacity: a path strokes at half alpha"
    ((lossesOf faded).isEmpty && alphaOf faded == #[(none, some 500)])
  let filled := picDoc "" "\\fill[fill opacity=0.3] (0,0) rectangle (1,1);"
  t "fill opacity: a key-bearing fill fills at its alpha"
    ((lossesOf filled).isEmpty && alphaOf filled == #[(some 300, none)])
  let drawn := picDoc "" "\\filldraw[fill=grid, draw opacity=0.25] (0,0) circle (1);"
  t "draw opacity: the stroke alone takes it"
    ((lossesOf drawn).isEmpty && alphaOf drawn == #[(some 1000, some 250)])
  t "opacity: the typed SVG states the alphas"
    (let doc := (elabStr faded).1
     doc.body.any fun b =>
       (attrValuesOf (· == "path") "stroke-opacity" (HtmlDoc.blockNode {} b)).any (· == "0.5"))
