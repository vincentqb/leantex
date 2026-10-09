module

public import Tests.PictureKeys

public section

open LeanTex.Core

namespace PictureLabelSpacing

structure Witness where
  ink : ShippedInk.InkBounds
  anchor : Dim.Sp × Dim.Sp
  tangent : Dim.Sp × Dim.Sp
  width : Dim.Sp
  size : Dim.Sp
  em : Dim.Sp
  ex : Dim.Sp
  text : String
  deriving Repr

/-- Read the label's outline hull and the path's midpoint and tangent from
the shipped page. The only text in these probes belongs to the label.
Page paths use downward y; the witness uses upward y throughout. -/
def pathLabelWitness (fonts : Font.FontSet) (src : String) : Except String Witness := do
  let (doc, ds) := elabMeasured fonts src
  if ds.any (fun d => d.code == "W0334" || d.severity == .error) then
    throw s!"picture option was refused: {ds.map (·.message)}"
  let out := layoutOf fonts doc
  let some page := out.pages[0]? | throw "no shipped page"
  let #[path] := page.paths | throw "expected one shipped path"
  let (anchor, tangent) ← match path.path with
    | .segs #[.line x y u v] => pure (((x + u) / 2, -(y + v) / 2), (u - x, y - v))
    | .segs #[.cubic x y a b c d u v] =>
      pure (((x + 3 * a + 3 * c + u) / 8, -(y + 3 * b + 3 * d + v) / 8),
        (-x - a + c + u, y + b - d - v))
    | .rect x y w h => pure ((x + w / 2, -(y + h / 2)), (w, h))
    | .segs _ | .circle .. | .tri .. => throw "expected one segment or rectangle"
  let glyphs := shippedBodyGlyphs out
  let some glyph := glyphs[0]? | throw "no shipped label"
  return { ink := ← ShippedInk.targetInk fonts glyphs
           anchor, tangent, width := (path.stroke.map (·.width)).getD 0
           size := glyph.size, em := doc.page.fontSize
           ex := ((Layout.labelMetric (Layout.Geom.ofPage doc.page) fonts) #[.text "x"] 1000).ex
           text := String.ofList (glyphs.toList.map (·.scalar)) }

def pathLabelSource (picOpts pathOpts labelOpts body endpoint : String)
    (operation : String := "--") : String :=
  picDoc "" s!"[{picOpts}]"
    (s!"\\draw[{pathOpts}] (0,0) {operation} node[{labelOpts}] " ++
      "{" ++ body ++ "} " ++ endpoint ++ ";")

/-- Vertical distance from the outside of a horizontal stroke to the
nearest outline of the whole label, including descenders and later lines. -/
def Witness.gap (w : Witness) (above : Bool) : Dim.Sp :=
  (if above then w.ink.bottom - w.anchor.2 else w.anchor.2 - w.ink.top) - w.width / 2

end PictureLabelSpacing

open PictureLabelSpacing in
/-- A font-relative default reads the surrounding dimension font; `font=`
and body switches change the text only. Explicit separation wins, a style name is its expansion,
and reversing either path direction or auto side reverses the attachment.
All assertions read shipped glyph outlines and strokes. Integer font
scaling, centre rounding and page translation contribute at most four sp;
the tolerance is arithmetic, not a perceptual tuning threshold. -/
def PictureLabelSpacing.checks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  for body in ["MAP", "gyp", "MAP\\\\gyp"] do
    for labelOpts in ["", "font=\\small", "font=\\Large"] do
      for stroke in ["thin", "semithick", "very thick"] do
        for (auto, endpoint, above) in
            [("auto", "(4,0)", true), ("auto,swap", "(4,0)", false),
             ("auto", "(-4,0)", false), ("auto=right", "(-4,0)", true)] do
          let src := pathLabelSource "" s!"{auto},{stroke}" labelOpts body endpoint
          match pathLabelWitness fonts src with
          | .error e => t s!"path-label witness: {e}" false
          | .ok w =>
            -- pgfmoduleshapes.code.tex: inner ysep=.3333em;
            -- outer ysep=.5\pgflinewidth. Subtracting the half stroke
            -- above leaves the declared inner clearance.
            let expected := w.em * 3333 / 10000
            t s!"whole label clears {auto}/{stroke}/{labelOpts}/{body}"
              ((w.gap above - expected).natAbs ≤ 4)
            t "label attachment preserves all source letters"
              (w.text == body.replace "\\\\" "")
  for (placement, dx, dy) in
      [("right", 1, 0), ("left", -1, 0), ("above", 0, 1), ("below", 0, -1),
       ("above right", 1, 1), ("above left", -1, 1),
       ("below right", 1, -1), ("below left", -1, -1)] do
    match pathLabelWitness fonts (pathLabelSource "" "" placement "MAP\\\\gyp" "(4,0)") with
    | .error e => t s!"explicit path-label placement: {e}" false
    | .ok w =>
      let gap := w.em * 3333 / 10000 + w.width / 2
      let gx := if dx > 0 then w.ink.left - w.anchor.1 else w.anchor.1 - w.ink.right
      let gy := if dy > 0 then w.ink.bottom - w.anchor.2 else w.anchor.2 - w.ink.top
      t s!"explicit {placement} clears every named side with the whole label"
        ((dx == 0 || gx + 4 ≥ gap) && (dy == 0 || (gy - gap).natAbs ≤ 4) &&
         w.text == "MAPgyp")
  for (opts, gap) in [("inner sep=0pt", Dim.pt 0), ("inner ysep=2pt", Dim.pt 2)] do
    for above in [true, false] do
      let placement := if above then "above" else "below"
      match pathLabelWitness fonts (pathLabelSource "" "" s!"{placement},{opts}" "MAP\\\\gyp" "(4,0)") with
      | .error e => t s!"explicit label separation: {e}" false
      | .ok w =>
        t "explicit separation moves the whole multiline box" ((w.gap above - gap).natAbs ≤ 4)
  let direct := pathLabelSource "" "auto" "inner sep=2pt,align=left" "MAP\\\\gyp" "(4,0)"
  let named := pathLabelSource "edge-text/.style={inner sep=2pt,align=left}" "auto"
    "edge-text" "MAP\\\\gyp" "(4,0)"
  t "a path-label style ships the same placement as its expanded keys"
    (match pathLabelWitness fonts direct, pathLabelWitness fonts named with
     | .ok a, .ok b => a.ink == b.ink && a.anchor == b.anchor && a.text == b.text
     | _, _ => false)
  -- In TikZ's auto algorithm a diagonal selects a corner: both axes
  -- clear the anchor. Cardinal-only placement misses one of these axes.
  for (endpoint, left, up) in
      [("(4,2)", true, true), ("(4,-2)", false, true),
       ("(-4,2)", true, false), ("(-4,-2)", false, false)] do
    match pathLabelWitness fonts (pathLabelSource "" "auto" "" "MAP" endpoint) with
    | .error e => t s!"diagonal label: {e}" false
    | .ok w =>
      let gap := w.em * 3333 / 10000 + w.width / 2
      let dx := if left then w.anchor.1 - w.ink.right else w.ink.left - w.anchor.1
      let dy := if up then w.ink.bottom - w.anchor.2 else w.anchor.2 - w.ink.top
      -- Horizontal glyph bearings can add room inside the logical width.
      t "a diagonal auto label clears the anchor in both coordinates"
        (dx + 4 ≥ gap && (dy - gap).natAbs ≤ 4)
  -- A cubic with a horizontal chord has a downward tangent at its middle.
  -- The local tangent selects the upper-right corner, not merely above.
  match pathLabelWitness fonts (pathLabelSource "" "auto" "" "MAP" "(4,0)" "to[out=100,in=0]") with
  | .error e => t s!"curved label: {e}" false
  | .ok w =>
    t "the curve probe has a downward midpoint tangent" (w.tangent.1 > 0 && w.tangent.2 < 0)
    let gap := w.em * 3333 / 10000 + w.width / 2
    t "a curved auto label attaches according to its local tangent"
      (w.ink.left - w.anchor.1 + 4 ≥ gap &&
       (w.ink.bottom - w.anchor.2 - gap).natAbs ≤ 4)
  -- PGF's dimension-font probe: either ordering of `font=` and a length,
  -- and a switch inside the text, retain the surrounding em and ex.
  for (opts, body, unit) in
      [("", "\\Large MAP", ""),
       ("font=\\Large,inner sep=1em", "MAP", "em"),
       ("inner sep=1em,font=\\Large", "MAP", "em"),
       ("inner sep=1em", "\\Large MAP", "em"),
       ("font=\\Large,inner sep=1ex", "MAP", "ex"),
       ("inner sep=1ex,font=\\Large", "MAP", "ex"),
       ("inner sep=1ex", "\\Large MAP", "ex")] do
    match pathLabelWitness fonts (pathLabelSource "" "auto" opts body "(4,0)") with
    | .error e => t s!"dimension font: {e}" false
    | .ok w =>
      let expected := if unit == "em" then w.em else if unit == "ex" then w.ex
        else w.em * 3333 / 10000
      t s!"label padding retains its dimension font: {opts}/{body}"
        ((w.gap true - expected).natAbs ≤ 4 && w.size > w.em)
  match pathLabelWitness fonts (pathLabelSource "" "auto" "" "MAP" "(4,2)" "rectangle") with
  | .error e => t s!"rectangle label: {e}" false
  | .ok w =>
    let gap := w.em * 3333 / 10000 + w.width / 2
    t "a rectangle's auto label attaches to its diagonal like a straight path"
      (w.anchor.1 - w.ink.right + 4 ≥ gap &&
       (w.ink.bottom - w.anchor.2 - gap).natAbs ≤ 4)
  for pt in ["11pt", "12pt"] do
    let src := (pathLabelSource "" "auto" "" "MAP\\\\gyp" "(4,0)").replace
      "\\documentclass{article}" ("\\documentclass[" ++ pt ++ "]{article}")
    match pathLabelWitness fonts src with
    | .error e => t s!"document dimension font: {e}" false
    | .ok w =>
      t "label padding follows the document's actual body size"
        ((w.gap true - w.em * 3333 / 10000).natAbs ≤ 4 && w.em > Dim.pt 10)
