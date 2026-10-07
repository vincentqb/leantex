import Tests.Artifact

open LeanTex.Core

namespace PictureShrink

private def names : Array String := #["Birch", "Maple", "Willow"]

private def picture (label : String) : String :=
  "\\begin{tikzpicture}\n" ++
  "\\fill[blue!20] (-1,-0.7) rectangle (2,0.7);\n" ++
  "\\node[draw,fill=black!10,inner sep=4pt,minimum width=16mm] (n) at (0,0) {" ++ label ++ "};\n" ++
  "\\node[circle,draw,minimum size=3mm,inner sep=0pt] at (1.5,0.3) {};\n" ++
  "\\draw[->] (0.9,-0.2) -- (1.8,-0.2);\n" ++
  "\\draw (0.9,-0.4) to[out=90,in=180] (1.8,0.1);\n" ++
  "\\end{tikzpicture}\n\n"

private def source (shrink : Bool) : String :=
  "\\documentclass{article}\\pictures{tool=none}\\begin{document}\n" ++
  "An invented lead line.\n\n" ++ picture "Birch" ++
  "\\vspace{20pt minus " ++ (if shrink then "4" else "0") ++ "pt}\n\n" ++ picture "Maple" ++
  "\\vspace{18pt minus " ++ (if shrink then "8" else "0") ++ "pt}\n\n" ++ picture "Willow" ++
  "\\end{document}"

private def labels (out : Layout.Out) : Array Layout.LineOut :=
  out.pages.flatMap fun p => p.lines.filter fun l => names.contains (lineText l)

private def fills (out : Layout.Out) : Array Layout.Fill := out.pages.flatMap (·.fills)

private def paths (out : Layout.Out) : Array Layout.PathOut := out.pages.flatMap (·.paths)

/-- Independent observations of a shipped path: constructor, dimensions,
segment kinds and every endpoint/control point. Translation changes only y. -/
private def coordinates : Layout.PagePath → Nat × Array Dim.Sp × Array (Dim.Sp × Dim.Sp)
  | .circle x y r => (0, #[r], #[(x, y)])
  | .rect x y w h => (1, #[w, h], #[(x, y)])
  | .segs ss => (2, ss.map (fun s => match s with | .line .. => 0 | .cubic .. => 1),
      ss.flatMap fun s => match s with
      | .line x y u v => #[(x, y), (u, v)]
      | .cubic x y a b c d u v => #[(x, y), (a, b), (c, d), (u, v)])
  | .tri x y u v a b => (3, #[], #[(x, y), (u, v), (a, b)])

private def pathShift (before after : Layout.PathOut) (dy : Dim.Sp) : Bool :=
  let (bk, bd, bp) := coordinates before.path
  let (ak, ad, ap) := coordinates after.path
  bk == ak && bd == ad && bp.size == ap.size &&
    (bp.zip ap).all (fun ((x, y), (u, v)) => x == u && v == y + dy) &&
    before.stroke == after.stroke && before.fill == after.fill && before.leaf == after.leaf

private def fillShift (before after : Layout.Fill) (dy : Dim.Sp) : Bool :=
  before.x == after.x && before.w == after.w && before.h == after.h &&
    before.color == after.color && after.y == before.y + dy

private def close (a b : Dim.Sp) : Bool :=
  -- Each PDF coordinate is rounded to .001 pt. Comparing two box edges
  -- and two baselines can accumulate four such rounding errors.
  (a - b).natAbs ≤ (4 * (Dim.spPerPt / 1000 + 1)).toNat

private def boxShift (bh ah : Dim.Sp) (before after : ArtBox) (dy : Dim.Sp) : Bool :=
  before.kind == after.kind && close before.x0 after.x0 && close before.x1 after.x1 &&
    close (ah - after.y0) (bh - before.y0 + dy) &&
    close (ah - after.y1) (bh - before.y1 + dy)

end PictureShrink

/-- One page owes one glue-set ratio, but each picture owns the shrink
preceding it. Its labels, rectangle fills, outlines, circles, straight and
curved edges, and arrowheads must move together. These invented pictures
have 0, 4 and 12 pt of preceding shrink; a 6 pt deficit moves them by
0, 2 and 6 pt. The PDF reader independently checks the bytes' coordinates.
With no deficit, declaring shrink must leave the PDF byte-identical. -/
def pictureShrinkChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabMeasured oneFace (PictureShrink.source true)
  let geom := Layout.Geom.ofPage doc.page
  let roomy := layoutOf oneFace doc geom
  -- The full-height background encloses every picture mark, so its last
  -- bottom is the page builder's final natural bottom.
  let naturalBottom := (PictureShrink.fills roomy).foldl (fun y f => max y (f.y + f.h)) 0
  let tightGeom := { geom with pageH := naturalBottom + geom.vmargin - Dim.pt 6 }
  let tight := layoutOf oneFace doc tightGeom
  let before := PictureShrink.labels roomy
  let after := PictureShrink.labels tight
  t "picture shrink: supported source and one page at half glue capacity"
    (ds.all (·.code == "N0100") && roomy.pages.size == 1 && tight.pages.size == 1 &&
      !(roomy.diags.any (·.code == "N0200")) &&
      (tight.diags.filter (·.code == "N0200")).size == 1 &&
      (before.map lineText) == PictureShrink.names &&
      (after.map lineText) == PictureShrink.names &&
      (PictureShrink.fills roomy).size == 3 && (PictureShrink.fills tight).size == 3)
  for i in [:3] do
    let name := PictureShrink.names[i]!
    let dy := -Dim.pt (#[0, 2, 6][i]!)
    let a := before[i]!
    let b := after[i]!
    let ps := (PictureShrink.paths roomy).filter (·.leaf == a.leaf)
    let qs := (PictureShrink.paths tight).filter (·.leaf == b.leaf)
    t s!"picture shrink: {name} label follows its own preceding glue"
      (a.x == b.x && b.y == a.y + dy && a.leaf == b.leaf)
    t s!"picture shrink: {name} fill follows its label"
      (PictureShrink.fillShift (PictureShrink.fills roomy)[i]!
        (PictureShrink.fills tight)[i]! dy)
    t s!"picture shrink: {name} all path coordinates follow its label"
      (ps.size == 5 && qs.size == 5 &&
        ps.any (fun p => match p.path with | .circle .. => true | _ => false) &&
        ps.any (fun p => match p.path with
          | .segs ss => ss.any (fun s => match s with | .cubic .. => true | _ => false)
          | _ => false) &&
        (ps.zip qs).all fun (p, q) => PictureShrink.pathShift p q dy)
    let rects := qs.filterMap fun p => match p.path with
      | .rect _ y _ h => some (y, h)
      | _ => none
    t s!"picture shrink: {name} glyph ink stays centered in its node"
      (match rects.toList with
       | [(y, h)] =>
         let (ht, dp) := Layout.labelGlyphExtent oneFace b.size b.segs
         (b.y + (dp - ht) / 2 - (y + h / 2)).natAbs ≤ 1
       | _ => false)
  let roomyPdf := driverPdf oneFace geom doc roomy
  let tightPdf := driverPdf oneFace tightGeom doc tight
  match readArtifact roomyPdf, readArtifact tightPdf with
  | .ok old, .ok now =>
    t "picture shrink: both PDFs decode with all picture paint"
      (old.size == 1 && now.size == 1 && old[0]!.boxes.size == 18 && now[0]!.boxes.size == 18)
    let a := old[0]!
    let b := now[0]!
    for i in [:3] do
      let name := PictureShrink.names[i]!
      let dy := -Dim.pt (#[0, 2, 6][i]!)
      let runsA := a.runs.filter (·.text == name)
      let runsB := b.runs.filter (·.text == name)
      t s!"picture shrink: PDF {name} baseline follows its own glue"
        (match runsA.toList, runsB.toList with
         | [ra], [rb] => PictureShrink.close ra.x rb.x &&
           PictureShrink.close (b.mediaH - rb.y) (a.mediaH - ra.y + dy)
         | _, _ => false)
      -- PDF paints all rectangle fills first, then each picture's five
      -- paths in source order. Every box edge is read from PDF operators.
      let indices := #[i] ++ (Array.range 5).map (fun k => 3 + 5 * i + k)
      t s!"picture shrink: PDF {name} fill and all paths follow its label"
        (indices.all fun k => match a.boxes[k]?, b.boxes[k]? with
          | some p, some q => PictureShrink.boxShift a.mediaH b.mediaH p q dy
          | _, _ => false)
      t s!"picture shrink: PDF {name} baseline keeps its offset inside the box"
        (match runsA.toList, runsB.toList, a.boxes[3 + 5 * i]?, b.boxes[3 + 5 * i]? with
         | [ra], [rb], some p, some q =>
           PictureShrink.close (ra.y - p.y0) (rb.y - q.y0) &&
             PictureShrink.close (p.y1 - ra.y) (q.y1 - rb.y)
         | _, _, _, _ => false)
  | _, _ => t "picture shrink: PDFs decode" false
  let (fixed, fixedDs) := elabMeasured oneFace (PictureShrink.source false)
  let fixedOut := layoutOf oneFace fixed geom
  t "picture shrink: no deficit preserves complete layout"
    (fixedDs.all (·.code == "N0100") && reprStr roomy.pages == reprStr fixedOut.pages)
  t "picture shrink: no deficit preserves exact PDF bytes"
    (roomyPdf == driverPdf oneFace geom fixed fixedOut)
