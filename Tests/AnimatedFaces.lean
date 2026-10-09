module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

/-- Poster content can differ in size from frame one. The shipped box
keeps the first-frame canvas, and the browser names a separate static
poster for print and reduced motion. These assertions fail when the
store carries both values but a backend ignores them. -/
def animatedFacesChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let plan : Image.Plan := { pxW := 60, pxH := 120 }
  let svg := "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"60\" height=\"120\"/>".toUTF8
  let imgs : Image.Store := { entries := #[
    { src := "sequence.pdf", page := .last, animated := true,
      info := some plan, canvasSize := some (Dim.pt 120, Dim.pt 80),
      webSvg := some svg, posterSvg := some svg }] }
  let doc := (elabStr (dvDoc ""
    "\\animategraphics[width=60pt,poster=last,alt={Moving square}]{10}{sequence.pdf}{}{}")).1
  let out := layoutOf fonts doc (imgs := imgs)
  let placements (out : Layout.Out) := (allLines out).flatMap fun line =>
    line.segs.filterMap fun seg => match seg with
      | .image idx w h => some (idx, w, h)
      | _ => none
  let shipped := placements out
  t "a differently sized poster preserves the animation's first-frame canvas"
    (shipped == #[(some 0, Dim.pt 60, Dim.pt 40)])
  let failed := { imgs with entries := imgs.entries.map fun en =>
    { en with webError := some "poster conversion failed" } }
  t "a failed browser conversion preserves the native poster and canvas"
    (placements (layoutOf fonts doc (imgs := failed)) == shipped)
  -- req: a failed browser-face conversion still reserves the image's exact
  -- intrinsic pixel box in the placeholder, so the page does not reflow.
  let (_, failedTree, _) := HtmlDoc.emitTree { imgs := failed } doc
  let failedSpans := elemAttrsList (· == "span") #[] failedTree.toList
  t "a failed conversion placeholder reserves the exact intrinsic pixel box"
    (failedSpans.any fun (_, attrs) =>
      attrs.any fun (key, value) => key == "style" &&
        hasStr value "width: 160px" && hasStr value "height: 107px")
  -- req: a generated style never begins with a stray separator. An unsized
  -- animation has only the canvas aspect-ratio, which must not lead with ';'.
  let barePlan : Image.Plan := { pxW := 60, pxH := 120 }
  let bareStore : Image.Store := { entries := #[
    { src := "sequence.pdf", animated := true, info := some barePlan,
      canvasSize := some (Dim.pt 120, Dim.pt 80), webSvg := some svg,
      posterSvg := some svg }] }
  let bare := (elabStr (dvDoc ""
    "\\animategraphics[alt={Moving square}]{10}{sequence.pdf}{}{}")).1
  let (_, bareTree, _) := HtmlDoc.emitTree { imgs := bareStore } bare
  let bareImgs := elemAttrsList (· == "img") #[] bareTree.toList
  t "an unsized animation declares the canvas without a leading separator"
    (bareImgs.any fun (_, attrs) =>
      attrs.any fun (key, value) => key == "style" &&
        hasStr value "aspect-ratio: " && hasStr value "object-fit: fill" &&
        !value.startsWith ";" && !value.startsWith " ")
  let (_, tree, _) := HtmlDoc.emitTree { imgs } doc
  let images := elemAttrsList (· == "img") #[] tree.toList
  t "HTML declares the same first-frame aspect ratio"
    (images.any fun (_, attrs) =>
      attrs.contains ("width", "160") && attrs.contains ("height", "107") &&
      attrs.any (fun (key, value) => key == "style" &&
        hasStr value s!"aspect-ratio: {Dim.pt 120} / {Dim.pt 80}" &&
        hasStr value "object-fit: fill"))
  let sources := elemAttrsList (· == "source") #[] tree.toList
  t "HTML selects a static poster for print and reduced motion"
    (sources.any fun (_, attrs) =>
      attrs.any (fun (key, value) => key == "media" &&
        hasStr value "print" && hasStr value "prefers-reduced-motion: reduce") &&
      attrs.any (fun (key, value) => key == "srcset" && !value.isEmpty))
  t "both animation and static poster are captured"
    ((HtmlDoc.imageResources imgs).size == 2)
  t "every picture source embeds a captured resource"
    (sources.all fun (_, attrs) => attrs.all fun (key, value) =>
      key != "srcset" || (HtmlDoc.imageResources imgs).any (fun asset => value == asset.uri))
  let facts := HtmlDoc.a11yFacts true false tree
  t "animation alternatives name one image without hidden focus"
    (images.size == 1 && images.all (fun (_, attrs) => attrs.contains ("alt", "Moving square")) &&
      (elemAttrsList (· == "picture") #[] tree.toList).size == 1 &&
      facts.imgs == 1 && facts.imgsUnnamed == 0 && facts.hiddenTabStops == 0)

end Tests
