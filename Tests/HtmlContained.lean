import Tests.Support

open LeanTex.Core

namespace Tests

/-- A byte oracle independent of the emitter's encoder. The command reads
only invented test bytes or the repository's test faces. -/
private def containedDataOracle (mime : String) (data : ByteArray) : IO String :=
  IO.FS.withTempDir fun dir => do
    let path := dir / "payload"
    IO.FS.writeBinFile path data
    let out ← IO.Process.output { cmd := "base64", args := #["-w0", path.toString] }
    unless out.exitCode == 0 do
      throw <| IO.userError "the HTML containment byte oracle requires base64"
    return "data:" ++ mime ++ ";base64," ++ out.stdout

/-- A single HTML file carries the exact captured rendering bytes in its
actual typed carriers. These assertions fail on the sibling-file emitter;
closure of nested SVG/CSS references is a separate, stricter obligation. -/
def htmlContainedChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let moving := svgDocument "<rect width=\"20\" height=\"20\" fill=\"blue\"/>"
  let poster := svgDocument "<rect width=\"20\" height=\"20\" fill=\"red\"/>"
  let body := "\\includegraphics[alt={A captured square}]{figure.svg} " ++
    "\\href{https://example.invalid/reading}{Further reading}"
  let doc := (elabStr body).1
  let imgs : Image.Store := { entries := #[
    { src := "figure.svg", source := some moving, posterSvg := some poster,
      info := some { pxW := 20, pxH := 20 } }] }
  let cfg : HtmlDoc.Config := { imgs, fonts := some fonts, mdHref := some "reading.md" }
  let (head, tree, _) := HtmlDoc.emitTree cfg doc
  let images := elemAttrsList (· == "img") #[] tree.toList
  let sources := elemAttrsList (· == "source") #[] tree.toList
  let expectedMoving ← containedDataOracle "image/svg+xml" moving
  let expectedPoster ← containedDataOracle "image/svg+xml" poster
  t "contained HTML: moving image carries captured bytes"
    (images.size == 1 && images.all (fun (_, attrs) =>
      attrs.contains ("src", expectedMoving)))
  t "contained HTML: static media source carries its own captured bytes"
    (sources.size == 1 && sources.all (fun (_, attrs) =>
      attrs.contains ("srcset", expectedPoster) &&
      attrs.contains ("media", "print, (prefers-reduced-motion: reduce)")))
  let converted := { imgs with entries := imgs.entries.map fun en =>
    { en with source := some "replaced original".toUTF8, webSvg := some moving } }
  let (_, convertedTree, _) := HtmlDoc.emitTree { cfg with imgs := converted } doc
  t "contained HTML: converted browser bytes win over original bytes"
    ((elemAttrsList (· == "img") #[] convertedTree.toList).all fun (_, attrs) =>
      attrs.contains ("src", expectedMoving))
  let css := treeCssList "" head.toList
  for ff in HtmlDoc.shipFaces fonts do
    let f := fonts.get ff.index
    let expected ← containedDataOracle (if f.isCff then "font/otf" else "font/ttf") f.data
    t "contained HTML: font rule carries its resolved face byte for byte"
      (hasStr css ("src: url(\"" ++ expected ++ "\") format(\"" ++ ff.format ++ "\")"))
  let links := elemAttrsList (· == "a") #[] tree.toList
  t "contained HTML: outgoing reading link remains navigation"
    (links.any fun (_, attrs) => attrs.contains ("href", "https://example.invalid/reading"))
  t "contained HTML: markdown alternate remains navigation"
    ((elemAttrsList (· == "link") #[] head.toList).any fun (_, attrs) =>
      attrs.contains ("rel", "alternate") && attrs.contains ("href", "reading.md"))

end Tests
