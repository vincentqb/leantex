import Main
import Tests.Support

namespace Tests

open LeanTex.Core

/-- A boundary face is the conversion of captured PDF bytes. A stale
unkeyed sibling cannot answer for it, and a cache replacement between
preparation and acceptance cannot change the published artifact. -/
def svgPublicationChecks (ref : IO.Ref (List String)) : IO Unit := do
  let .ok expected ← LeanTex.Cli.ImageAssets.picFace svgCanvasPdf |
    throw <| IO.userError "the boundary publication probe requires pdftocairo"
  IO.FS.withTempDir fun dir => do
    for name in ["stale", "deleted"] do
      let cache := dir / name
      IO.FS.createDirAll cache
      let cached := cache / "picture.pdf"
      let sibling := cached.withExtension "svg"
      if name == "stale" then
        IO.FS.writeFile cached "a replaced PDF cache entry"
        IO.FS.writeFile sibling "<svg>an obsolete sibling</svg>"
      let source := Ir.picSrcPrefix ++ "0123456789abcdef0123456789abcdef"
      let output := cache / "out"
      let initial : Image.Store := { entries := #[
        { src := source, info := some { pxW := 120, pxH := 80 } }] }
      let (imgs, diags, unconverted) ← picsToSvg
        #[{ src := source, bytes := svgCanvasPdf, cached }] initial
      check ref s!"boundary {name}: conversion follows captured PDF bytes"
        (imgs.entries[0]!.webSvg == some expected && diags.isEmpty && unconverted.isEmpty)
      check ref s!"boundary {name}: preparation creates no output directory"
        (!(← output.pathExists))
      let doc := (elabStr "\\includegraphics[alt={Captured square}]{figure.svg}").1
      let rename (i : Ir.Inline) : Ir.Inline := match i with
        | .image _ size alt => .image source size alt
        | i => i
      let doc := { doc with body := Ir.mapBlocks rename doc.body }
      let (result, _) ← prepareHtml "figure.tex" { imgs } doc
      let page ← match result with
        | .ok page => pure page
        | .error why => throw <| IO.userError ("the captured boundary SVG did not close: " ++ why)
      -- Neither location remains trustworthy by the time acceptance ends.
      IO.FS.writeFile cached "changed after preparation"
      IO.FS.writeFile sibling "<svg>changed after preparation</svg>"
      let target := output / "figure.html"
      let _ ← publish none (some (target.toString, page)) none none
      let html ← IO.FS.readFile target
      let (_, got) ← svgPublishedAsset html output "img" "src"
      check ref s!"boundary {name}: publication writes the checked serialization"
        (html == page.render)
      check ref s!"boundary {name}: publication uses the prepared SVG snapshot"
        (got == expected)
      check ref s!"boundary {name}: publication consists of one file"
        ((← output.readDir).map (·.fileName) == #["figure.html"])

end Tests
