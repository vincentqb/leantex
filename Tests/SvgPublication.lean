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
      let (_, pubs, diags, unconverted) ← picsToSvg
        #[{ src := source, bytes := svgCanvasPdf, cached }] "figure.assets" { entries := #[] }
      check ref s!"boundary {name}: conversion follows captured PDF bytes"
        (pubs.size == 1 && diags.isEmpty && unconverted.isEmpty)
      check ref s!"boundary {name}: preparation creates no output directory"
        (!(← output.pathExists))
      -- Neither location remains trustworthy by the time acceptance ends.
      IO.FS.writeFile cached "changed after preparation"
      IO.FS.writeFile sibling "<svg>changed after preparation</svg>"
      let ui ← Ui.mk' { cmd := .help, color := .never }
      let _ ← publish ui none "figure.assets" "figure.fonts"
        (some ((output / "figure.html").toString, "<html></html>", pubs, #[], none))
        none none
      let target := output / "figure.assets" / "0123456789abcdef0123456789abcdef.svg"
      let got := (← (IO.FS.readBinFile target).toBaseIO).toOption
      check ref s!"boundary {name}: publication uses the prepared SVG snapshot"
        (got == some expected)
      check ref s!"boundary {name}: publication leaves no staging files"
        (← if ← (output / "figure.assets").pathExists then do
          pure ((← (output / "figure.assets").readDir).all (fun en => en.fileName.endsWith ".svg"))
        else pure true)

end Tests
