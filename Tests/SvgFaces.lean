module

public import Tests.DriverAssets
public import Tests.Support

public section

namespace Tests

open LeanTex.Core Tests.DriverAssets

/-- Preparing an image twice must keep the same published faces and native
canvas. Conversion always consumes the captured source; a previous browser
face cannot hide a failed new conversion. -/
def svgFacePreparationChecks (ref : IO.Ref (List String)) : IO Unit := do
  let req : Image.Request := { src := "selected.pdf", page := .last, animated := true }
  let .ok (info, canvas) := Image.decodeRequest .default svgCanvasPdf req |
    throw <| IO.userError "the synthetic PDF did not decode"
  let entry : Image.Loaded :=
    { toRequest := req, info := some info, canvasSize := canvas, source := some svgCanvasPdf }
  let store : Image.Store := { entries := #[entry] }
  let once ← imageBrowserFaces store
  let twice ← imageBrowserFaces once
  check ref "browser preparation: the selected PDF page has a primary SVG"
    (once.entries[0]!.webSvg.isSome && once.entries[0]!.posterSvg.isNone)
  check ref "browser preparation: a second pass publishes exactly the same assets"
    (HtmlDoc.imageAssets once == HtmlDoc.imageAssets twice)
  check ref "browser preparation: a second pass retains captured primary bytes"
    (once.entries[0]!.webSvg == twice.entries[0]!.webSvg)
  check ref "browser preparation: the first-frame canvas survives both passes"
    (once.entries[0]!.size? == store.entries[0]!.size? &&
      twice.entries[0]!.size? == store.entries[0]!.size?)
  let broken : Image.Store :=
    { entries := #[{ once.entries[0]! with source := some "a failed captured PDF".toUTF8 }] }
  let refused ← imageBrowserFaces broken
  check ref "browser preparation: old browser bytes cannot answer for a failed source"
    (refused.entries[0]!.webError.isSome && (HtmlDoc.imageAssets refused).isEmpty)
  check ref "browser preparation: failed conversion clears old converted payloads"
    (refused.entries[0]!.webSvg.isNone && refused.entries[0]!.posterSvg.isNone)

end Tests
