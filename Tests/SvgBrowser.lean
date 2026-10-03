import scripts.Board
import Tests.Support

namespace Tests

open LeanTex.Core LeanTex.Cli Scoreboard

/-- Source keys and expected browser identities read captured inputs. The
filesystem may change after capture, but that cannot alter this build. -/
def svgBrowserSourceChecks (ref : IO.Ref (List String)) : IO Unit := do
  IO.FS.withTempDir fun dir => do
    let moving := svgDocument
      "<rect width=\"20\" height=\"20\"><animate attributeName=\"opacity\" values=\"0;1;0\" dur=\"2s\"/></rect>"
    IO.FS.writeBinFile (dir / "sequence.PDF") svgCanvasPdf
    IO.FS.writeBinFile (dir / "sequence.SVG") moving
    let (doc, _) := elabStr
      "\\animategraphics[poster=last,alt={Moving square}]{10}{sequence.PDF}{}{}"
    let (store, _, read) ← Hermetic.storeFor dir doc
    check ref "hermetic source: uppercase companion is captured once"
      (store.entries.any fun en => en.companion == some moving)
    check ref "hermetic source: the recorded input includes the actual companion bytes"
      (read.contains ("sequence.SVG", moving))
    let before := Hermetic.browserSourceBlobs "figure" doc store
    IO.FS.removeFile (dir / "sequence.PDF")
    IO.FS.removeFile (dir / "sequence.SVG")
    check ref "hermetic source: deleting files after capture cannot change its source key"
      (contentKey before == contentKey (Hermetic.browserSourceBlobs "figure" doc store))
    let actual ← imageFaces store
    let faced := Hermetic.facedStore store
    let expectedFor := fun imgs : Image.Store =>
      let (_, body, _) := HtmlDoc.emitTree { imgs } doc
      browserExpectedFaces "figure" body
    let expected := expectedFor faced
    check ref "hermetic source: expected identities match real converted primary and poster"
      (expected == expectedFor actual && expected.size == 2)
    check ref "hermetic source: the typed page contains every captured resource URI"
      ((HtmlDoc.imageResources faced).all fun a =>
        let html := (HtmlDoc.emit { imgs := faced, assetsDir := "figure.assets" } doc).1
        (html.splitOn a.uri).length > 1)
    let without : Image.Store :=
      { entries := store.entries.map fun en => { en with companion := none } }
    check ref "hermetic source: removing a captured companion changes both plan and key"
      ((expectedFor (Hermetic.facedStore without)).size == 1 &&
        contentKey before != contentKey (Hermetic.browserSourceBlobs "figure" doc without))
where
  imageFaces (store : Image.Store) : IO Image.Store := do
    return { entries := ← store.entries.mapM BrowserFaces.prepare }

end Tests
