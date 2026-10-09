module

public import LeanTex.Cli.PictureAssets
public import Tests.Support

public section

namespace Tests

open LeanTex.Cli

private def pictureAssetWrapped : String :=
  "\\documentclass{article}\n\\begin{document}Synthetic picture.\\end{document}\n"

private def pictureAssetPdf (label : String) : ByteArray :=
  svgCanvasPdf ++ ("\n% synthetic picture tool: " ++ label ++ "\n").toUTF8

private def pictureAssetQuote (text : String) : String :=
  "'" ++ text.replace "'" "'\\''" ++ "'"

private def pictureAssetToolBody (root : System.FilePath) (label : String) : String :=
  "#!/bin/sh\nset -eu\nroot=" ++ pictureAssetQuote root.toString ++
  "\nlabel=" ++ pictureAssetQuote label ++ "\n" ++
  "if [ \"$1\" = --version ]; then\n\
  printf '%s\\n' version >> \"$root/$label.calls\"\n\
  printf '%s\\n' 'synthetic picture renderer 1'\n\
  exit 0\n\
fi\n\
[ \"$#\" -eq 3 ] && [ \"$1\" = -interaction=batchmode ] && \
[ \"$2\" = -halt-on-error ] && [ \"$3\" = pic.tex ] || exit 91\n\
/usr/bin/cmp pic.tex \"$root/wrapped.tex\" || exit 92\n\
printf '%s\\n' render >> \"$root/$label.calls\"\n\
printf '%s\\n' \"$0\" >> \"$root/$label.argv0\"\n\
mode=$(/bin/cat \"$root/mode\")\n\
case \"$mode\" in\n\
  inconclusive) exit 17;;\n\
  refused) printf '%s\\n' 'synthetic picture refusal' > pic.log; exit 17;;\n\
esac\n\
if [ \"$mode\" = barrier ]; then\n\
  if /bin/mkdir \"$root/claimed\" 2>/dev/null; then who=first; peer=second\n\
  else who=second; peer=first; fi\n\
  pwd -P > \"$root/$who.cwd\"\n\
  printf '%s\\n' \"$who\" > attempt-owner\n\
  : > \"$root/$who.started\"\n\
  n=0\n\
  while [ ! -f \"$root/$peer.started\" ] && [ \"$n\" -lt 500 ]; do\n\
    /bin/sleep 0.01\n\
    n=$((n + 1))\n\
  done\n\
  if [ ! -f \"$root/$peer.started\" ]; then : > \"$root/timed-out\"; exit 93; fi\n\
  if [ \"$(/bin/cat attempt-owner)\" != \"$who\" ]; then\n\
    : > \"$root/shared-cwd\"; exit 94\n\
  fi\n\
  : > \"$root/$who.observed-peer\"\n\
fi\n\
/bin/cat \"$root/$label.pdf\" > pic.pdf\n\
printf '%s\\n' 'synthetic picture produced' > pic.log\n"

private def pictureAssetInstall (root : System.FilePath) (label : String) :
    IO (String × String × String) := do
  let tool := root / label
  IO.FS.writeFile tool (pictureAssetToolBody root label)
  IO.setAccessRights tool { user := ⟨true, true, true⟩ }
  IO.FS.writeBinFile (root / (label ++ ".pdf")) (pictureAssetPdf label)
  let stamp ← ToolProbe.witness tool.toString
  let .present version ← ToolProbe.probeVersion tool.toString |
    throw <| IO.userError "the synthetic picture tool did not report its version"
  if stamp.isEmpty then
    throw <| IO.userError "the synthetic picture tool has no identity witness"
  return (tool.toString, stamp, version)

private def pictureAssetLines (path : System.FilePath) : IO (List String) := do
  return ((← (IO.FS.readFile path).toBaseIO).toOption.getD "").splitOn "\n"
    |>.filter (!·.isEmpty)

private def pictureAssetRead (path : System.FilePath) : IO ByteArray := do
  return (← (IO.FS.readBinFile path).toBaseIO).toOption.getD ByteArray.empty

private def pictureAssetNames (path : System.FilePath) : IO (Array String) := do
  return ((← path.readDir.toBaseIO).toOption.getD #[]).map (·.fileName)

private def pictureAssetDrawn (got : PictureAssets.Answer) (expected : ByteArray)
    (cached : Bool) : Bool :=
  got.result.outcome == .drawn && got.result.bytes == expected && got.cached == cached

/-- Actual foreground processes, captured PDFs and checksummed cache records.
The file handshake witnesses overlap; its bounded polling only prevents a
broken implementation from hanging the suite. No elapsed-time claim is made. -/
def pictureAssetsChecks (ref : IO.Ref (List String)) : IO Unit :=
  IO.FS.withTempDir fun temporary => do
    let root ← IO.FS.realPath temporary
    let t := check ref
    IO.FS.writeFile (root / "wrapped.tex") pictureAssetWrapped
    IO.FS.writeFile (root / "mode") "barrier"
    let (tool, stamp, version) ← pictureAssetInstall root "renderer-a"
    let expected := pictureAssetPdf "renderer-a"
    let calls := root / "renderer-a.calls"
    let cache := root / "cache"
    IO.FS.createDir cache
    let name := PictureAssets.slotName pictureAssetWrapped tool stamp version
    let slot := cache / name
    let run := PictureAssets.fulfil (some cache) tool stamp version pictureAssetWrapped

    let first ← IO.asTask run .dedicated
    let second ← IO.asTask run .dedicated
    let one ← IO.wait first
    let two ← IO.wait second
    t "picture assets: independent identical requests both return their complete captured PDF"
      (one.toOption.any (pictureAssetDrawn · expected false) &&
        two.toOption.any (pictureAssetDrawn · expected false))
    let firstCwd ← pictureAssetLines (root / "first.cwd")
    let secondCwd ← pictureAssetLines (root / "second.cwd")
    t "picture assets: concurrent attempts have distinct working directories"
      (firstCwd.length == 1 && secondCwd.length == 1 && firstCwd != secondCwd &&
        !(← (root / "shared-cwd").pathExists))
    t "picture assets: the foreground tools each observe the other before finishing"
      ((← (root / "first.observed-peer").pathExists) &&
        (← (root / "second.observed-peer").pathExists) &&
        !(← (root / "timed-out").pathExists))
    t "picture assets: exactly two cold render processes ran"
      ((← pictureAssetLines calls).count "render" == 2)
    t "picture assets: concurrent writers leave one whole checked answer and no staging residue"
      (name.endsWith ".answer" && (← pictureAssetNames cache) == #[name] &&
        ConvCache.decode (← pictureAssetRead slot) == some (.ok expected))

    IO.FS.writeFile (root / "mode") "draw"
    let before ← pictureAssetLines calls
    let warm ← run
    t "picture assets: a checked cache hit returns the captured PDF without running the tool"
      (pictureAssetDrawn warm expected true && (← pictureAssetLines calls) == before)

    let encoded := ConvCache.encode (.ok expected)
    let corrupt := encoded.set! (encoded.size - 1) 0
    for (label, broken) in [
        ("truncated", encoded.extract 0 (encoded.size / 2)),
        ("corrupt", corrupt)] do
      t s!"picture assets: the {label} test record fails checksum validation"
        (ConvCache.decode broken == none)
      IO.FS.writeBinFile slot broken
      let before := (← pictureAssetLines calls).count "render"
      let retried ← run
      t s!"picture assets: a {label} record retries once and publishes the full answer"
        (pictureAssetDrawn retried expected false &&
          (← pictureAssetLines calls).count "render" == before + 1 &&
          ConvCache.decode (← pictureAssetRead slot) == some (.ok expected) &&
          (← pictureAssetNames cache) == #[name])

    let (otherTool, otherStamp, otherVersion) ← pictureAssetInstall root "renderer-b"
    t "picture assets: distinct executable paths really report the same version banner"
      (tool != otherTool && stamp != otherStamp && version == otherVersion)
    let otherName := PictureAssets.slotName pictureAssetWrapped otherTool otherStamp otherVersion
    let otherExpected := pictureAssetPdf "renderer-b"
    let otherCalls := root / "renderer-b.calls"
    let other ← PictureAssets.fulfil (some cache)
      otherTool otherStamp otherVersion pictureAssetWrapped
    t "picture assets: a same-version tool at another path cannot reuse the first tool's answer"
      (name != otherName && pictureAssetDrawn other otherExpected false &&
        (← pictureAssetLines otherCalls).count "render" == 1 &&
        ConvCache.decode (← pictureAssetRead (cache / otherName)) == some (.ok otherExpected) &&
        ConvCache.decode (← pictureAssetRead slot) == some (.ok expected))
    let otherBefore ← pictureAssetLines otherCalls
    let otherWarm ← PictureAssets.fulfil (some cache)
      otherTool otherStamp otherVersion pictureAssetWrapped
    t "picture assets: each tool's answer warms independently"
      (pictureAssetDrawn otherWarm otherExpected true &&
        (← pictureAssetLines otherCalls) == otherBefore)

    let retryCache := root / "inconclusive"
    IO.FS.createDir retryCache
    IO.FS.writeFile (root / "mode") "inconclusive"
    let before := (← pictureAssetLines calls).count "render"
    for _ in [:2] do
      let got ← PictureAssets.fulfil (some retryCache) tool stamp version pictureAssetWrapped
      t "picture assets: a failed process without a log is inconclusive and uncached"
        (!got.cached && got.result.bytes.isEmpty &&
          match got.result.outcome with
          | .inconclusive _ => true
          | .drawn | .refused _ => false)
    t "picture assets: an inconclusive process outcome retries and writes no cache answer"
      ((← pictureAssetLines calls).count "render" == before + 2 &&
        (← pictureAssetNames retryCache).isEmpty)

    IO.FS.writeFile (root / "mode") "refused"
    let refused ← PictureAssets.fulfil (some retryCache) tool stamp version pictureAssetWrapped
    let before ← pictureAssetLines calls
    let replayed ← PictureAssets.fulfil (some retryCache) tool stamp version pictureAssetWrapped
    t "picture assets: a logged refusal is remembered with the same words and no rerun"
      (!refused.cached && replayed.cached && refused.result.outcome == replayed.result.outcome &&
        (match refused.result.outcome with
        | .refused words => words.trimAscii.toString == "synthetic picture refusal"
        | .drawn | .inconclusive _ => false) &&
        (← pictureAssetLines calls) == before)
    t "picture assets: a remembered refusal is not a previous captured PDF"
      ((← PictureAssets.previous retryCache (PictureAssets.key pictureAssetWrapped)) == none)

    IO.FS.writeFile (root / "mode") "draw"
    let blocked := root / "cache-is-a-file"
    IO.FS.writeFile blocked "a regular file cannot contain cache records"
    let got ← PictureAssets.fulfil (some blocked) tool stamp version pictureAssetWrapped
    t "picture assets: an unavailable cache directory does not lose produced bytes"
      (pictureAssetDrawn got expected false &&
        (← IO.FS.readFile blocked) == "a regular file cannot contain cache records")
    let renameCache := root / "rename-failure"
    IO.FS.createDir renameCache
    IO.FS.createDir (renameCache / name)
    let got ← PictureAssets.fulfil (some renameCache) tool stamp version pictureAssetWrapped
    t "picture assets: a failed cache rename preserves captured bytes and removes staging files"
      (pictureAssetDrawn got expected false && (← pictureAssetNames renameCache) == #[name])
    let got ← PictureAssets.fulfil none tool stamp version pictureAssetWrapped
    t "picture assets: rendering with no cache still returns the exact captured bytes"
      (pictureAssetDrawn got expected false)

    -- TeX engines select their format from the invoked name. Resolving a
    -- symlink for identity must not replace that name when executing it.
    let aliasPath := root / "renderer-format"
    let linked ← IO.Process.output {
      cmd := "ln", args := #["-s", tool, aliasPath.toString] }
    t "picture assets: the synthetic format alias is a working symlink"
      (linked.exitCode == 0 && (← IO.FS.realPath aliasPath).toString == tool)
    let aliased ← PictureAssets.fulfil none aliasPath.toString "" "" pictureAssetWrapped
    t "picture assets: an executable alias keeps its invocation name in owned scratch"
      (pictureAssetDrawn aliased expected false &&
        (← pictureAssetLines (root / "renderer-a.argv0")).getLast? == some aliasPath.toString)

    let history := root / "previous"
    IO.FS.createDir history
    let sourceKey := PictureAssets.key pictureAssetWrapped
    IO.FS.writeBinFile (history / (sourceKey ++ "-legacy.pdf")) expected
    IO.FS.writeBinFile (history / (sourceKey ++ "-refused.answer"))
      (ConvCache.encode (.error "synthetic picture refusal"))
    IO.FS.writeBinFile (history / (sourceKey ++ "-broken.answer")) corrupt
    let unrelated := PictureAssets.slotName (pictureAssetWrapped ++ "% unrelated source\n")
      tool stamp version
    IO.FS.writeBinFile (history / unrelated) encoded
    t "picture assets: previous ignores raw PDFs, refusals, corrupt records and unrelated source keys"
      ((← PictureAssets.previous history sourceKey) == none)
    IO.FS.writeBinFile (history / name) encoded
    t "picture assets: previous returns only the matching checked success bytes"
      ((← PictureAssets.previous history sourceKey) == some expected)

end Tests
