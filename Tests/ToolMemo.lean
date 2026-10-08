module

public import LeanTex.Cli.ConvCache
public import LeanTex.Cli.ToolProbe
public import LeanTex.Cli.AtomicFile
public import Tests.Support

public section

open LeanTex.Cli

namespace Tests

/-- A memo reuses only a complete, intact answer. Publishing a replacement
must leave existing readers and older writers on their original file. -/
def toolMemoChecks (ref : IO.Ref (List String)) : IO Unit := do
  IO.FS.withTempDir fun dir => do
    -- Publishing beside a writable destination must not depend on the
    -- system temporary directory. Only the child's environment changes.
    let some lean ← ToolProbe.onPath "lean" |
      throw <| IO.userError "atomic publication checks require the Lean interpreter"
    let driver := dir / "publication.lean"
    IO.FS.writeFile driver <|
      "import LeanTex.Cli.AtomicFile\n" ++
      "def main (args : List String) : IO Unit := do\n" ++
      "  let [target] := args | throw (IO.userError \"expected one destination\")\n" ++
      "  LeanTex.Cli.AtomicFile.write target \"complete answer\".toUTF8\n"
    let target := dir / "independent.answer"
    let unavailable := (dir / "missing-temporary-directory").toString
    let result ← IO.Process.output {
      cmd := lean.toString, args := #["--run", driver.toString, target.toString],
      env := #[("TMPDIR", some unavailable), ("TMP", some unavailable),
        ("TEMP", some unavailable)] }
    check ref "atomic file: publication needs only the destination directory"
      (result.exitCode == 0 &&
        (← (IO.FS.readFile target).toBaseIO).toOption == some "complete answer")

    let memo := dir / "tool.ver"
    let stampA := "synthetic-tool\t101\t1\t0"
    let stampB := "synthetic-tool\t102\t2\t0"
    let versionA := "converter 12345"
    let versionB := "converter 98765"
    let repair (label : String) (contents : ByteArray) (stamp : String) : IO Unit := do
      IO.FS.writeBinFile memo contents
      let calls ← IO.mkRef (0 : Nat)
      let probe := do
        calls.modify (· + 1)
        return PicCache.Tool.present versionA
      let got ← ToolProbe.identify memo stamp probe
      check ref s!"tool memo/{label}: invalid data requires a fresh answer"
        (got == .present versionA && (← calls.get) == 1)
      let warm ← ToolProbe.identify memo stamp probe
      check ref s!"tool memo/{label}: the repaired answer is reusable"
        (warm == .present versionA && (← calls.get) == 1)

    repair "legacy raw" (PicCache.versionMemo stampA versionA).toUTF8 stampA
    let encoded ← IO.FS.readBinFile memo
    let text ← IO.FS.readFile memo
    for n in [:encoded.size] do
      repair s!"prefix {n}" (encoded.extract 0 n) stampA
    repair "changed witness" (text.replace stampA stampB).toUTF8 stampB
    repair "changed version" (text.replace versionA versionB).toUTF8 stampA
    repair "trailing data" (encoded ++ "\nextra line".toUTF8) stampA
    repair "invalid UTF-8" (encoded.push 255) stampA
    repair "old schema" (text.replace "tool-version-v2" "tool-version-v1").toUTF8 stampA

    IO.FS.removeFile memo
    discard <| ToolProbe.identify memo stampA (pure (.present versionA))
    let before ← IO.FS.readBinFile memo
    IO.FS.withFile memo .read fun reader => do
      let got ← ToolProbe.identify memo stampB (pure (.present versionB))
      check ref "tool memo: a changed witness returns the new version" (got == .present versionB)
      check ref "tool memo: an open reader retains the complete previous file"
        ((← reader.readBinToEnd) == before)
    let warm ← ToolProbe.identify memo stampB (pure (.absent "unexpected probe"))
    check ref "tool memo: a new reader gets the complete replacement"
      (warm == .present versionB && (← IO.FS.readBinFile memo) != before)

    -- A legacy writer has flushed a valid-looking prefix but still owns its
    -- handle. Its eventual suffix cannot alter the newly published memo.
    IO.FS.withFile memo .write fun writer => do
      writer.putStr (PicCache.versionMemo stampA "converter 1")
      writer.flush
      let calls ← IO.mkRef (0 : Nat)
      let got ← ToolProbe.identify memo stampA do
        calls.modify (· + 1)
        return .present versionA
      check ref "tool memo: an in-flight legacy prefix is never reused"
        (got == .present versionA && (← calls.get) == 1)
      let published ← IO.FS.readBinFile memo
      writer.putStr "2345"
      writer.flush
      check ref "tool memo: an older writer cannot damage the replacement"
        ((← IO.FS.readBinFile memo) == published)
    let warm ← ToolProbe.identify memo stampA (pure (.absent "unexpected probe"))
    check ref "tool memo: the replacement survives the older writer closing"
      (warm == .present versionA)

    for badPath in #[dir / "blocked.ver", dir / "missing" / "tool.ver"] do
      if badPath.fileName == some "blocked.ver" then IO.FS.createDir badPath
      let calls ← IO.mkRef (0 : Nat)
      for _ in [:2] do
        let got ← ToolProbe.identify badPath stampA do
          calls.modify (· + 1)
          return .present versionA
        check ref "tool memo: failed publication preserves the probe answer" (got == .present versionA)
      check ref "tool memo: failed publication is retried" ((← calls.get) == 2)
    check ref "tool memo: successful and failed publications clean their staging files"
      ((← dir.readDir).all fun entry => !entry.fileName.endsWith ".part")

    -- ConvCache's public publisher retains the same byte-for-byte replacement
    -- and cleanup behaviour after its implementation is shared with ToolProbe.
    let target := dir / "conversion.answer"
    let old := ConvCache.encode (.error "synthetic previous refusal")
    let next := ConvCache.encode (.ok "synthetic conversion answer".toUTF8)
    ConvCache.atomicWrite target old
    IO.FS.withFile target .read fun reader => do
      ConvCache.atomicWrite target next
      check ref "atomic file: an existing conversion reader retains its envelope"
        ((← reader.readBinToEnd) == old)
    check ref "atomic file: the new conversion reader gets the whole replacement"
      ((← IO.FS.readBinFile target) == next)
    let blocked := dir / "blocked.answer"
    IO.FS.createDir blocked
    IO.FS.writeFile (blocked / "sentinel") "keep"
    let failed ← (ConvCache.atomicWrite blocked next).toBaseIO
    check ref "atomic file: failed rename preserves the destination"
      ((match failed with | .error _ => true | .ok _ => false) &&
        (← IO.FS.readFile (blocked / "sentinel")) == "keep")
    check ref "atomic file: no staging files survive either outcome"
      ((← dir.readDir).all fun entry => !entry.fileName.endsWith ".part")

end Tests
