import LeanTex.Cli.ConvCache

open LeanTex.Cli

-- These checks cross the real process/file boundary. Stubs name their
-- invocations so a warm answer, a replay, and a retry cannot look alike.
private def stub (payload : String) (tail : String := "") : String :=
  "#!/bin/sh\n\
if [ \"$1\" = '-v' ]; then echo V >> \"$COUNT\"; echo 'converter 1'; exit 0; fi\n\
echo C >> \"$COUNT\"\n\
for out in \"$@\"; do :; done\n" ++
  (if tail.isEmpty then "printf '%s' '" ++ payload ++ "' > \"$out\"\n" else tail)

private def face (ink : String) : String :=
  "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"100\" height=\"100\"><path d=\"" ++ ink ++ "\"/></svg>"

private def writeTool (path : System.FilePath) (body : String) : IO Unit := do
  IO.FS.writeFile path body
  IO.setAccessRights path { user := ⟨true, true, true⟩ }

private def calls (path : System.FilePath) : IO Nat := do
  let text := (← (IO.FS.readFile path).toBaseIO).toOption.getD ""
  return ((text.splitOn "\n").filter (· == "C")).length

private def slots (root : System.FilePath) : IO (Array System.FilePath) := do
  let entries := (← (root / "leantex" / "convs").readDir.toBaseIO).toOption.getD #[]
  return entries.filterMap fun en => if en.fileName.endsWith ".answer" then some en.path else none

def main (args : List String) : IO UInt32 := do
  let failures ← IO.mkRef (#[] : Array String)
  let check (name : String) (ok : Bool) : IO Unit := do
    unless ok do failures.modify (·.push name)
  let probe ← IO.FS.realPath ".lake/build/bin/convProbe"
  let path := (← IO.getEnv "PATH").getD ""
  let first := face "M0 0L20 20"
  IO.FS.withTempDir fun dir => do
    let bin := dir / "bin"
    let cache := dir / "cache"
    let count := dir / "count"
    IO.FS.createDirAll bin
    writeTool (bin / "pdftocairo") (stub first)
    let run := RunBounded.runBounded probe.toString #[] dir 4000 100
      (env := #[("PATH", some (bin.toString ++ ":" ++ path)),
        ("XDG_CACHE_HOME", some cache.toString), ("COUNT", some count.toString)])
    let a ← run
    let saved ← slots cache
    check "cache migration: fresh conversion" (a.complete && a.out.startsWith "OK " &&
      saved.size == 1 && (← calls count) == 1)
    if let some slot := saved[0]? then
      let cacheDir := cache / "leantex" / "convs"
      let memo ← IO.FS.readFile
        (cacheDir / ("tool-" ++ LeanTex.Core.Flate.contentKey "pdftocairo".toUTF8 ++ ".ver"))
      if let some (stamp, version) := PicCache.readVersionMemo memo then
        -- Freeze the old key and envelope: v1 could record a killed process
        -- as a refusal. Correcting new attempts must also retire that answer.
        let recipe := "pdftocairo -svg -f 1 -l 1 <input> <output>\n<svg preserveAspectRatio=\"none\" "
        let identity := "pdftocairo\n" ++ stamp ++ "\n" ++ version
        let variant := LeanTex.Core.Flate.contentKey (String.intercalate "\u0000"
          ["vector-cache-v1", LeanTex.version, recipe, identity]).toUTF8
        let legacy := cacheDir /
          (((slot.fileName.getD "").take 32 |>.toString) ++ "-" ++ variant ++ ".answer")
        IO.FS.removeFile slot
        IO.FS.writeBinFile legacy (ConvCache.encode (.error "pdftocairo exited 137: interrupted"))
        let b ← run
        let c ← run
        check "cache migration: interrupted v1 answer is retried"
          (b.complete && c.complete && b.out == a.out && c.out == a.out && (← calls count) == 2)
        check "cache migration: replacement is separate and reusable" ((← slots cache).size == 2)
      else check "cache migration: version witness" false
  for (label, tail, expectedRuns, success) in #[
      ("warm", "", 1, true),
      ("refusal", "echo \"${out%/*}/source.pdf: refused input\" >&2\nexit 3\n", 1, false),
      ("silent", "exit 3\n", 2, false),
      ("signal-term", "echo interrupted >&2\nkill -TERM $$\n", 2, false),
      ("signal-kill", "echo interrupted >&2\nkill -KILL $$\n", 2, false),
      ("empty", ": > \"$out\"\n", 2, false),
      ("failed-output", "echo invalid > \"$out\"\necho refused >&2\nexit 3\n", 1, false),
      ("malformed", "echo invalid > \"$out\"\n", 2, false),
      ("truncated", "echo '<svg xmlns=\"http://www.w3.org/2000/svg\">' > \"$out\"\n", 2, false),
      ("pic-malformed", "echo invalid > \"$out\"\n", 2, false)] do
    IO.FS.withTempDir fun dir => do
      let bin := dir / "bin"
      let cache := dir / "cache"
      let count := dir / "count"
      IO.FS.createDirAll bin
      writeTool (bin / "pdftocairo") (stub first tail)
      let run := fun (args : Array String) => RunBounded.runBounded probe.toString args dir 4000 100
        (env := #[("PATH", some (bin.toString ++ ":" ++ path)),
          ("XDG_CACHE_HOME", some cache.toString), ("COUNT", some count.toString)])
      let args := if label == "pic-malformed" then #["pic"] else #[]
      let a ← run args
      let b ← run args
      check s!"{label}: expected answer" (a.complete && b.complete &&
        a.out.startsWith (if success then "OK " else "ERR "))
      check s!"{label}: expected attempts" ((← calls count) == expectedRuns)
      check s!"{label}: exact replay" (a.out == b.out)
      check s!"{label}: only a verdict has a slot" ((← slots cache).size == (if expectedRuns == 1 then 1 else 0))
      if label == "warm" then
        for slot in ← slots cache do IO.FS.writeBinFile slot ByteArray.empty
        let c ← run #[]
        check "empty warm slot: rerun and repair" (c.out == a.out && (← calls count) == 2)
        for slot in ← slots cache do IO.FS.writeFile slot "broken envelope"
        let d ← run #[]
        check "corrupt warm slot: rerun and repair" (d.out == a.out && (← calls count) == 3)
        -- An executable replacement may retain the same version banner.
        writeTool (bin / "pdftocairo") (stub (face "M0 0L30 30L40 40"))
        let e ← run #[]
        check "same-banner replacement: fresh bytes" (e.out != a.out && e.out.startsWith "OK " &&
          (← calls count) == 4)
      if label == "warm" then
        let before ← calls count
        let a ← run #["font"]
        let b ← run #["font"]
        check "unembedded font: still converts without reusing a slot"
          (a.out.startsWith "OK " && b.out == a.out && (← calls count) == before + 2)
  -- exec searches past a non-executable file or a directory. The cache
  -- must follow the tool it reaches, including a same-banner replacement.
  for label in #["non-executable", "directory", "current-directory"] do
    IO.FS.withTempDir fun dir => do
      let shadow := dir / "shadow"
      let bin := dir / "bin"
      let cache := dir / "cache"
      let count := dir / "count"
      IO.FS.createDirAll shadow
      IO.FS.createDirAll bin
      let skipped := shadow / "pdftocairo"
      if label == "directory" then IO.FS.createDir skipped
      else IO.FS.writeFile skipped (stub first)
      writeTool (bin / "pdftocairo") (stub first)
      let selected := if label == "current-directory" then dir / "pdftocairo"
        else bin / "pdftocairo"
      if label == "current-directory" then writeTool selected (stub first)
      let searchPath := (if label == "current-directory" then "" else shadow.toString) ++
        ":" ++ bin.toString
      let run := RunBounded.runBounded probe.toString #[] dir 4000 100
        (env := #[("PATH", some searchPath),
          ("XDG_CACHE_HOME", some cache.toString), ("COUNT", some count.toString)])
      let a ← run
      let b ← run
      check s!"PATH {label}: executable answer is reusable"
        (a.complete && b.complete && a.out.startsWith "OK " && b.out == a.out &&
          (← calls count) == 1 && (← slots cache).size == 1)
      writeTool selected (stub (face "M0 0L30 30L40 40"))
      let c ← run
      let d ← run
      check s!"PATH {label}: actual executable replacement changes the answer"
        (c.complete && d.complete && c.out.startsWith "OK " && c.out != a.out &&
          d.out == c.out && (← calls count) == 2 && (← slots cache).size == 2)
  IO.FS.withTempDir fun dir => do
    let bin := dir / "bin"
    let cache := dir / "cache"
    let count := dir / "count"
    IO.FS.createDirAll bin
    let run := fun (env : Array (String × Option String)) =>
      RunBounded.runBounded probe.toString #[] dir 4000 100
        (env := #[("PATH", some bin.toString), ("XDG_CACHE_HOME", some cache.toString),
          ("COUNT", some count.toString)] ++ env)
    let a ← run #[]
    check "missing tool: no verdict" (a.complete && a.out.startsWith "ERR " && (← slots cache).isEmpty)
    writeTool (bin / "pdftocairo") (stub first)
    let b ← run #[]
    check "restored tool: retries" (b.out.startsWith "OK " && (← calls count) == 1)
    -- A version command that never finishes must not hang a conversion or
    -- grant a cache identity. Its process inherits the same bounded runner.
    writeTool (bin / "pdftocairo") ((stub first).replace "echo 'converter 1'"
      "trap '' TERM; while :; do :; done")
    let start ← IO.monoMsNow
    let c ← run #[]
    let d ← run #[]
    check "unbounded version: no identity, conversion still runs"
      (c.complete && d.complete && c.out == b.out && d.out == b.out &&
        (← calls count) == 3 && (← slots cache).size == 1 &&
        (← IO.monoMsNow) - start < 7500)
  IO.FS.withTempDir fun dir => do
    let bin := dir / "bin"
    let cache := dir / "cache"
    let count := dir / "count"
    IO.FS.createDirAll bin
    writeTool (bin / "pdftocairo") ((stub first).replace "echo C" "/bin/sleep 0.05\necho C")
    let run := RunBounded.runBounded probe.toString #[] dir 4000 100
      (env := #[("PATH", some bin.toString), ("XDG_CACHE_HOME", some cache.toString),
        ("COUNT", some count.toString)])
    let tasks ← (List.range 12).mapM fun _ => IO.asTask run Task.Priority.dedicated
    let results := tasks.map (·.get.toOption)
    let lines := results.filterMap (·.map (·.out))
    check "concurrent writers: every result is whole"
      (results.length == 12 && results.all (·.any (fun r => r.complete && r.out.startsWith "OK ")) &&
        lines.all (· == lines.headD ""))
    let entries ← (cache / "leantex" / "convs").readDir
    let slots ← slots cache
    check "concurrent writers: one verdict and no staging residue"
      (slots.size == 1 && entries.all (fun e => !e.fileName.endsWith ".part"))
    if let some slot := slots[0]? then
      let answer := ConvCache.decode (← IO.FS.readBinFile slot)
      check "concurrent writers: slot is the served bytes"
        (answer.any fun a => match a with
          | .error _ => false
          | .ok b => lines.headD "" == s!"OK {b.size} {LeanTex.Core.Flate.contentKey b}\n")
  if args.contains "--tools" then
    let some converter ← ToolProbe.onPath "rsvg-convert"
      | throw <| IO.userError "rsvg-convert is required for --tools"
    for (label, body, runs) in [
        ("paths", "<path d=\"M0 0L20 20\"/>", 1),
        ("text", "<text x=\"1\" y=\"15\">A</text>", 2),
        ("font-unit", "<rect width=\"1em\" height=\"10\"/>", 2),
        ("encoded-unit", "<rect width=\"1&#101;m\" height=\"10\"/>", 2),
        ("stylesheet", "<style><![CDATA[rect { width: 1em; }]]></style><rect height=\"10\"/>", 2),
        ("inline-style", "<rect style=\"width: 1em\" height=\"10\"/>", 2)] do
      IO.FS.withTempDir fun dir => do
        let bin := dir / "bin"
        let cache := dir / "cache"
        let count := dir / "count"
        IO.FS.createDirAll bin
        writeTool (bin / "rsvg-convert") "#!/bin/sh\n\
if [ \"$1\" != '--version' ]; then echo C >> \"$COUNT\"; fi\n\
exec \"$CONVERTER\" \"$@\"\n"
        let input := dir / "input.svg"
        IO.FS.writeFile input
          ("<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"40\" height=\"40\">" ++ body ++ "</svg>")
        let run := RunBounded.runBounded probe.toString #["svg", input.toString] dir 4000 100
          (env := #[("PATH", some (bin.toString ++ ":" ++ path)),
            ("XDG_CACHE_HOME", some cache.toString), ("COUNT", some count.toString),
            ("CONVERTER", some converter.toString)])
        let a ← run
        let b ← run
        check s!"SVG {label}: font assumptions only control reuse"
          (a.complete && b.complete && a.out.startsWith "OK " && b.out == a.out &&
            (← calls count) == runs && (← slots cache).size == (if runs == 1 then 1 else 0))
  let failed ← failures.get
  for name in failed do IO.eprintln s!"FAIL: {name}"
  IO.println s!"conversion cache IO checks: {failed.size} failures"
  return if failed.isEmpty then 0 else 1
