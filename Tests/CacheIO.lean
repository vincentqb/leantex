module

public import LeanTex.Cli.ImageAssets
public import Tests.Support
public import LeanTex.Cli.RunBounded
import LeanTex.Core.SlotRecord
import LeanTex.Core.FigureFace

public section

open LeanTex.Cli

namespace Tests

/-- The child removes only its fresh, empty working directory, leaving the suite's cwd and
environment unchanged. -/
def runCacheCwdChild (args : List String) : IO UInt32 := do
  let [owned, stage] := args |
    throw <| IO.userError "expected the owned working directory and removal stage"
  let cwd ← IO.currentDir
  unless cwd.toString == owned && (stage == "before" || stage == "after") do
    throw <| IO.userError "refusing to remove an unowned working directory"
  let ref ← IO.mkRef ([] : List String)
  let expected := "synthetic conversion answer".toUTF8
  let calls ← IO.mkRef (0 : Nat)
  if stage == "before" then IO.FS.removeDir cwd
  let answer ← (ConvCache.cached "synthetic source".toUTF8 "deleted-cwd"
      #["cache-identity-tool"] true do
    calls.modify (· + 1)
    if stage == "after" then IO.FS.removeDir cwd
    return ({ outcome := .drawn, bytes := expected }, true)).toBaseIO
  check ref s!"cache identity/{stage}: the producer runs once and its answer survives"
    ((← calls.get) == 1 && match answer with
      | .ok (.ok bytes) => bytes == expected
      | _ => false)
  check ref s!"cache identity/{stage}: the working directory was actually removed"
    (match ← IO.currentDir.toBaseIO with | .error _ => true | .ok _ => false)
  let stamp ← (ToolProbe.witness "cache-identity-tool").toBaseIO
  check ref s!"cache identity/{stage}: an unavailable cwd still resolves an absolute PATH entry"
    (match stamp with | .ok s => !s.isEmpty | .error _ => false)
  let relative ← (World.ToolPath.witness "cache-identity-tool").runM (m := BaseIO) fun q =>
    match q with | .env "PATH" => pure (some "../bin") | q => Host.answer q
  check ref s!"cache identity/{stage}: an unavailable cwd gives a relative PATH entry no witness"
    relative.isEmpty
  let converted ← (ImageAssets.canonicalPoster (svgDocument "")).toBaseIO
  check ref s!"cache identity/{stage}: an SVG conversion returns an inner error"
    (match converted with | .ok (.error why) => !why.isEmpty | _ => false)
  let some cache ← IO.getEnv "XDG_CACHE_HOME" |
    throw <| IO.userError "missing isolated cache root"
  let entries ← (System.FilePath.mk cache / "leantex" / "convs").readDir
  check ref s!"cache identity/{stage}: an answer is published exactly when its identity held across the attempt"
    ((entries.any fun entry => entry.fileName.endsWith ".answer") == (stage == "after"))
  let failed ← ref.get
  for message in failed.reverse do IO.eprintln message
  IO.println s!"cache identity/{stage}: {failed.length} failures"
  return if failed.isEmpty then 0 else 1

/-- Optional identity IO may prevent caching but neither bypasses the producer nor turns its answer
into an exception. -/
def cacheIdentityChecks (ref : IO.Ref (List String)) : IO Unit := do
  let (lean, leanPath) ← leanChild "cache identity checks"
  for stage in #["before", "after"] do
    IO.FS.withTempDir fun dir => do
      let cwd := dir / "cwd"
      let bin := dir / "bin"
      IO.FS.createDir cwd
      IO.FS.createDir bin
      let tool := bin / "cache-identity-tool"
      IO.FS.writeFile tool "#!/bin/sh\nprintf '%s\\n' 'cache identity test 1'\n"
      IO.setAccessRights tool { user := ⟨true, true, true⟩ }
      let driver := dir / "probe.lean"
      IO.FS.writeFile driver
        "import Tests.CacheIO\n\
         def main (args : List String) : IO UInt32 := Tests.runCacheCwdChild args\n"
      let result ← childRun 1200 lean.toString
        #["--run", driver.toString, cwd.toString, stage] cwd
        (env := #[("PATH", some bin.toString), ("LEAN_PATH", some leanPath),
          ("XDG_CACHE_HOME", some (dir / "cache").toString)])
      check ref s!"cache identity/{stage}: isolated IO contracts\n{result.out}{result.err}"
        (result.complete && result.ran == .exited 0)
  let thrown ← (ConvCache.cached ByteArray.empty "producer-error" #[] false
    (throw <| IO.userError "synthetic producer error")).toBaseIO
  check ref "cache identity: producer IO errors remain the producer's errors"
    (match thrown with
      | .error e => e.toString == (IO.userError "synthetic producer error").toString
      | .ok _ => false)

/-- The cache records' bytes, pinned: a slot and the two kinds of face answer encode as they always
have, so a cache written by one build reads in the next. -/
def cacheRecordChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let hex (b : ByteArray) : String := b.foldl (init := "") fun s x =>
    s ++ (if x < 16 then "0" else "") ++ String.ofList (Nat.toDigits 16 x.toNat)
  t "cache records: a slot's bytes" (hex (LeanTex.Core.SlotRecord.encode #["a", "bc"] ⟨#[1, 2, 3]⟩) ==
    "4c54534c4f54310a85f9f7007e8bad890000001600000002000000016100000002626300000003010203")
  t "cache records: an empty slot's bytes" (hex (LeanTex.Core.SlotRecord.encode #[] .empty) ==
    "4c54534c4f54310aa8c7f832281a39c5000000080000000000000000")
  t "cache records: a refused face's bytes"
    (hex (LeanTex.Core.FigureFace.encode #["k"] (.error "why")) ==
      "4c5446414345320aa461188c3315caa70000001100000001000000016b0000000003776879")
  t "cache records: a drawn face's bytes"
    (hex (LeanTex.Core.FigureFace.encode #["k1", "k2"]
      (.ok { losses := #[.element "e", .font "f", .budget "b"], face := ⟨#[9, 8]⟩, words := "w" })) ==
      "4c5446414345320a4f2bb7609540b0ac0000003200000002000000026b31000000026b32010000000300000000016506" ++
      "00000001660700000001620000000209080000000177")

end Tests
