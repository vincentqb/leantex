import LeanTex.Cli.ImageAssets
import Tests.Support

open LeanTex.Cli

namespace Tests

/-- The child removes only its fresh, empty working directory. The suite's
cwd and environment remain unchanged while other IO checks run. -/
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
  check ref s!"cache identity/{stage}: an unavailable cwd supplies no witness"
    (match stamp with | .ok "" => true | _ => false)
  let validated ← (ImageAssets.validateSvg (svgDocument "")).toBaseIO
  check ref s!"cache identity/{stage}: SVG validation returns an inner error"
    (match validated with | .ok (.error why) => !why.isEmpty | _ => false)
  let some cache ← IO.getEnv "XDG_CACHE_HOME" |
    throw <| IO.userError "missing isolated cache root"
  let entries ← (System.FilePath.mk cache / "leantex" / "convs").readDir
  check ref s!"cache identity/{stage}: an unavailable identity publishes no answer"
    (entries.all fun entry => !entry.fileName.endsWith ".answer")
  let failed ← ref.get
  for message in failed.reverse do IO.eprintln message
  IO.println s!"cache identity/{stage}: {failed.length} failures"
  return if failed.isEmpty then 0 else 1

/-- Optional identity IO may prevent caching, but must neither bypass the
producer nor turn its answer into an IO exception. -/
def cacheIdentityChecks (ref : IO.Ref (List String)) : IO Unit := do
  let some lean ← ToolProbe.onPath "lean" |
    throw <| IO.userError "cache identity checks require the Lean interpreter"
  let libraries ← IO.FS.realPath ".lake/build/lib/lean"
  let leanPath := libraries.toString ++ ":" ++ (← IO.getEnv "LEAN_PATH").getD ""
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
      let result ← RunBounded.runBounded lean.toString
        #["--run", driver.toString, cwd.toString, stage] cwd 10000 100
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

end Tests
