/-! The conversion-cache IO oracle: real processes over the real
`ImageAssets`/`ConvCache` slot machinery, driven with local executable
stubs and a temporary cache, so it needs no installed converter and no
network. It proves the properties that live in IO, not in a pure theorem:

* **B1 — concurrent writers never publish an incomplete byte.** Many builds
  race to fill one slot through `picFace`; every one is served a whole,
  identical file, exactly one output slot lands, and no `.part` temp
  survives.

Build the `conv-probe` and `conv-child` helpers first (they are ordinary
`lake` executables); this oracle spawns them.
-/

/-- The probe binary that calls the real `ImageAssets.picFace`. -/
def probeBin : IO System.FilePath := IO.FS.realPath ".lake/build/bin/convProbe"

/-- Make an executable stub at `path` with the given script body. -/
def writeStub (path : System.FilePath) (body : String) : IO Unit := do
  IO.FS.writeFile path body
  let r ← IO.Process.output { cmd := "chmod", args := #["+x", path.toString] }
  unless r.exitCode == 0 do throw <| IO.userError s!"chmod failed for {path}"

/-- A stub `pdftocairo`: names the given version on `-v`, else sleeps
briefly (to widen the fill race) and writes the given payload to its output
argument. Version and payload are baked into the script text so that a
different one changes the file's stat witness — an upgrade the tool-version
memo must notice. -/
def pdftocairoStub (version payload : String) : String :=
  "#!/bin/sh\n\
for a in \"$@\"; do\n\
  if [ \"$a\" = \"-v\" ]; then echo \"" ++ version ++ "\"; exit 0; fi\n\
done\n\
out=\"\"\n\
for a in \"$@\"; do out=\"$a\"; done\n\
sleep 0.05\n\
printf '" ++ payload ++ "' > \"$out\"\n\
exit 0\n"

/-- The default stub used by the concurrency and empty-warmed checks. -/
def defaultStub : String :=
  pdftocairoStub "pdftocairo 99.0 (leantex conv-cache-io stub)"
    "STUBSVG-0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789"

private def check (ref : IO.Ref (List String)) (name : String) (ok : Bool) : IO Unit :=
  unless ok do ref.modify (name :: ·)

/-- Spawn `n` probes concurrently, all sharing one cache and one stub
`pdftocairo`, and hold the atomic-publish contract to what every writer was
served and what the slot directory holds afterward. -/
def concurrentWriteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let probe ← probeBin
  let path := (← IO.getEnv "PATH").getD ""
  IO.FS.withTempDir fun dir => do
    let bin := dir / "bin"
    IO.FS.createDirAll bin
    writeStub (bin / "pdftocairo") defaultStub
    let cache := dir / "cache"
    IO.FS.createDirAll cache
    let env := #[("PATH", some (bin.toString ++ ":" ++ path)),
      ("XDG_CACHE_HOME", some cache.toString)]
    let n := 16
    let tasks ← (List.range n).mapM fun _ =>
      IO.asTask (IO.Process.output { cmd := probe.toString, env }) Task.Priority.dedicated
    let results ← tasks.mapM fun t => pure (t.get)
    let outs := results.filterMap (·.toOption)
    check ref "every concurrent probe completed" (outs.length == n)
    let lines := outs.map (·.stdout.trimAscii.toString)
    check ref "every probe was served a conversion (no error)"
      (lines.all (·.startsWith "OK "))
    let distinct := (lines.foldl (fun s l => if s.contains l then s else l :: s) ([] : List String))
    -- Every writer must have been served the identical whole file: one
    -- distinct "OK <len> <checksum>" line across all racers.
    check ref "every probe served the identical whole bytes" (distinct.length == 1)
    let convs := cache / "leantex" / "convs"
    let entries ← try (← convs.readDir).toList.mapM (fun e => pure e.fileName)
      catch _ => pure []
    let outSlots := entries.filter (·.endsWith ".out")
    let partSlots := entries.filter (·.endsWith ".part")
    check ref "exactly one output slot was published" (outSlots.length == 1)
    check ref "no leftover .part temp survived any writer" (partSlots.isEmpty)
    -- The published slot is the whole payload every probe was served, never
    -- a prefix: its size equals the length each probe reported.
    let servedLen := ((lines.head?.getD "").splitOn " ")[1]?.bind (·.toNat?)
    match outSlots, servedLen with
    | [name], some len =>
      let bytes ← IO.FS.readBinFile (convs / name)
      check ref "the published slot holds the whole served payload"
        (bytes.size == len && len > 0)
    | _, _ => check ref "the published slot holds the whole served payload" false

/-- A warmed slot whose output went empty (a truncated file, or a half-written
byte from a writer that died before atomic staging existed) is not a hit:
the next build re-runs the tool and republishes a whole file, rather than
serving nothing. -/
def emptyWarmedChecks (ref : IO.Ref (List String)) : IO Unit := do
  let probe ← probeBin
  let path := (← IO.getEnv "PATH").getD ""
  IO.FS.withTempDir fun dir => do
    let bin := dir / "bin"
    IO.FS.createDirAll bin
    writeStub (bin / "pdftocairo") defaultStub
    let cache := dir / "cache"
    IO.FS.createDirAll cache
    let env := #[("PATH", some (bin.toString ++ ":" ++ path)),
      ("XDG_CACHE_HOME", some cache.toString)]
    let convs := cache / "leantex" / "convs"
    let first ← IO.Process.output { cmd := probe.toString, env }
    check ref "empty-warmed: first run warms the slot" (first.exitCode == 0)
    let outSlots := ((← convs.readDir).toList.map (·.fileName)).filter (·.endsWith ".out")
    match outSlots with
    | [name] =>
      IO.FS.writeBinFile (convs / name) ByteArray.empty
      let second ← IO.Process.output { cmd := probe.toString, env }
      check ref "empty-warmed: an emptied slot re-runs and is served whole"
        (second.exitCode == 0 && second.stdout.trimAscii.toString.startsWith "OK ")
      let bytes ← IO.FS.readBinFile (convs / name)
      check ref "empty-warmed: the republished slot is non-empty" (!bytes.isEmpty)
    | _ => check ref "empty-warmed: exactly one slot warmed" false

/-- **M1 — a timeout kills a TERM-ignoring descendant that holds the pipes,
and never hangs the build.** The stub's leader and a grandchild both trap
`SIGTERM` and sleep far past the budget, and the grandchild inherits the
pipes; only the group `SIGKILL` after grace can reap them, and only the
bounded drains keep the held pipe from hanging the reader. The probe must
return well under the descendants' own sleep, and afterward no stub process
may survive. -/
def timeoutKillChecks (ref : IO.Ref (List String)) : IO Unit := do
  let probe ← IO.FS.realPath ".lake/build/bin/runBoundProbe"
  IO.FS.withTempDir fun dir => do
    let marker := dir / "marker"
    IO.FS.createDirAll marker
    let stub := dir / "hang"
    -- Leader and grandchild both ignore TERM and sleep 30 s; the grandchild
    -- holds the inherited stdout/stderr. Each records its pid.
    writeStub stub <|
      "#!/bin/sh\n\
echo \"$$\" > \"" ++ (marker / "leader.pid").toString ++ "\"\n\
sh -c 'trap \"\" TERM; echo \"$$\" > \"" ++ (marker / "grandchild.pid").toString ++
        "\"; sleep 30' &\n\
trap \"\" TERM\n\
sleep 30\n"
    let t0 ← IO.monoMsNow
    let run ← IO.Process.output { cmd := probe.toString, args := #[stub.toString] }
    let dt := (← IO.monoMsNow) - t0
    check ref "timeout: the probe returned (no hang on the held pipe)" (run.exitCode == 0)
    -- The stub descendants sleep 30 s; a budget of 0.4 s + 0.3 s grace means
    -- a correct run returns in ~1 s. Allow generous slack, but far under 30 s.
    check ref "timeout: returned far under the descendants' 30 s sleep" (dt < 10000)
    check ref "timeout: the run is reported as an overrun"
      (run.stdout.trimAscii.toString.startsWith "RAN LeanTex.Cli.PicCache.Ran.overran")
    -- No stub process survives: both recorded pids are gone.
    let alive (pidFile : System.FilePath) : IO Bool := do
      match ← (IO.FS.readFile pidFile).toBaseIO with
      | .error _ => return false
      | .ok s =>
        let pid := s.trimAscii.toString
        if pid.isEmpty then return false
        let r ← IO.Process.output { cmd := "kill", args := #["-0", pid] }
        return r.exitCode == 0
    -- Give the OS a moment to finish reaping after SIGKILL.
    IO.sleep 300
    check ref "timeout: no TERM-ignoring leader survived" (!(← alive (marker / "leader.pid")))
    check ref "timeout: no TERM-ignoring grandchild survived"
      (!(← alive (marker / "grandchild.pid")))

/-- **M5 — a picture face is served from its tool-versioned slot, never a
stale sibling.** The M5 defect served the `.svg` beside the PDF whenever it
existed, keyed only by the lualatex picture key, so an upgraded `pdftocairo`
kept painting the old face. `picFace` keys the slot on the tool's version,
so warming under one version and then upgrading the tool must yield fresh
bytes, not the warm ones. -/
def toolUpgradeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let probe ← probeBin
  let path := (← IO.getEnv "PATH").getD ""
  IO.FS.withTempDir fun dir => do
    let bin := dir / "bin"
    IO.FS.createDirAll bin
    let cache := dir / "cache"
    IO.FS.createDirAll cache
    let env := #[("PATH", some (bin.toString ++ ":" ++ path)),
      ("XDG_CACHE_HOME", some cache.toString)]
    -- Warm the slot under version 1.
    writeStub (bin / "pdftocairo") (pdftocairoStub "pdftocairo 1.0" "FACE-ONE-PAYLOAD")
    let first ← IO.Process.output { cmd := probe.toString, env }
    let firstLine := first.stdout.trimAscii.toString
    check ref "tool-upgrade: first version converts" (firstLine.startsWith "OK ")
    -- Upgrade the tool: a new binary content (version and payload), so its
    -- stat witness changes and the version memo re-probes.
    IO.sleep 1100
    writeStub (bin / "pdftocairo") (pdftocairoStub "pdftocairo 2.0" "FACE-TWO-PADDING!")
    let second ← IO.Process.output { cmd := probe.toString, env }
    let secondLine := second.stdout.trimAscii.toString
    check ref "tool-upgrade: second version converts" (secondLine.startsWith "OK ")
    -- The two payloads differ in length, so the reported "OK <len> <sum>"
    -- lines must differ: the upgrade was not served the stale face.
    check ref "tool-upgrade: an upgraded tool is not served the stale face"
      (firstLine != secondLine)
    -- Both slots coexist, keyed by version.
    let convs := cache / "leantex" / "convs"
    let outs := ((← convs.readDir).toList.map (·.fileName)).filter (·.endsWith ".out")
    check ref "tool-upgrade: each version keeps its own slot" (outs.length == 2)

def main : IO UInt32 := do
  let ref ← IO.mkRef ([] : List String)
  concurrentWriteChecks ref
  emptyWarmedChecks ref
  timeoutKillChecks ref
  toolUpgradeChecks ref
  let failed ← ref.get
  for name in failed.reverse do IO.eprintln s!"FAIL: {name}"
  IO.println s!"conversion-cache IO oracle: {failed.length} failures"
  return if failed.isEmpty then 0 else 1
