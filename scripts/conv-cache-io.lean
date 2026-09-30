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

/-- A stub `pdftocairo`: names a version on `-v`, else sleeps briefly (to
widen the fill race) and writes a fixed 64-byte payload to its output
argument. -/
def pdftocairoStub : String :=
  "#!/bin/sh\n\
for a in \"$@\"; do\n\
  if [ \"$a\" = \"-v\" ]; then echo \"pdftocairo 99.0 (leantex conv-cache-io stub)\"; exit 0; fi\n\
done\n\
out=\"\"\n\
for a in \"$@\"; do out=\"$a\"; done\n\
sleep 0.05\n\
printf 'STUBSVG-0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789' > \"$out\"\n\
exit 0\n"

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
    writeStub (bin / "pdftocairo") pdftocairoStub
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
    writeStub (bin / "pdftocairo") pdftocairoStub
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

def main : IO UInt32 := do
  let ref ← IO.mkRef ([] : List String)
  concurrentWriteChecks ref
  emptyWarmedChecks ref
  let failed ← ref.get
  for name in failed.reverse do IO.eprintln s!"FAIL: {name}"
  IO.println s!"conversion-cache IO oracle: {failed.length} failures"
  return if failed.isEmpty then 0 else 1
