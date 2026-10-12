module

public import LeanTex.Cli.Compression
public import LeanTex.Cli.ConvCache
public import LeanTex.Cli.PlanCache
public import LeanTex.Cli.Engine
public import LeanTex.Cli.Host
public import LeanTex.Core.SlotRecord
public import Tests.Support

public section

open LeanTex.Core LeanTex.Cli

namespace Tests

/-- **A changed engine misses the answers an earlier engine stored**, in each
cache of the engine's own answers: a flate stream, an image plan and a
converter's face answer the engine that wrote them, a slot another engine
wrote is computed afresh and replaced, and the earlier engine then misses
the later one's. The defect keyed all three by the release version, which
every build of a release shares, so a changed compressor or planner was
served an older one's answer. -/
def engineCacheChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  IO.FS.withTempDir fun dir => do
    let a : Engine.Cache := { dir, engine := "invented engine a" }
    let b : Engine.Cache := { dir, engine := "invented engine b" }
    -- A flate stream.
    let input := "an invented page stream".toUTF8
    let calls ← IO.mkRef (0 : Nat)
    let compute := fun bytes => do
      calls.modify (· + 1)
      return Flate.deflate bytes
    let z ← Compression.deflateCachedAt (some a) input compute
    let warm ← Compression.deflateCachedAt (some a) input compute
    t "engine caches: a flate slot answers the engine that wrote it"
      (warm == z && (← calls.get) == 1)
    let later ← Compression.deflateCachedAt (some b) input compute
    t "engine caches: another engine misses a flate slot and deflates afresh"
      (later == z && (← calls.get) == 2)
    let stored ← IO.FS.readBinFile (Compression.cachePath dir input)
    t "engine caches: the flate slot then answers the later engine and not the earlier"
      (SlotRecord.lookup (Compression.slotKey b.engine input) stored == some z &&
        SlotRecord.lookup (Compression.slotKey a.engine input) stored == none)
    discard <| Compression.deflateCachedAt (some a) input compute
    t "engine caches: the earlier engine misses the later one's flate slot" ((← calls.get) == 3)
    -- An image plan: an alpha PNG, whose plan recodes, so it is cached.
    let png ← IO.FS.readBinFile "testdata/corpus/rects-alpha.png"
    let params := Image.PlanParams.default
    let encoded (r : Except String Image.Plan) : Option ByteArray := r.toOption.map Image.encodeBin
    let (first, hit1) ← PlanCache.decodeCached (some a) params png
    let (again, hit2) ← PlanCache.decodeCached (some a) params png
    let (other, hit3) ← PlanCache.decodeCached (some b) params png
    let (back, hit4) ← PlanCache.decodeCached (some a) params png
    t "engine caches: an image plan answers the engine that planned it, and no other"
      ((encoded first).isSome && !hit1 && hit2 && !hit3 && !hit4 &&
        encoded again == encoded first && encoded other == encoded first &&
        encoded back == encoded first)
    -- A converter's face: a synthetic producer, no tool.
    let convs := dir / "convs"
    IO.FS.createDirAll convs
    let produced ← IO.mkRef (0 : Nat)
    let face := "an invented converted face".toUTF8
    let produce : IO (ConvCache.Result × Bool) := do
      produced.modify (· + 1)
      return ({ outcome := .drawn, bytes := face }, true)
    let source := "an invented conversion source".toUTF8
    let convert (engine : String) :=
      ConvCache.cachedResultIn (some convs) (some engine) source "invented recipe" #[] true produce
    let c1 ← convert a.engine
    let c2 ← convert a.engine
    let c3 ← convert b.engine
    let c4 ← convert a.engine
    t "engine caches: a conversion answers the engine that recorded it, and no other"
      ([c1, c2, c3, c4].all (·.answer == .ok face) && (← produced.get) == 3)
  -- An identity reads each of its parts: a binary rebuilt to another size at
  -- the same time is another engine, as one rebuilt at another time is.
  let st : World.Stat :=
    { kind := .file, size := 1000, mtimeSec := 1700000000, mtimeNsec := 5, real := "/opt/a/leantex" }
  t "engine caches: an identity moves with the binary's size alone, its time alone and its path alone"
    ([{ st with size := 1001 }, { st with mtimeSec := 1700000001 }, { st with mtimeNsec := 6 },
      { st with real := "/opt/b/leantex" }].all (Engine.identity · != Engine.identity st))

/-- **A rebuilt engine reads none of an earlier engine's answers**: two
copies of the engine binary, two identities as a rebuild or a replacement
leaves (`Engine.engineId`), build one document over one cache. With every
flate slot the first wrote holding another slot's stream under its own key,
and the image slot another image's plan, the first serves the planted
answers and ships another PDF, while the second ships byte for byte the PDF
a cold build ships. The defect keyed these slots by the release version,
which every build of a release shares, so a planted answer changed another
binary's PDF. -/
def engineIdentityChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let binary ← IO.FS.realPath ".lake/build/bin/leantex"
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  let alpha ← IO.FS.readBinFile "testdata/corpus/rects-alpha.png"
  let flat ← IO.FS.readBinFile "testdata/corpus/rects.png"
  IO.FS.withTempDir fun root => do
    let root ← IO.FS.realPath root
    let program := (← IO.FS.readBinFile binary)
    -- Each copy stands where a build tree keeps the engine, under its own root.
    for name in ["a", "b"] do
      IO.FS.createDirAll (root / name / ".lake/build/bin")
      IO.FS.writeBinFile (root / name / ".lake/build/bin/leantex") program
      IO.setAccessRights (root / name / ".lake/build/bin/leantex") { user := ⟨true, true, true⟩ }
    let identity (name : String) : IO String := do
      match ← Host.answer (.stat (root / name / ".lake/build/bin/leantex").toString) with
      | .ok st => return Engine.identity st
      | .error _ => return ""
    t "engine identity: two copies of the binary are two engines"
      ((← identity "a") != (← identity "b"))
    IO.FS.writeBinFile (root / "figure.png") alpha
    IO.FS.writeFile (root / "doc.tex")
      ("\\documentclass{article}\n\\begin{document}\nA first invented page.\n\\newpage\n" ++
        "A second invented page.\n\n\\includegraphics[alt={Invented rectangles}]{figure}\n" ++
        "\\end{document}\n")
    let build (engine : String) (cache output : String) (more : Array String := #[]) :=
      IO.Process.output {
        cmd := (root / engine / ".lake/build/bin/leantex").toString, cwd := some root,
        args := #["doc.tex", "-o", output] ++ more,
        env := #[("LEANTEX_FONT", some font.toString),
          ("XDG_CACHE_HOME", some (root / cache).toString)] }
    let cold ← build "a" "cold-cache" "cold.pdf"
    let filled ← build "a" "cache" "filled.pdf"
    let coldPdf ← IO.FS.readBinFile (root / "cold.pdf")
    t s!"engine identity: the cold and the filling builds publish ({cold.exitCode}, {filled.exitCode}): {cold.stderr}{filled.stderr}"
      (cold.exitCode == 0 && filled.exitCode == 0 &&
        (← IO.FS.readBinFile (root / "filled.pdf")) == coldPdf)
    -- Over the first engine's cache, the second plans its image afresh: its
    -- images phase reports no cached plan, where the first's warm build does.
    let imagesPhase (run : IO.Process.Output) : List String :=
      (run.stdout.splitOn "\n").filter fun line =>
        hasStr line "\"event\":\"phase\"" && hasStr line "\"name\":\"images\""
    let warmA ← build "a" "cache" "warm.pdf" #["-v", "--porcelain"]
    let probeB ← build "b" "cache" "probe.pdf" #["-v", "--porcelain"]
    t s!"engine identity: the engine that planned the image reads its plan back: {imagesPhase warmA}"
      (warmA.exitCode == 0 && (imagesPhase warmA).length == 1 &&
        (imagesPhase warmA).all (hasStr · "cached"))
    t s!"engine identity: another engine reads no plan the first stored: {imagesPhase probeB}"
      (probeB.exitCode == 0 && (imagesPhase probeB).length == 1 &&
        (imagesPhase probeB).all (!hasStr · "cached") &&
        (← IO.FS.readBinFile (root / "probe.pdf")) == coldPdf)
    -- The first engine's slots again, for the plant.
    let refilled ← build "a" "cache" "refilled.pdf"
    t s!"engine identity: the first engine fills the cache again ({refilled.exitCode})"
      (refilled.exitCode == 0)
    -- Plant: each flate slot holds, under the key it holds now, the stream
    -- the next slot held when the first engine filled the cache, and the
    -- image slot another image's plan under its own key — the same wrong
    -- answers however often it runs.
    let flate := root / "cache" / "leantex" / "flate"
    let imgs := root / "cache" / "leantex" / "imgs"
    let planted := match Image.probe flat >>= Image.plan Image.PlanParams.default with
      | .ok pl => Image.encodeBin pl
      | .error _ => ByteArray.empty
    let slotsIn (dir : System.FilePath) : IO (Array (System.FilePath × Array String × ByteArray)) := do
      let found ← (← dir.readDir).filterMapM fun e => do
        return (SlotRecord.decode (← IO.FS.readBinFile e.path)).map fun (k, p) => (e.path, k, p)
      return found.qsort (·.1.toString < ·.1.toString)
    let filledSlots ← slotsIn flate
    let plant : IO (Nat × Nat) := do
      let slots ← slotsIn flate
      if slots.map (·.1) != filledSlots.map (·.1) then return (0, 0)
      for i in [0:slots.size] do
        let (path, key, _) := slots[i]!
        let (_, _, next) := filledSlots[(i + 1) % filledSlots.size]!
        IO.FS.writeBinFile path (SlotRecord.encode key next)
      let plans ← (← imgs.readDir).filterMapM fun e => do
        return (SlotRecord.decode (← IO.FS.readBinFile e.path)).map (e.path, ·.1)
      for (path, key) in plans do
        IO.FS.writeBinFile path (SlotRecord.encode key planted)
      return (slots.size, plans.size)
    let (flates, images) ← plant
    let wrong ← slotsIn flate
    t s!"engine identity: the first engine left flate slots and an image slot to plant, each now holding another's stream ({flates}, {images})"
      (flates ≥ 2 && images == 1 && !planted.isEmpty &&
        (wrong.zip filledSlots).all fun ((_, _, held), (_, _, filled)) => held != filled)
    let served ← build "a" "cache" "served.pdf"
    t s!"engine identity: the engine that wrote the slots serves what they hold ({served.exitCode}): {served.stderr}"
      (served.exitCode == 0 && (← IO.FS.readBinFile (root / "served.pdf")) != coldPdf)
    discard plant
    let fresh ← build "b" "cache" "fresh.pdf"
    t s!"engine identity: another engine misses every planted slot and ships the cold PDF ({fresh.exitCode}): {fresh.stderr}"
      (fresh.exitCode == 0 && (← IO.FS.readBinFile (root / "fresh.pdf")) == coldPdf)
    -- A rebuild keeps the path: the binary written again in place moves its
    -- modification time, and a longer one its size too. Over slots its
    -- former self wrote and the plant holds, each reads them as another
    -- engine's and ships the cold PDF.
    let engineA := root / "a" / ".lake/build/bin/leantex"
    for (change, bytes) in [("written again", program), ("grown", program.push 0)] do
      discard <| build "a" "cache" "refilled.pdf"
      discard plant
      let before ← identity "a"
      IO.sleep 20
      IO.FS.writeBinFile engineA bytes
      let after ← identity "a"
      let rebuilt ← build "a" "cache" "rebuilt.pdf"
      t s!"engine identity: a binary {change} in place is another engine and ships the cold PDF ({rebuilt.exitCode}): {rebuilt.stderr}"
        (before != after && rebuilt.exitCode == 0 &&
          (← IO.FS.readBinFile (root / "rebuilt.pdf")) == coldPdf)

/-- **A watcher keeps the identity it started as.** A watcher whose first
build reads no cache — it has no document yet — and whose binary is then
replaced at its path, a longer file renamed over it as a relink leaves it,
writes every slot of the rebuild that answers the document under the
identity its binary had when the process started, and none under the
replacement's. The defect: with an identity read per build, or first read
by a build, the watcher read the image it runs as the system names it once
replaced, or the replacement, and either wrote no slot or claimed a binary
that never ran. -/
def engineWatchChecks (ref : IO.Ref (List String))
    (executable : System.FilePath := ".lake/build/bin/leantex") : IO Unit := do
  let t := check ref
  let program ← IO.FS.readBinFile (← IO.FS.realPath executable)
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  let alpha ← IO.FS.readBinFile "testdata/corpus/rects-alpha.png"
  IO.FS.withTempDir fun root => do
    let root ← IO.FS.realPath root
    let engine := root / ".lake/build/bin/leantex"
    let next := root / ".lake/build/bin/leantex.next"
    IO.FS.createDirAll (root / ".lake/build/bin")
    IO.FS.writeBinFile engine program
    IO.setAccessRights engine { user := ⟨true, true, true⟩ }
    let stated : IO String := do
      match ← Host.answer (.stat engine.toString) with
      | .ok st => return Engine.identity st
      | .error _ => return ""
    let started ← stated
    IO.FS.writeBinFile (root / "figure.png") alpha
    let child ← IO.Process.spawn {
      cmd := engine.toString, cwd := some root
      args := #["doc.tex", "-o", "out.pdf", "--porcelain", "--watch"]
      env := #[("XDG_CACHE_HOME", some (root / "cache").toString),
        ("HOME", some (root / "home").toString), ("PATH", some (root / "no-tools").toString),
        ("LEANTEX_FONT", some font.toString), ("LEANTEX_FONT_PATH", none)]
      stdin := .null, stdout := .piped, stderr := .null }
    try
      let first ← watcherSummary child.stdout
      t s!"engine watch: the first build, with no document to read, ends: {first}"
        (first.any (hasStr · "\"ok\":false"))
      IO.FS.writeBinFile next (program.push 0)
      IO.setAccessRights next { user := ⟨true, true, true⟩ }
      IO.FS.rename next engine
      let replaced ← stated
      IO.FS.writeFile (root / "doc.next")
        ("\\documentclass{article}\n\\begin{document}\nAn invented watched page.\n\n" ++
          "\\includegraphics[alt={Invented rectangles}]{figure}\n\\end{document}\n")
      IO.FS.rename (root / "doc.next") (root / "doc.tex")
      let second ← watcherSummary child.stdout
      t s!"engine watch: the rebuild answering the document publishes: {second}"
        (second.any (hasStr · "\"ok\":true"))
      let mut engines : Array String := #[]
      for part in ["flate", "imgs"] do
        let dir := root / "cache" / "leantex" / part
        if ← dir.pathExists then
          for e in ← dir.readDir do
            if let some (key, _) := SlotRecord.decode (← IO.FS.readBinFile e.path) then
              engines := engines.push (key.back?.getD "")
      t s!"engine watch: the rebuild's {engines.size} slots all name the binary the watcher started as, \
none its replacement"
        (started != replaced && !started.isEmpty && engines.size ≥ 2 && engines.all (· == started))
    finally
      try child.kill catch _ => pure ()
      discard child.wait

end Tests
