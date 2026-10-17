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

/-- A changed engine misses the answers an earlier engine stored, in each cache of the engine's own
answers: a flate stream, an image plan and a converter's face. -/
def engineCacheChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  IO.FS.withTempDir fun dir => do
    let a : Engine.Cache := { dir, engine := "invented engine a" }
    let b : Engine.Cache := { dir, engine := "invented engine b" }
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
    -- An alpha PNG's plan recodes, so it is cached.
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
  -- An identity reads each of its parts: size, time and path.
  let st : World.Stat :=
    { kind := .file, size := 1000, mtimeSec := 1700000000, mtimeNsec := 5, real := "/opt/a/leantex" }
  t "engine caches: an identity moves with the binary's size alone, its time alone and its path alone"
    ([{ st with size := 1001 }, { st with mtimeSec := 1700000001 }, { st with mtimeNsec := 6 },
      { st with real := "/opt/b/leantex" }].all (Engine.identity · != Engine.identity st))

/-- Two sources of one content plan once a build, however their fetches are scheduled: a cold
build names both and reads the second's plan from the first's slot. -/
def imageCopyChecks (ref : IO.Ref (List String)) : IO Unit := do
  let font ← IO.FS.realPath "testdata/corpus/fonts/OpenSans-Regular.ttf"
  let alpha ← IO.FS.readBinFile "testdata/corpus/rects-alpha.png"
  IO.FS.withTempDir fun root => do
    IO.FS.writeBinFile (root / "first.png") alpha
    IO.FS.writeBinFile (root / "second.png") alpha
    IO.FS.writeFile (root / "doc.tex")
      ("\\documentclass{article}\n\\begin{document}\n" ++
        "\\includegraphics[alt={Invented rectangles}]{first}\n\n" ++
        "\\includegraphics[alt={The same invented rectangles}]{second}\n\\end{document}\n")
    let run ← engineRun root #["doc.tex", "-o", "doc.pdf", "-v", "--porcelain"] font
      (root / "cache")
    let images := phaseLines run "images"
    check ref s!"image copies: a cold build plans one content once and reads it back: {images}"
      (run.exitCode == 0 && images.length == 1 && images.all (hasStr · "2 files, 1 cached"))

/-- A rebuilt engine reads none of an earlier engine's answers: over planted slots the first engine
ships another PDF while the second ships a cold build's bytes. -/
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
    -- Over the first engine's cache the second plans its image afresh.
    let warmA ← build "a" "cache" "warm.pdf" #["-v", "--porcelain"]
    let probeB ← build "b" "cache" "probe.pdf" #["-v", "--porcelain"]
    t s!"engine identity: the engine that planned the image reads its plan back: {phaseLines warmA "images"}"
      (warmA.exitCode == 0 && (phaseLines warmA "images").length == 1 &&
        (phaseLines warmA "images").all (hasStr · "cached"))
    t s!"engine identity: another engine reads no plan the first stored: {phaseLines probeB "images"}"
      (probeB.exitCode == 0 && (phaseLines probeB "images").length == 1 &&
        (phaseLines probeB "images").all (!hasStr · "cached") &&
        (← IO.FS.readBinFile (root / "probe.pdf")) == coldPdf)
    let refilled ← build "a" "cache" "refilled.pdf"
    t s!"engine identity: the first engine fills the cache again ({refilled.exitCode})"
      (refilled.exitCode == 0)
    -- Each flate slot holds the next slot's earlier stream, the image slot another image's plan.
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
    -- A rebuild in place moves the binary's modification time, and a longer one its size too.
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

/-- A watcher keeps the identity it started as: after its binary is replaced, it writes every slot
under its starting identity. -/
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
