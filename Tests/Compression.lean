import LeanTex.Cli.Compression
import LeanTex.Cli.ConvCache
import Tests.Support

open LeanTex.Core LeanTex.Cli

namespace Tests

private structure Compressing where
  active : List System.FilePath := []
  peak : Nat := 0
  collision : Bool := false
  started : Array ByteArray := #[]
  finished : Array ByteArray := #[]

private def compressionConcurrencyChecks (ref : IO.Ref (List String)) : IO Unit := do
  let a := "q\n0 0 10 10 re f\nQ\n".toUTF8
  let b := "q\n1 0 0 1 20 30 cm\nQ\n".toUTF8
  let c := bytes [0, 255, 0, 128, 3, 0, 42]
  let inputs := #[a, b, a, c, b]
  let programs := inputs.map (·, false)
  for fonts in #[false, true] do
    let kind := if fonts then "fonts" else "pages"
    for limit in #[0, 1, 2, 4] do
      let state ← Std.Mutex.new ({} : Compressing)
      let compute := fun input => do
        let key := Compression.cachePath "." input
        state.atomically do
          modify fun s => { s with
            collision := s.collision || s.active.contains key
            active := key :: s.active
            peak := max s.peak (s.active.length + 1)
            started := s.started.push input }
        IO.sleep (if input == a then 12 else 1)
        let z := Flate.deflate input
        state.atomically do
          modify fun s => { s with
            active := s.active.erase key, finished := s.finished.push input }
        return z
      if fonts then
        let got ← Compression.fontZdata none 4 #[3, 1, 2, 3, 0] programs limit compute
        check ref s!"compression {kind}/{limit}: keeps font indices and last assignment"
          (got == #[some (Flate.deflate b), some (Flate.deflate b),
            some (Flate.deflate a), some (Flate.deflate c)])
      else
        let got ← Compression.pageStreams none inputs limit compute
        check ref s!"compression {kind}/{limit}: keeps each raw and compressed pair in source order"
          (got == inputs.map (fun input => (input, some (Flate.deflate input))))
      let seen ← state.atomically get
      check ref s!"compression {kind}/{limit}: bounded tasks serialize actual cache paths"
        (!seen.collision && seen.peak ≤ max 1 limit &&
          seen.active.isEmpty && seen.finished.size == inputs.size)
      check ref s!"compression {kind}/{limit}: small computations stay serial"
        (seen.peak == 1)

    -- Exercise the task path above the compressor's larger-table boundary.
    let padding := ByteArray.mk (Array.replicate 65536 0)
    let largeA := a ++ padding
    let largeB := b ++ padding
    let largeC := c ++ padding
    let state ← Std.Mutex.new ({} : Compressing)
    let overlapped ← Std.Mutex.new (0 : Nat)
    let compute := fun input => do
      let key := Compression.cachePath "." input
      state.atomically do
        modify fun s => { s with
          collision := s.collision || s.active.contains key
          active := key :: s.active
          peak := max s.peak (s.active.length + 1)
          started := s.started.push input }
      try
        for _ in [:1000] do
          if (← state.atomically get).started.size ≥ 2 then
            overlapped.atomically (modify (· + 1))
            break
          IO.sleep 1
        return input
      finally
        state.atomically do
          modify fun s => { s with
            active := s.active.erase key, finished := s.finished.push input }
    if fonts then
      let got ← Compression.fontZdata none 2 #[1, 0, 1, 0]
        #[(largeA, false), (largeB, true), (largeA, true), (largeB, false)] 2 compute
      check ref "compression large fonts: source indices survive task completion order"
        (got == #[some largeB, some largeA])
    else
      let got ← Compression.pageStreams none #[largeA, largeB, largeA, largeB] 2 compute
      check ref "compression large pages: pairs survive task completion order"
        (got == #[largeA, largeB, largeA, largeB].map (fun input => (input, some input)))
    let seen ← state.atomically get
    check ref s!"compression {kind}: large computations overlap with bounded, distinct cache paths"
      ((← overlapped.atomically get) == 4 && seen.peak == 2 &&
        !seen.collision && seen.active.isEmpty && seen.finished.size == 4)

    for (a, b, c) in #[(a, b, c), (largeA, largeB, largeC)] do
      let state ← Std.Mutex.new ({} : Compressing)
      let d := "not started after failure".toUTF8
      let compute := fun input => do
        let key := Compression.cachePath "." input
        state.atomically do
          modify fun s => { s with active := key :: s.active, started := s.started.push input }
        try
          if input == a then
            IO.sleep 20
            throw (IO.userError "first source failure")
          if input == b then throw (IO.userError "second source failure")
          IO.sleep 10
          return Flate.deflate input
        finally
          state.atomically do
            modify fun s => { s with
              active := s.active.erase key, finished := s.finished.push input }
      let ending ← (do
        if fonts then
          discard <| Compression.fontZdata none 4 #[0, 1, 2, 3]
            (#[(a, false), (b, true), (c, false), (d, false)]) 3 compute
        else
          discard <| Compression.pageStreams none #[a, b, c, d] 3 compute).toBaseIO
      let seen ← state.atomically get
      check ref s!"compression {kind}/{a.size}: finishes the failed batch with the first source error"
        ((match ending with
          | .error e => e.toString == (IO.userError "first source failure").toString
          | .ok _ => false) && seen.active.isEmpty &&
          seen.finished.size == 3 && !seen.started.contains d)

private def compressionCacheChecks (ref : IO.Ref (List String)) : IO Unit := do
  IO.FS.withTempDir fun dir => do
    let input := "invented compression cache payload".toUTF8
    let expected := Flate.deflate input
    let path := Compression.cachePath dir input
    IO.FS.createDirAll (path.parent.getD dir)
    -- This is all the old header-only reader needed to embed a partial file.
    IO.FS.writeBinFile path (bytes [0x78, 0x9C])
    let calls ← IO.mkRef (0 : Nat)
    let compute := fun b => do
      calls.modify (· + 1)
      return Flate.deflate b
    let recovered ← Compression.deflateCachedAt (some dir) input compute
    check ref "compression cache: a zlib header alone is a miss"
      (recovered == expected && (← calls.get) == 1)
    check ref "compression cache: publishes a checked envelope"
      (ConvCache.decode (← IO.FS.readBinFile path) == some (.ok expected))
    let warm ← Compression.deflateCachedAt (some dir) input
      (fun _ => throw (IO.userError "warm compression cache recomputed"))
    check ref "compression cache: warm bytes exactly match recompression" (warm == expected)

    let encoded := ConvCache.encode (.ok expected)
    for broken in #[encoded.extract 0 (encoded.size - 1),
        ConvCache.encode (.error "not a compressor answer"),
        ConvCache.encode (.ok (bytes [0x78, 0x9C])),
        bytes [0, 1, 2, 3]] do
      IO.FS.writeBinFile path broken
      let got ← Compression.deflateCachedAt (some dir) input compute
      check ref "compression cache: truncated, refused, or malformed entries recompute"
        (got == expected && ConvCache.decode (← IO.FS.readBinFile path) == some (.ok expected))
    check ref "compression cache: each broken entry causes one computation" ((← calls.get) == 5)

    IO.FS.removeFile path
    calls.set 0
    let pages ← Compression.pageStreams (some dir) #[input, input, input] 4 compute
    let fonts ← Compression.fontZdata (some dir) 2 #[1, 0]
      #[(input, false), (input, true)] 4 compute
    check ref "compression cache: repeated pages and font programs reuse one complete slot"
      ((← calls.get) == 1 &&
        pages == Array.replicate 3 (input, some expected) &&
        fonts == Array.replicate 2 (some expected))

    let blocked := dir / "unavailable"
    IO.FS.writeFile blocked "a file cannot be a cache directory"
    let uncached ← Compression.deflateCachedAt (some blocked) input
    check ref "compression cache: cache IO failure preserves the computed bytes" (uncached == expected)

    -- Simultaneous callers can publish to the same slot outside one batch.
    IO.FS.removeFile path
    let started ← Std.Mutex.new (0 : Nat)
    let compute := fun b => do
      started.atomically (modify (· + 1))
      for _ in [:1000] do
        if (← started.atomically get) == 2 then break
        IO.sleep 1
      return Flate.deflate b
    let first ← IO.asTask (Compression.deflateCachedAt (some dir) input compute) .dedicated
    let second ← IO.asTask (Compression.deflateCachedAt (some dir) input compute) .dedicated
    let one ← IO.wait first
    let two ← IO.wait second
    check ref "compression cache: simultaneous publications return complete answers"
      (one.toOption == some expected && two.toOption == some expected &&
        ConvCache.decode (← IO.FS.readBinFile path) == some (.ok expected))
    let entries ← (path.parent.getD dir).readDir
    check ref "compression cache: publication cleans its staging directories"
      (entries.all fun entry => !entry.fileName.endsWith ".part")
    IO.FS.removeFile path
    IO.FS.createDir path
    let unpublished ← Compression.deflateCachedAt (some dir) input
    let entries ← (path.parent.getD dir).readDir
    check ref "compression cache: failed rename falls back and cleans staging"
      (unpublished == expected && entries.all fun entry => !entry.fileName.endsWith ".part")

/-- Guards for the actual compression dispatch and cache boundary. -/
def compressionChecks (ref : IO.Ref (List String)) : IO Unit := do
  let a := bytes [0, 255, 7, 0, 10]
  let b := "synthetic second font program".toUTF8
  let c := "synthetic replacement font program".toUTF8
  let invalid := "must never be compressed".toUTF8
  let calls ← Std.Mutex.new (#[] : Array ByteArray)
  let compute := fun input => do
    calls.atomically (modify (·.push input))
    return Flate.deflate input
  let got ← Compression.fontZdata none 3 #[2, 0, 9, 2, 1]
    #[(a, false), (b, true), (invalid, false), (c, true)] 4 compute
  check ref "compression fonts: zip truncates, invalid indices skip, subset flags do not reorder"
    (got == #[some (Flate.deflate b), none, some (Flate.deflate c)] &&
      !(← calls.atomically get).contains invalid &&
      (← calls.atomically get).size == 3)
  for keep in #[#[], #[9]] do
    let got ← Compression.fontZdata none 0 keep #[(invalid, false)] 4
      (fun _ => throw (IO.userError "unused font was compressed"))
    check ref "compression fonts: no selected fonts starts no computation" got.isEmpty
  let pages ← Compression.pageStreams none #[]
    4 (fun _ => throw (IO.userError "empty page set started a task"))
  check ref "compression pages: empty input starts no computation" pages.isEmpty
  let empty ← Compression.pageStreams none #[ByteArray.empty]
  check ref "compression pages: empty stream preserves exact compressor bytes"
    (empty == #[(ByteArray.empty, some (Flate.deflate ByteArray.empty))])
  compressionConcurrencyChecks ref
  compressionCacheChecks ref

end Tests
