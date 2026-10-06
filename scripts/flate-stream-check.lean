import LeanTex.Core.Flate

/-!
Focused compression regression check, independent of the document engine:
`lake env lean --run scripts/flate-stream-check.lean`.

Checks both directions against Python's zlib, fixed/dynamic/stored blocks,
the caller's output bound, and truncated streams. Printed compressed hashes
also let a factorization be compared with its preceding implementation.
This is an executable check; universal codec contracts live under Core/Flate.
-/

open LeanTex.Core

private def fail (message : String) : IO α :=
  throw (IO.userError s!"flate-stream-check: {message}")

private def samples : Array (String × ByteArray) := Id.run do
  let mut cases := #[
    ("empty", ByteArray.empty),
    ("one", ByteArray.mk #[42]),
    ("two", ByteArray.mk #[0, 255]),
    ("alphabet", ByteArray.mk (Array.ofFn (n := 256) fun i => UInt8.ofNat i)),
    ("long-run", ByteArray.mk (Array.replicate 70000 7)),
    ("period-three", ByteArray.mk (Array.ofFn (n := 4097) fun i => UInt8.ofNat (i % 3))),
    ("text", (String.join (List.replicate 100
      "A small stream carries literal bytes and repeated phrases. ")).toUTF8)]
  let mut seed : UInt64 := 0x71349512A31762BF
  for size in #[17, 258, 1025, 32767, 32768, 65535, 65536] do
    let mut bytes := ByteArray.emptyWithCapacity size
    for _ in [0:size] do
      seed := seed ^^^ (seed >>> 12)
      seed := seed ^^^ (seed <<< 25)
      seed := seed ^^^ (seed >>> 27)
      bytes := bytes.push (seed * 2685821657736338717).toUInt8
    cases := cases.push (s!"random-{size}", bytes)
  return cases

private def check (dir : System.FilePath) (label : String) (raw : ByteArray) : IO Unit := do
  let encoded := Flate.deflate raw
  match Flate.inflate encoded raw.size with
  | .ok out => unless out == raw do fail s!"{label}: own round trip"
  | .error e => fail s!"{label}: own decoder: {e}"
  if raw.size > 0 then
    match Flate.inflate encoded (raw.size - 1) with
    | .error _ => pure ()
    | .ok _ => fail s!"{label}: output bound"
  IO.FS.writeBinFile (dir / "raw") raw
  IO.FS.writeBinFile (dir / "encoded") encoded
  let python ← IO.Process.output {
    cmd := "python3"
    args := #["-c",
      "import pathlib,sys,zlib\np=pathlib.Path(sys.argv[1])\nr=(p/'raw').read_bytes()\nassert zlib.decompress((p/'encoded').read_bytes())==r\nfor level in (0,1,9):\n (p/str(level)).write_bytes(zlib.compress(r,level))\nc=zlib.compressobj(strategy=zlib.Z_FIXED)\n(p/'fixed').write_bytes(c.compress(r)+c.flush())",
      dir.toString] }
  unless python.exitCode == 0 do
    fail s!"{label}: foreign codec: {python.stderr}"
  for mode in #["0", "1", "9", "fixed"] do
    let foreign ← IO.FS.readBinFile (dir / mode)
    match Flate.inflate foreign raw.size with
    | .ok out => unless out == raw do fail s!"{label}: foreign stream {mode}"
    | .error e => fail s!"{label}: foreign stream {mode}: {e}"
  for size in [0:min encoded.size 32] do
    match Flate.inflate (encoded.extract 0 size) raw.size with
    | .error _ => pure ()
    | .ok out =>
      -- The decoder intentionally does not require the Adler trailer.
      unless out == raw do fail s!"{label}: truncated stream returned different bytes"
  IO.println s!"{label}\t{encoded.size}\t{Flate.contentKey encoded}"

def main : IO Unit := do
  let dir ← IO.FS.createTempDir
  try
    for (label, raw) in samples do check dir label raw
    IO.println "flate-stream-check: passed"
  finally
    IO.FS.removeDirAll dir
