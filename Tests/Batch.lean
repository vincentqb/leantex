module

public import LeanTex.Cli.Batch
public import Std.Sync.Mutex
public import Tests.Support

public section

open LeanTex.Cli

namespace Tests

private structure Running where
  keys : List Nat := []
  peak : Nat := 0
  collision : Bool := false
  started : Array Nat := #[]
  finished : Array Nat := #[]

/-- Exercise the IO consumer of the proved partition: actual overlap,
exclusive cache ownership, stable answers, and draining after exceptions. -/
def batchChecks (ref : IO.Ref (List String)) : IO Unit := do
  for limit in #[0, 1, 2, 4] do
    let state ← Std.Mutex.new ({} : Running)
    let input := #[0, 1, 0, 2, 3, 2, 4, 5]
    let out ← Batch.map limit id (fun key => do
      state.atomically do
        modify fun s => { s with
          collision := s.collision || s.keys.contains key
          keys := key :: s.keys
          peak := max s.peak (s.keys.length + 1)
          started := s.started.push key }
      IO.sleep 10
      state.atomically do
        modify fun s => { s with keys := s.keys.erase key, finished := s.finished.push key }
      return key + 10) input
    let seen ← state.atomically get
    check ref s!"batch {limit}: preserves source order despite duplicate keys"
      (out == input.map (· + 10))
    check ref s!"batch {limit}: bounds concurrent work and owns each key once"
      (!seen.collision && seen.peak ≤ max 1 limit && seen.keys.isEmpty &&
        seen.finished.size == input.size)

  -- The first task waits for the second to start. This observes overlap
  -- without making a speed claim or depending on one task's sleep duration.
  let started ← Std.Mutex.new (0 : Nat)
  let overlap ← Batch.map 2 id (fun key => do
    started.atomically (modify (· + 1))
    let mut together := false
    for _ in [:1000] do
      if (← started.atomically get) == 2 then
        together := true
        break
      IO.sleep 1
    return (key, together)) #[0, 1]
  check ref "batch: independent requests really run concurrently"
    (overlap == #[(0, true), (1, true)])

  let state ← Std.Mutex.new ({} : Running)
  let ending ← (Batch.map 3 id (fun key => do
    state.atomically do
      modify fun s => { s with keys := key :: s.keys, started := s.started.push key }
    try
      if key == 0 then throw (IO.userError "invented task failure")
      IO.sleep 20
      return key
    finally
      state.atomically do
        modify fun s => { s with keys := s.keys.erase key, finished := s.finished.push key }
    ) #[0, 1, 2, 3]).toBaseIO
  let seen ← state.atomically get
  check ref "batch: errors join every started writer before returning"
    ((match ending with | .error _ => true | .ok _ => false) &&
      seen.keys.isEmpty && seen.finished.size == 3 &&
      !seen.started.contains 3)

end Tests
