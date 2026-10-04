import Tests.Support

open LeanTex.Core

private def repeatedControls (name : String) (count : Nat) : Array Parse.Raw := Id.run do
  let pos : Pos := {}
  let mut body := #[]
  for _ in [:count] do
    body := body.push (.ctrl name pos) |>.push (.group #[.word "type" pos] pos) |>.push .space
  return #[.env "document" body pos]

@[noinline] private def executeControls (raws : Array Parse.Raw) : IO (Array Parse.Raw) :=
  pure (Compat.execute "compat-execution.tex" raws).raws

private def controlAllocations (raws : Array Parse.Raw) : IO (Nat × Array Parse.Raw) := do
  let before ← IO.getNumHeartbeats
  let actual ← executeControls raws
  let after ← IO.getNumHeartbeats
  return (after - before, actual)

/-- Execution preserves the emitted stream and processes each prefix once.
Doubling linear work tends to 2× allocations, prefix replay to 4×; 3×
separates those growth rates without depending on the host's elapsed time. -/
def compatExecutionChecks (ref : IO.Ref (List String)) : IO Unit := do
  for name in ["underline", "textbf", "plain"] do
    let small := repeatedControls name 128
    let large := repeatedControls name 256
    let (smallCost, smallOut) ← controlAllocations small
    let (largeCost, largeOut) ← controlAllocations large
    check ref s!"execution/{name}/exact-small" (smallOut == small)
    check ref s!"execution/{name}/exact-large" (largeOut == large)
    check ref s!"execution/{name}/linear-allocation-growth" (largeCost < 3 * smallCost)
