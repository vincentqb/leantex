import LeanTex.Cli.DriverDiag

/-! The boundary's one host-free decision: what a picture gets when no tool
looked at it. Whether a tool is runnable is a fact about the machine, and
what a tool that ran said is that tool's own words — neither is this
module's. What is this module's is the judgement taken once the answer is
"nothing ran": an earlier render of the same request serves, and where none
exists the placeholder ships and the loss is named. That decision reads a
directory and returns its diagnostic, so a test can run it rather than
restate it, and a driver that stopped naming the loss fails the suite
instead of passing it. -/

namespace LeanTex.Cli.Boundary

open LeanTex.Core

/-- A picture no boundary tool looked at. Any earlier render of the same
request serves — the content hash is the request's meaning, and the tool
version in a slot's name only forces a re-render on upgrade, so a warm
cache needs no tool installed. Where the cache holds none, W0379 names the
loss and the placeholder box ships in its place: one per picture, at its
span, so the census gate can match each to what it lost. A remembered
*refusal* is deliberately not read here — with no tool there is no version
to match it against, and "no tool, no render" is the honest answer. -/
def coldPicture (picDir : System.FilePath) (tool key : String)
    (span : Option Span := none) : IO (Except Diag System.FilePath) := do
  let entries ← picDir.readDir
  let any? := entries.findSome? fun e =>
    if e.fileName.startsWith (key ++ "-") && e.fileName.endsWith ".pdf" then
      some e.path
    else none
  match any? with
  | some cached => return .ok cached
  | none => return .error (DriverDiag.boundaryToolUnavailable tool span)

end LeanTex.Cli.Boundary
