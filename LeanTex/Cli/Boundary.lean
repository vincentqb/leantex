import LeanTex.Cli.DriverDiag
import LeanTex.Core.Ir

/-! The boundary's host-free decisions. Whether a tool is runnable is a fact
about the machine, and what a tool that ran said is that tool's own words —
neither is this module's. What is this module's is the judgement taken once
the answers are in. When "nothing ran", an earlier render of the same
request serves, and where none exists the placeholder ships and the loss is
named (`coldPicture`). When a request was refused either way, a picture the
rendered subset draws in part is withdrawn from the boundary and drawn by
the subset (`withdraw`). Each decision returns its diagnostics, so a test
can run it rather than restate it, and a driver that stopped naming the
loss fails the suite instead of passing it. -/

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

/-- What the boundary's refusals leave standing, once the rendered subset
has been asked to stand in: the picture ids whose requests are withdrawn,
the refusals that still stand, and the notes that say why each withdrawn
picture is drawn by the subset. -/
structure Withdrawal where
  ids : Array String := #[]
  standing : Array (String × Diag) := #[]
  notes : Array Diag := #[]
  deriving Repr

/-- **A refusal withdraws a request the subset can stand in for.** A
refused request whose picture the rendered subset draws in part —
`fallbacks`, by picture id, the elaborator's record — is withdrawn: the
driver elaborates again with its id (`Elab.runPrepared`'s `picWithdrawn`),
the subset's drawing ships with its refusals named, and one N0419 at the
picture's span says why the boundary did not draw it, in the tool's own
words where it ran (`said`, by image source). Every other refusal stands:
a picture the subset draws nothing of keeps W0379's placeholder, or E0382's
failed run. Pure, so the decision is a value a test runs rather than a
sentence about the driver. -/
def withdraw (tool : String) (fallbacks : Array String)
    (refused : Array (String × Diag)) (said : Array (String × String))
    (spans : Array (String × Span)) : Withdrawal :=
  refused.foldl (init := {}) fun w (src, why) =>
    match fallbacks.find? (Ir.picSrcPrefix ++ · == src) with
    | some id =>
      { w with
        ids := w.ids.push id
        notes := w.notes.push (DriverDiag.boundaryWithdrawn tool
          ((said.find? (·.1 == src)).map (·.2)) src ((spans.find? (·.1 == src)).map (·.2))) }
    | none => { w with standing := w.standing.push (src, why) }

end LeanTex.Cli.Boundary
