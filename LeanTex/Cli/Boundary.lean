import LeanTex.Cli.DriverDiag
import LeanTex.Cli.PicCache
import LeanTex.Cli.PictureAssets
import LeanTex.Core.Ir

/-! The boundary's host-free decisions. Whether a tool is runnable is a fact
about the machine, and what a tool that ran said is that tool's own words —
neither is this module's. What is this module's is the judgement taken once
the answers are in. When "nothing ran", an earlier render of the same
request serves, and where none exists the placeholder ships and the loss is
named (`coldPicture`). When a request was refused either way, a picture the
rendered subset draws in part is withdrawn from the boundary and drawn by
the subset (`withdraw`); an attempt that never reached an answer is no
refusal, and stands. Each decision returns its diagnostics, so a test
can run it rather than restate it, and a driver that stopped naming the
loss fails the suite instead of passing it. -/

namespace LeanTex.Cli.Boundary

open LeanTex.Core

/-- With no tool, a complete checked drawing of the same request can serve.
Otherwise W0379 names the missing drawing at its source span. Refusals are
not replayed here: without the tool, its identity cannot be established. -/
def coldPicture (picDir : System.FilePath) (tool key : String)
    (span : Option Span := none) : IO (Except Diag ByteArray) := do
  match ← PictureAssets.previous picDir key with
  | some bytes => return .ok bytes
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

/-- How a boundary request came back with no drawing. `answered` is an
answer the withdrawal may act on: no tool looked at the request (W0379,
`said` none), or the tool ran and said no, in its own words. `unfinished` is
an attempt that never reached an answer — a budget kill, a spawn that
raised, a nonzero exit that left no log (`PicCache.outcome`): a fact about
the machine, not the request. -/
inductive Undrawn where
  | answered (why : Diag) (said : Option String)
  | unfinished (why : Diag)
  deriving Repr

/-- The refusal an undrawn request stands on when nothing withdraws it. -/
def Undrawn.why : Undrawn → Diag
  | .answered d _ => d
  | .unfinished d => d

/-- One attempt's ending as the withdrawal reads it: a drawing is nothing to
withdraw, the tool's own no is an answer in its words, and an attempt that
never finished is no answer at all. -/
def undrawnOf (tool : String) (o : PicCache.Outcome) (span : Option Span) : Option Undrawn :=
  match o with
  | .drawn => none
  | .refused says => some (.answered (DriverDiag.boundaryFailed tool says span) (some says))
  | .inconclusive says => some (.unfinished (DriverDiag.boundaryUnfinished tool says span))

/-- One undrawn request folded into the withdrawal: an answered one whose
picture the subset draws in part is withdrawn, with its note; everything
else stands. -/
def withdrawStep (tool : String) (fallbacks : Array String) (spans : Array (String × Span))
    (w : Withdrawal) (r : String × Undrawn) : Withdrawal :=
  match r.2, fallbacks.find? (Ir.picSrcPrefix ++ · == r.1) with
  | .answered _ said, some id =>
    { w with
      ids := w.ids.push id
      notes := w.notes.push (DriverDiag.boundaryWithdrawn tool said r.1
        ((spans.find? (·.1 == r.1)).map (·.2))) }
  | u, _ => { w with standing := w.standing.push (r.1, u.why) }

/-- **An attempt that never finished is never withdrawn** (`_exact`): it
joins the refusals that stand, whatever the subset could draw, so the run
stays as loud as a failed render — the artifact never changes on a fact
about the machine. The defect withdrew it like the tool's own verdict: a
killed or crashed tool shipped the subset's drawing with exit 0, its cause
a note printed only under `-v`. -/
theorem withdrawStep_unfinished_exact (tool : String) (fallbacks : Array String)
    (spans : Array (String × Span)) (w : Withdrawal) (src : String) (d : Diag) :
    withdrawStep tool fallbacks spans w (src, .unfinished d) =
      { w with standing := w.standing.push (src, d) } := by
  unfold withdrawStep
  cases fallbacks.find? (Ir.picSrcPrefix ++ · == src) <;> rfl

/-- **A refusal withdraws a request the subset can stand in for.** An
answered request — no tool looked, or the tool said no — whose picture the
rendered subset draws in part (`fallbacks`, by picture id, the elaborator's
record) is withdrawn: the driver elaborates again with its id
(`Elab.runPrepared`'s `picWithdrawn`), the subset's drawing ships with its
refusals named, and one N0419 at the picture's span says why the boundary
did not draw it, in the tool's own words where it ran. Every other refusal
stands: a picture the subset draws nothing of keeps W0379's placeholder, or
E0382's failed run, and an attempt that never finished keeps its E0382
(`withdrawStep_unfinished_exact`). Pure, so the decision is a value a test
runs rather than a sentence about the driver. -/
def withdraw (tool : String) (fallbacks : Array String)
    (undrawn : Array (String × Undrawn)) (spans : Array (String × Span)) : Withdrawal :=
  undrawn.foldl (withdrawStep tool fallbacks spans) {}

/-- **The HTML face withdraws a drawing it cannot show.** A boundary
picture's page face is its PDF, and its HTML face the SVG converted from
that PDF. Where the conversion is missing (W0378) the image has nothing to
show but a request key, so a picture the rendered subset draws in part —
`fallbacks`, the elaborator's record — is withdrawn from the HTML face
alone, which the driver elaborates again with it drawn by the subset; the
PDF keeps the boundary's drawing. The ids, by picture: those among the
fallbacks whose image source converted to no SVG (`unconverted`). -/
def htmlWithdraw (fallbacks unconverted : Array String) : Array String :=
  fallbacks.filter fun id => unconverted.contains (Ir.picSrcPrefix ++ id)

end LeanTex.Cli.Boundary
