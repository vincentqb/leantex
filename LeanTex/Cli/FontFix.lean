module

public import LeanTex.Core.Ir

/-! The fixed point the driver has to reach, as values it can check.

**The artifact is a function of the document and the font environment** —
and the font environment is a function of the elaborated document, because
`\fonts` is a preamble declaration and the off-corner weights, the math
face and the per-glyph fallback are read off the whole body. So the
driver's job is not to order two independent things; it is to land on a
document `d` with `d = elaborate(source, measurement(fontEnv(d)))`, and the
only question is how many elaborations that takes.

One suffices whenever a face resolved from the preamble alone measures
every label the way the final environment would. That is decidable, and
decided here: `probes` is every measurement an elaboration made, `agree`
asks whether two environments answer them identically, and `extent_agree`
is why an affirmative answer settles the document — a node's extent is a
function of its label's ink and nothing else (`Ir.Pic.nodeExtent`), so two
metrics that agree on the ink place the node at the same point, and the
border arithmetic downstream is the same arithmetic on the same numbers.

The policy lives in the driver as values, not as control flow, so it can
be checked with no font installed: `Cli/PicCache.lean` is the precedent. -/

namespace LeanTex.Cli.FontFix

open LeanTex.Core

private instance instDecidableEqLabelInk : DecidableEq Ir.Pic.LabelInk := fun a b => by
  cases a
  cases b
  simp only [Ir.Pic.LabelInk.mk.injEq]
  infer_instance

/-- One measurement: a label's content at its per-mille size. The pair is
exactly `Ir.Pic.LabelMetric`'s argument list, so a probe is a *call* that
was made rather than a description of one. -/
public abbrev Probe := Array Ir.Inline × Nat

/-- Every measurement one picture asked a face for. A node's extent is
computed from the shapes its own body would emit (`Picture.evalNode` hulls
them through `Ir.Pic.Shape.inkBox`), and those are the label shapes the
node then emits, so the picture's own labels are the calls — which is what
`probesOfPic_covers` says. Edge labels ride along: a label nothing measured
is a probe that can only make the answer more conservative, never less. -/
public def probesOfPic (p : Ir.Pic.Picture) : Array Probe :=
  p.shapes.filterMap fun s => match s with
    | .label _ _ content _ scale _ => some (content, scale)
    | .rect _ _ _ _ _ => none
    | .circle _ _ _ _ _ => none
    | .frame _ _ _ _ _ _ => none
    | .edge _ _ _ => none

/-- Every measurement a document's pictures asked a face for, at any
depth — each distinct call once. Labels repeat heavily (a deck's rows reuse
the same words, a graph its own node names), and the comparison is an
`m content scale` on both faces, so the duplicates are the cost: 180 labels
over twelve distinct words is twelve measurements, not a hundred and
eighty. -/
public def probes (blocks : Array Ir.Block) : Array Probe :=
  Ir.foldBlocks (fun acc b => match b with
      | .picture p => probesOfPic p |>.foldl
          (fun acc q => if acc.contains q then acc else acc.push q) acc
      | _ => acc)
    (fun acc _ => acc) #[] blocks

/-- Whether two font environments' measurements are the same measurement,
on every call an elaboration made. -/
public def agree (m₁ m₂ : Ir.Pic.LabelMetric) (ps : Array Probe) : Bool :=
  ps.all fun p => decide (m₁ p.1 p.2 = m₂ p.1 p.2)

/-- How many probes the two faces answer differently, for the report: a
superseded provisional face is worth naming with its cause, since the cost
of being wrong is a second elaboration and a reader who sees it can move
the declaration that caused it into the preamble. -/
public def disagreements (m₁ m₂ : Ir.Pic.LabelMetric) (ps : Array Probe) : Nat :=
  ps.foldl (fun n p => if m₁ p.1 p.2 = m₂ p.1 p.2 then n else n + 1) 0

/-- **A face agrees with itself.** The check never sends a document down
the slow path for a provisional environment that was already the final
one — which is the property that makes the fast path the common case
rather than an accident of which fixtures were tried. -/
public theorem agree_refl (m : Ir.Pic.LabelMetric) (ps : Array Probe) :
    agree m m ps = true := by
  simp [agree]

/-- The measurement behind an affirmative answer, for one probe. -/
public theorem agree_probe (m₁ m₂ : Ir.Pic.LabelMetric) (ps : Array Probe)
    (h : agree m₁ m₂ ps = true) (p : Probe) (hp : p ∈ ps) :
    m₁ p.1 p.2 = m₂ p.1 p.2 := by
  rw [agree, Array.all_eq_true] at h
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hp
  exact of_decide_eq_true (h i hi)

/-- **Two metrics that measure a label alike place its node alike.** The
extent a node registers is a function of its label's ink and its declared
minimum (`Ir.Pic.nodeExtent`), so this is the congruence — and it is the
whole reason an agreeing provisional face needs no second elaboration: the
placement fixed point reads these numbers and nothing else about the face,
and `Ir.Pic.nodeExtent_covers` then holds of the shipped document with the
final environment's own measurement. -/
public theorem extent_agree (m₁ m₂ : Ir.Pic.LabelMetric) (content : Array Ir.Inline)
    (scale : Nat) (align : Ir.Pic.LabelAlign) (declA declB : Dim.Sp)
    (h : m₁ content scale = m₂ content scale) :
    Ir.Pic.nodeExtent m₁ content scale align declA declB
      = Ir.Pic.nodeExtent m₂ content scale align declA declB := by
  simp [Ir.Pic.nodeExtent, h]

/-- **Every label of a picture is probed.** The coverage the check rests
on: a measurement the driver never compares is a measurement that could
differ in silence, so the probe set has to hold each label the picture
carries. -/
public theorem probesOfPic_covers (p : Ir.Pic.Picture) (x y : Dim.Sp)
    (content : Array Ir.Inline) (color : Ir.Color) (scale : Nat)
    (align : Ir.Pic.LabelAlign)
    (h : Ir.Pic.Shape.label x y content color scale align ∈ p.shapes) :
    (content, scale) ∈ probesOfPic p := by
  rw [probesOfPic, Array.mem_filterMap]
  exact ⟨_, h, rfl⟩

end LeanTex.Cli.FontFix
