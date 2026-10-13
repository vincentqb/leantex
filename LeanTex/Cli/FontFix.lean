module

public import LeanTex.Core.Ir

/-! The font-environment fixed point the driver reaches, as values: the measurements an
elaboration made and whether two environments answer them alike. -/

namespace LeanTex.Cli.FontFix

open LeanTex.Core

private instance instDecidableEqLabelInk : DecidableEq Ir.Pic.LabelInk := fun a b => by
  cases a
  cases b
  simp only [Ir.Pic.LabelInk.mk.injEq]
  infer_instance

/-- One label measurement: a label's content at its per-mille size, `Ir.Pic.LabelMetric`'s
arguments. -/
public abbrev Probe := Array Ir.Inline × Nat

/-- Every measurement one picture asked a face for, edge labels included. -/
public def probesOfPic (p : Ir.Pic.Picture) : Array Probe :=
  p.shapes.filterMap fun s => match s with
    | .label _ _ content _ scale _ => some (content, scale)
    | .ink _ => none

/-- Every distinct measurement a document's pictures asked a face for, at any depth. -/
public def probes (blocks : Array Ir.Block) : Array Probe :=
  Ir.foldBlocks (fun acc b => match b with
      | .picture p => probesOfPic p |>.foldl
          (fun acc q => if acc.contains q then acc else acc.push q) acc
      | _ => acc)
    (fun acc _ => acc) #[] blocks

/-- Whether two font environments measure every probe alike. -/
public def agree (m₁ m₂ : Ir.Pic.LabelMetric) (ps : Array Probe) : Bool :=
  ps.all fun p => decide (m₁ p.1 p.2 = m₂ p.1 p.2)

/-- How many probes two environments measure differently. -/
public def disagreements (m₁ m₂ : Ir.Pic.LabelMetric) (ps : Array Probe) : Nat :=
  ps.foldl (fun n p => if m₁ p.1 p.2 = m₂ p.1 p.2 then n else n + 1) 0

public theorem agree_refl (m : Ir.Pic.LabelMetric) (ps : Array Probe) :
    agree m m ps = true := by
  simp [agree]

public theorem agree_probe (m₁ m₂ : Ir.Pic.LabelMetric) (ps : Array Probe)
    (h : agree m₁ m₂ ps = true) (p : Probe) (hp : p ∈ ps) :
    m₁ p.1 p.2 = m₂ p.1 p.2 := by
  rw [agree, Array.all_eq_true] at h
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hp
  exact of_decide_eq_true (h i hi)

public theorem extent_agree (m₁ m₂ : Ir.Pic.LabelMetric) (content : Array Ir.Inline)
    (scale : Nat) (align : Ir.Pic.LabelAlign) (declA declB : Dim.Sp)
    (h : m₁ content scale = m₂ content scale) :
    Ir.Pic.nodeExtent m₁ content scale align declA declB
      = Ir.Pic.nodeExtent m₂ content scale align declA declB := by
  simp [Ir.Pic.nodeExtent, h]

public theorem probesOfPic_covers (p : Ir.Pic.Picture) (x y : Dim.Sp)
    (content : Array Ir.Inline) (color : Ir.Color) (scale : Nat)
    (align : Ir.Pic.LabelAlign)
    (h : Ir.Pic.Shape.label x y content color scale align ∈ p.shapes) :
    (content, scale) ∈ probesOfPic p := by
  rw [probesOfPic, Array.mem_filterMap]
  exact ⟨_, h, rfl⟩

end LeanTex.Cli.FontFix
