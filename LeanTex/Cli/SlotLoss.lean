module

public import LeanTex.Core.Font
public import LeanTex.Core.Ir
public import LeanTex.Cli.Args
import LeanTex.Cli.DriverDiag

/-! A family slot set in a face that is not of its kind, named as W0390: the decision over
the resolved face set, the declared fonts and what the run's artifacts carry. -/

namespace LeanTex.Cli.SlotLoss

open LeanTex.Core

/-- What a slot's runs ask of the face that sets them. -/
public inductive SlotKind where
  /-- Fixed pitch, which every face declares (`post.isFixedPitch`). -/
  | fixedPitch
  /-- Contrast with the running text, read as whether the face is the text's own. -/
  | contrast
  deriving Repr, BEq, DecidableEq

/-- Whether the face serving `slot` is not of this kind, read through the setter's
`lookup`. -/
public def SlotKind.lost (k : SlotKind) (fs : Font.FontSet) (slot : Nat) : Bool :=
  match k with
  | .fixedPitch => !fs.slotIsFixedPitch slot
  | .contrast => fs.slotCollapsed slot

/-- A family slot with the words a diagnostic about it needs: its `\fonts` key, its runs,
what is known of the substitute, and its kind. -/
public structure SlotWord where
  slot : Nat
  key : String
  runs : String
  note : String
  kind : SlotKind
  deriving Repr, BEq

/-- Slot 1, NFSS's sans family. -/
public def sansWord : SlotWord :=
  { slot := 1, key := "sans", runs := "sans runs"
    note := "so they do not contrast with the text around them"
    kind := .contrast }

/-- Slot 2, NFSS's typewriter family. -/
public def monoWord : SlotWord :=
  { slot := 2, key := "mono", runs := "typewriter runs"
    note := "which is not fixed-pitch"
    kind := .fixedPitch }

/-- The slots a loss can be reported for; slot 0, the text face the others are compared
against, is absent. -/
public def words : Array SlotWord := #[sansWord, monoWord]

public theorem words_mem : ∀ w ∈ words, w.slot = 1 ∨ w.slot = 2 := by
  simp [words, sansWord, monoWord]

/-- The family a document declared for a slot, if any. -/
public def declared (spec : Ir.FontSpec) : Nat → Option String
  | 1 => spec.sans
  | 2 => spec.mono
  | _ => spec.body

/-- What served a lost slot: the running text's face, or the body family where the text
sets in another. -/
public inductive Served where
  | bodyFace
  | bodyFamily
  deriving Repr, BEq, DecidableEq

def Served.words : Served → String
  | .bodyFace => "the body face"
  | .bodyFamily => "the body family"

/-- Which of the two served the slot: the text's own face exactly when the
slot resolves where the text does. -/
public def served (fs : Font.FontSet) (slot : Nat) : Served :=
  if fs.slotCollapsed slot then .bodyFace else .bodyFamily

/-- The emitted artifacts that set runs in the resolved faces (`faced`: the PDF, an HTML
page under `embedded`) and those that style runs from their own stylesheet (`unfaced`); a
markdown twin is in neither. -/
public structure Carry where
  faced : Array Emit
  unfaced : Array Emit
  deriving Repr, BEq

/-- Which artifacts carry a face, the condition under which a slot loss is one. -/
public def carries (emit : Array Emit) (policy : Ir.FontPolicy) : Carry :=
  { faced := emit.filter fun e => e == .pdf || (e == .html && policy == .embedded)
    unfaced := emit.filter fun e => e == .html && policy != .embedded }

public theorem carries_exact (policy : Ir.FontPolicy) :
    (carries #[.html, .md] policy).faced.isEmpty = (policy != .embedded) := by
  cases policy <;> rfl

public theorem carries_mixed_exact :
    carries #[.pdf, .html] .none = { faced := #[.pdf], unfaced := #[.html] } := by
  rfl

/-- How a report names an artifact. -/
def artifactWord : Emit → String
  | .pdf => "the PDF"
  | .html => "the HTML page"
  | .md => "the markdown twin"

/-- The artifacts a report names when not every emitted artifact sets its runs in the
resolved faces; `none` when every one does. -/
def Carry.only (c : Carry) : Option String :=
  if c.unfaced.isEmpty then none
  else some (" and ".intercalate (c.faced.toList.map artifactWord))

/-- The family slots the document's own content asks for, picture labels and listing
captions included. -/
public def slotsUsed (doc : Ir.Doc) : Array Nat :=
  let push (acc : Array Nat) (n : Nat) : Array Nat :=
    if acc.contains n then acc else acc.push n
  let fi (acc : Array Nat) : Ir.Inline → Array Nat
    | .styled .mono _ => push acc 2
    | .styled .sans _ => push acc 1
    | _ => acc
  let fb (acc : Array Nat) : Ir.Block → Array Nat
    | .verbatim _ _ spec =>
      let acc := push acc 2
      match spec.caption with
      | some (_, caption) => Ir.foldInlines fi acc caption
      | none => acc
    | .picture pic => pic.labelContents.foldl (fun acc xs => Ir.foldInlines fi acc xs) acc
    | _ => acc
  let found := (Ir.furnitureInlines doc).foldl (fun acc r => Ir.foldInlines fi acc r)
    (Ir.foldBlocks fb fi #[] doc.body)
  if (Ir.mathRequests .alphabets doc).any (·.body.setsMono doc.fonts.mathSources.tt) then
    push found 2
  else found

/-- The slots this document lost: some artifact carries a face, the document sets the slot
and declared no family for it, and the serving face is not of the slot's kind. -/
public def losses (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat)
    (c : Carry) : Array SlotWord :=
  if c.faced.isEmpty then #[] else
  words.filter fun w =>
    used.contains w.slot && (declared spec w.slot).isNone && w.kind.lost fs w.slot

public theorem losses_exact (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat)
    (c : Carry) (w : SlotWord) :
    w ∈ losses spec fs used c ↔
      (c.faced.isEmpty = false ∧ w ∈ words ∧ used.contains w.slot = true
        ∧ (declared spec w.slot).isNone = true ∧ w.kind.lost fs w.slot = true) := by
  by_cases h : c.faced.isEmpty
  · simp [losses, h]
  · simp [losses, h, Array.mem_filter, and_assoc]

public theorem losses_mono_exact (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat)
    (c : Carry) :
    monoWord ∈ losses spec fs used c ↔
      (c.faced.isEmpty = false ∧ used.contains 2 = true ∧ spec.mono.isNone = true
        ∧ fs.slotIsFixedPitch 2 = false) := by
  rw [losses_exact]
  simp [monoWord, words, declared, SlotKind.lost]

public theorem losses_mem (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat)
    (c : Carry) (w : SlotWord) (h : w ∈ losses spec fs used c) :
    used.contains w.slot := by
  exact ((losses_exact spec fs used c w).mp h).2.2.1

/-- One diagnostic per lost slot, subject `slot:<key>`, naming what served it and, where
not every artifact carries the face, which artifact lost. -/
public def diags (spec : Ir.FontSpec) (fs : Font.FontSet) (doc : Ir.Doc)
    (c : Carry) : Array Diag :=
  (losses spec fs (slotsUsed doc) c).map fun w =>
    DriverDiag.slotCollapsed w.key w.runs (served fs w.slot).words w.note c.only
      (doc.surface == .tex) (!doc.fonts.dirs.isEmpty)

end LeanTex.Cli.SlotLoss
