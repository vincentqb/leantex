import LeanTex.Core.Font
import LeanTex.Core.Ir
import LeanTex.Cli.Args
import LeanTex.Cli.DriverDiag

/-! **A family slot that fell to the body face, named.**

The engine resolves three family slots — body, sans, mono. A slot the
document declares no family for is filled by the body family
(`resolveName` in the driver's assembly), so a `\texttt`, `\url` or
verbatim run in a document with no `\fonts{ mono = ... }` sets in body
prose. `Font.FontSet.slotCollapsed` is that fact, stated where `FontSet`
can see it; this module is the decision built on it, and the diagnostic is
`DriverDiag.slotCollapsed` (W0390).

Three things the decision needs beyond the index, each of them a condition
here rather than an assumption:

* what the document *set* — a slot no run reaches is no loss (`slotsUsed`);
* what the substitute *is* — a monospace body face sets `\texttt` in
  fixed pitch, index collapse or not (`Font.FontSet.slotIsFixedPitch`);
* whether the artifact carries a face at all — a page that declares
  `css =` ships none, and "set in the body face" then describes a file
  nobody receives (`carries`).

It sits under `LeanTex/Cli/` for two reasons. The emission needs the
document's `\fonts` declaration *and* the resolved index, and the driver's
assembly is the one place holding both. And a decision that is a module
returning its diagnostics is reachable as a unit — the property that lets a
probe run the real path rather than rebuild it, which a decision inlined in
the entry path is not.

Effects as data: nothing here opens a file or asks the host anything. The
font environment arrives as a resolved `FontSet` and a declared `FontSpec`,
both values; the answer leaves as `Diag` values. The policy is therefore
checkable with no font installed at all, which is the `Cli/PicCache.lean`
and `Cli/FontFix.lean` shape. -/

namespace LeanTex.Cli.SlotLoss

open LeanTex.Core

/-- A family slot, with the words a diagnostic about it needs: the `\fonts`
key that would declare it, the runs the loss is about, what is honestly
known about the substitute, and whether the slot's runs want a fixed-pitch
face. Data rather than a case split at the message site, so the two slots
cannot drift into saying the loss differently.

`runs` names the slot, not the constructs: which spelling reached a slot is
not a fact this census keeps (`\url` and `\texttt` are one `.styled .mono`
inline by the time the IR exists), and a message listing constructs the
document never wrote is a message that misreports. -/
structure SlotWord where
  slot : Nat
  key : String
  runs : String
  note : String
  /-- Do this slot's runs ask for a fixed-pitch face? True for mono, where
  a proportional substitute is the loss; false for sans, where the loss is
  the missing contrast and no flag in the face records it. -/
  wantsFixedPitch : Bool
  deriving Repr, BEq

/-- Slot 1: NFSS's sans family. The note claims no more than the engine
knows: whatever the body face is, a sans run set in it does not contrast
with the text around it. Whether that face is itself a sans design is a
question the engine cannot answer for every face — many declare no OS/2
family class — so it is not claimed. -/
def sansWord : SlotWord :=
  { slot := 1, key := "sans", runs := "sans runs"
    note := "so they do not contrast with the text around them"
    wantsFixedPitch := false }

/-- Slot 2: NFSS's typewriter family. The note is what the fixed-pitch
condition guarantees, so the message cannot say it of a monospace body. -/
def monoWord : SlotWord :=
  { slot := 2, key := "mono", runs := "typewriter runs"
    note := "which is not fixed-pitch"
    wantsFixedPitch := true }

/-- The slots a collapse can be reported for. Slot 0 is absent by
construction: it is the face the others are compared *against*, so a report
about it would be a vacuous truth rather than a loss (`words_mem`,
`Font.FontSet.slotCollapsed_body`). -/
def words : Array SlotWord := #[sansWord, monoWord]

/-- **Every reportable slot is drawn from the two past the body.** Keeps a
reader from being told the body face fell to itself. -/
theorem words_mem : ∀ w ∈ words, w.slot = 1 ∨ w.slot = 2 := by
  simp [words, sansWord, monoWord]

/-- The family a document declared for a slot, if it declared one. The
driver's own fallback order (`resolveName`) is what makes `none` the
condition worth reporting: an undeclared slot does not fail to resolve, it
resolves somewhere else. -/
def declared (spec : Ir.FontSpec) : Nat → Option String
  | 1 => spec.sans
  | 2 => spec.mono
  | _ => spec.body

/-- **Does this run's artifact set carry a face at all?** The PDF embeds the
resolved set; an HTML page does so only where `Doc.fontPolicy` is
`embedded`, which any declared `css =` turns off — the page then styles code
from its own stylesheet's monospace stack, and the markdown twin carries no
face either way. A loss about which face a run set in is a loss only where a
reader receives that face. -/
def carries (emit : Array Emit) (policy : Ir.FontPolicy) : Bool :=
  emit.contains .pdf || (emit.contains .html && policy == .embedded)

/-- **An HTML-only page under a declared stylesheet carries nothing.**
The gate's own condition, stated where the driver reads it: the
configuration the site port builds in is the one that must stay silent. -/
theorem carries_exact (policy : Ir.FontPolicy) :
    carries #[.html, .md] policy = (policy == .embedded) := by
  cases policy <;> simp [carries, Array.contains] <;> decide

/-- **Which family slots does this document's own content ask for?**
`foldBlocks`/`foldInlines` leaves, so the descent — a `\texttt` inside a
footnote, a running head, a style's font template — is the fold's and is
not re-decided here. A document that never sets mono is never told about
its mono slot.

Slot 2 is reached two ways and both are leaves: `Ir.Style.mono` on a
`.styled` inline (`\texttt`, `\ttfamily`, `\url`, inline verbatim), and an
`Ir.Block.verbatim`, which the layout sets by wrapping its content in
`.styled .mono`. -/
def slotsUsed (doc : Ir.Doc) : Array Nat :=
  let push (acc : Array Nat) (n : Nat) : Array Nat :=
    if acc.contains n then acc else acc.push n
  let fi (acc : Array Nat) : Ir.Inline → Array Nat
    | .styled .mono _ => push acc 2
    | .styled .sans _ => push acc 1
    | _ => acc
  let fb (acc : Array Nat) : Ir.Block → Array Nat
    | .verbatim _ _ _ => push acc 2
    | _ => acc
  (Ir.furnitureInlines doc).foldl (fun acc r => Ir.foldInlines fi acc r)
    (Ir.foldBlocks fb fi #[] doc.body)

/-- **The slots this document lost.** Five conditions, all necessary: the
artifact carries a face, the document asks for the slot, it declared no
family for it, the resolved index puts it on the body face, and — where the
slot's runs want fixed pitch — the face they got is not fixed-pitch. Drop
any one and the diagnostic becomes noise: a page shipping no face has no
face to lose, a document that never sets mono does not care, a document that
declared `mono` got what it asked for even if that family *is* the body
family, a slot resolving to its own face lost nothing, and a monospace body
sets typewriter runs in monospace whatever the index says. -/
def losses (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat)
    (carries : Bool) : Array SlotWord :=
  if !carries then #[] else
  words.filter fun w =>
    used.contains w.slot && (declared spec w.slot).isNone && fs.slotCollapsed w.slot
      && !(w.wantsFixedPitch && fs.slotIsFixedPitch w.slot)

/-- **The report is exactly its conditions.** A diagnostic resting on
`losses` names the condition it says it names, rather than a proxy that
could drift — the shape `slotCollapsed_exact` has one layer down. -/
theorem losses_exact (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat)
    (carries : Bool) (w : SlotWord) :
    w ∈ losses spec fs used carries ↔
      (carries = true ∧ w ∈ words ∧ used.contains w.slot = true
        ∧ (declared spec w.slot).isNone = true ∧ fs.slotCollapsed w.slot = true
        ∧ (w.wantsFixedPitch && fs.slotIsFixedPitch w.slot) = false) := by
  cases carries with
  | false => simp [losses]
  | true =>
    simp [losses, Array.mem_filter, and_assoc]
    intro _ _ _ _
    cases w.wantsFixedPitch <;> simp

/-- A reported slot is drawn from the slots the document set: the loss is
what a reader sees, and a reader sees nothing where the document set
nothing. -/
theorem losses_mem (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat)
    (carries : Bool) (w : SlotWord) (h : w ∈ losses spec fs used carries) :
    used.contains w.slot := by
  exact ((losses_exact spec fs used carries w).mp h).2.2.1

/-- The diagnostics for one resolved environment: one per collapsed slot the
document uses, each carrying `slot:<key>` as its subject so the site census
counts it. Never one per `\texttt` run — the loss is the slot's, and it is
the same loss wherever the slot is set. -/
def diags (spec : Ir.FontSpec) (fs : Font.FontSet) (doc : Ir.Doc)
    (carries : Bool) : Array Diag :=
  (losses spec fs (slotsUsed doc) carries).map fun w =>
    DriverDiag.slotCollapsed w.key w.runs w.note

end LeanTex.Cli.SlotLoss
