module

import LeanTex.Cli.SlotLoss

/-! Ordinary clients read the slot and artifact decisions through their
public records and contracts. Diagnostic wording is implementation detail. -/

open LeanTex.Core LeanTex.Cli
open LeanTex.Cli.SlotLoss

namespace Tests.SlotLossInterface

example : Repr SlotKind := inferInstance
example : DecidableEq SlotKind := inferInstance
example : BEq SlotWord := inferInstance
example : BEq Carry := inferInstance
example : DecidableEq Served := inferInstance
example : Array SlotKind := #[.fixedPitch, .contrast]
example (slot : Nat) (key runs note : String) (kind : SlotKind) : SlotWord :=
  { slot, key, runs, note, kind }
example (word : SlotWord) : Nat × String × String × String × SlotKind :=
  (word.slot, word.key, word.runs, word.note, word.kind)
example (faced unfaced : Array Emit) : Carry := { faced, unfaced }
example (carry : Carry) : Array Emit × Array Emit := (carry.faced, carry.unfaced)
example : Array Served := #[.bodyFace, .bodyFamily]
example : Array SlotWord := #[sansWord, monoWord]
example : Array SlotWord := words
example : SlotKind → Font.FontSet → Nat → Bool := SlotKind.lost
example : Ir.FontSpec → Nat → Option String := declared
example : Font.FontSet → Nat → Served := served
example : Array Emit → Ir.FontPolicy → Carry := carries
example : Ir.Doc → Array Nat := slotsUsed
example : Ir.FontSpec → Font.FontSet → Array Nat → Carry → Array SlotWord := losses
example : Ir.FontSpec → Font.FontSet → Ir.Doc → Carry → Array Diag := diags

example (word : SlotWord) (h : word ∈ words) : word.slot = 1 ∨ word.slot = 2 :=
  words_mem word h
example (policy : Ir.FontPolicy) :
    (carries #[.html, .md] policy).faced.isEmpty = (policy != .embedded) :=
  carries_exact policy
example : carries #[.pdf, .html] .none = { faced := #[.pdf], unfaced := #[.html] } :=
  carries_mixed_exact
example (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat)
    (carry : Carry) (word : SlotWord) :
    word ∈ losses spec fs used carry ↔
      (carry.faced.isEmpty = false ∧ word ∈ words ∧ used.contains word.slot = true
        ∧ (declared spec word.slot).isNone = true ∧ word.kind.lost fs word.slot = true) :=
  losses_exact spec fs used carry word
example (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat) (carry : Carry) :
    monoWord ∈ losses spec fs used carry ↔
      (carry.faced.isEmpty = false ∧ used.contains 2 = true ∧ spec.mono.isNone = true
        ∧ fs.slotIsFixedPitch 2 = false) :=
  losses_mono_exact spec fs used carry
example (spec : Ir.FontSpec) (fs : Font.FontSet) (used : Array Nat)
    (carry : Carry) (word : SlotWord) (h : word ∈ losses spec fs used carry) :
    used.contains word.slot :=
  losses_mem spec fs used carry word h

example : True := by
  fail_if_success have := SlotLoss.Served.words
  fail_if_success have := SlotLoss.artifactWord
  fail_if_success have := SlotLoss.Carry.only
  fail_if_success
    have : carries #[.pdf, .html] .none = { faced := #[.pdf], unfaced := #[.html] } := by
      rfl
  trivial

end Tests.SlotLossInterface
