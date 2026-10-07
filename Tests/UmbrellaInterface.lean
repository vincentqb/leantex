module

import LeanTex

/-! The public umbrella keeps its existing parser, document, artifact and
CLI library interfaces. Re-exporting a module does not expose its private
implementation or mutable state. -/

open LeanTex.Core LeanTex.Cli

namespace Tests.UmbrellaInterface

example (p : Pos) (body : Array Parse.Raw) : Parse.Raw := .group body p
example : String → Array Lex.Token → Array Parse.Raw × Array Diag := Parse.parse
example : Array (String × String) → Ir.Doc → Ir.Doc × Array Diag := Bib.apply
example : String → IO (Except Diag ByteArray) := Input.readSource
example : String → Array Parse.Raw →
    IO (Compat.Executed × Array Diag × Array (String × Option String × Pos)) :=
  Input.expandInputs
example : (Elab.structuralNames.all fun n => !Elab.renderedBuiltins.contains n) = true :=
  Elab.structural_rendered_disjoint
example : (Elab.builtinNames.all fun n =>
    Elab.structuralNames.contains n || Elab.renderedBuiltins.contains n) = true :=
  Elab.builtin_verdict_total
example : IO FontEnv.Cache := FontEnv.Cache.mk'
example : SlotLoss.Carry := { faced := #[.pdf], unfaced := #[.html] }

example (policy : Ir.FontPolicy) :
    (SlotLoss.carries #[.html, .md] policy).faced.isEmpty = (policy != .embedded) :=
  SlotLoss.carries_exact policy

example : True := by
  fail_if_success have := Parse.Frame
  fail_if_success have := Input.reasonLine
  fail_if_success have := Input.InputLog
  fail_if_success have := FontEnv.Cache.mk
  fail_if_success have := FontEnv.Cache.ref
  fail_if_success have := SlotLoss.Carry.only
  fail_if_success have := Boundary.Undrawn.why
  trivial

end Tests.UmbrellaInterface
