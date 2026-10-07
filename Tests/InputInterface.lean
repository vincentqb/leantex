module

import LeanTex.Cli.Input

/-! The file frontend's ordinary client receives parsed values, execution
state and typed diagnostics. File recursion and its log remain private. -/

open LeanTex.Core LeanTex.Cli.Input

namespace Tests.InputInterface

example : String → IO (Except Diag ByteArray) := readSource
example : System.FilePath → String → String → Pos →
    IO (Array Parse.Raw × Array Diag) := readInput
example : System.FilePath → Array Parse.Raw →
    IO (Array Parse.Raw × Array (String × Option String × Pos)) := expandLocalSty
example : String → Array Parse.Raw →
    IO (Compat.Executed × Array Diag × Array (String × Option String × Pos)) :=
  expandInputs
example : String → Ir.Doc → Array (String × Span) →
    IO (Ir.Doc × Array Diag) := @resolveBibliography
example : String → Array Parse.Raw → IO (Array Parse.Raw × Array Diag) := resolveData

example (file : String) : readSource file = readSource file := by
  fail_if_success unfold readSource
  rfl

example : True := by
  fail_if_success have := LeanTex.Cli.Input.reasonLine
  fail_if_success have := LeanTex.Cli.Input.readFragment
  fail_if_success have := LeanTex.Cli.Input.InputLog
  fail_if_success have := LeanTex.Cli.Input.ReadM
  fail_if_success have := LeanTex.Cli.Input.readAt
  trivial

end Tests.InputInterface
