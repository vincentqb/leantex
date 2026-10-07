module

import LeanTex.Core.Elab

open LeanTex.Core

namespace Tests.ElabInterface

example : String → Array Parse.Raw → Elab.Prepared := Elab.prepare
example : String → Compat.Executed → Elab.Prepared := Elab.prepareExecuted
example : Compat.InputContext → Array Compat.InputAttempt :=
  Compat.InputContext.inputAttempts
example : Elab.Prepared → Array Compat.InputAttempt := Elab.Prepared.inputAttempts
example : Array Parse.Raw → Elab.PicWants := Elab.picWants
example : String → String → Ir.Doc × Array Diag := Elab.run
example : Array (String × Span) → String → Option Span := Elab.ReqSpans.spanOf

example (file : String) : Elab.Ctx := { file }
example (ctx : Elab.Ctx) : Elab.Ctx := { ctx with argBody := true }
example (st : Elab.ESt) : Elab.ESt := { st with refusedTitleBody := none }
example (action : Elab.EM α) (st : Elab.ESt) : α × Elab.ESt := action.run st

example (file : String) (executed : Compat.Executed) :
    (Elab.prepareExecuted file executed).inputAttempts = executed.inputAttempts :=
  Elab.prepareExecuted_inputAttempts_exact file executed

example : True := by
  fail_if_success have := Elab.MacroRun
  fail_if_success have := Elab.MacroRoles.mk
  fail_if_success have := Elab.MacroRoles.inherited
  fail_if_success have := Elab.MacroRoles.inlines
  fail_if_success have := Elab.MacroRoles.blocks
  fail_if_success have := Elab.MacroRoles.blockKinds
  fail_if_success have := Elab.PEvent
  fail_if_success have := Elab.ArgScan
  fail_if_success have := Elab.BarSt
  fail_if_success have := Elab.elabInlinesFrom
  fail_if_success have := Elab.elabInlinesCtrl
  fail_if_success have := Elab.elabUnknownCtrl
  fail_if_success have := Elab.warnOnceDiag
  fail_if_success have := Elab.pictureKeyState
  fail_if_success have := Elab.pictureSettingState
  trivial

end Tests.ElabInterface
