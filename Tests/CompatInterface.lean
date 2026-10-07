module

import LeanTex.Core.Compat

/-! Compatibility consumers exchange parsed requests, execution receipts and
opaque checkpoints. The macro interpreter and its mutable state are local
implementation details. -/

open LeanTex.Core

namespace Tests.CompatInterface

example : Compat.InputRequest → Array Parse.Raw := Compat.InputRequest.call
example : Compat.InputRequest → String := Compat.InputRequest.name
example : Compat.InputRequest → String := Compat.InputRequest.options
example : Compat.InputContext → Array Compat.InputAttempt :=
  Compat.InputContext.inputAttempts
example : Compat.Executed → Compat.SourceTriggers := Compat.Executed.sourceTriggers
example : Compat.Executed → Array Compat.InputAttempt := Compat.Executed.inputAttempts
example : Compat.Executed → Array Parse.Raw → Compat.Executed :=
  Compat.Executed.withRaws
example : Array Parse.Raw → Array String := Compat.localStyCandidates
example : Compat.Executed → Compat.RewriteCursor := Compat.beginRewrite
example : Compat.RewriteCursor → Array Parse.Raw × Array Diag × Array String :=
  Compat.finishRewrite

example (request : Compat.InputRequest)
    (response : Option (Array Parse.Raw) × Compat.InputContext) :
    (Compat.finishInput request response).2.inputAttempts =
      response.2.inputAttempts.push ⟨request, response.1.isSome⟩ :=
  Compat.finishInput_attempts_exact request response

example (executed : Compat.Executed) (raws : Array Parse.Raw) :
    (executed.withRaws raws).raws = raws ∧
      (executed.withRaws raws).sourceTriggers = executed.sourceTriggers ∧
      (executed.withRaws raws).inputAttempts = executed.inputAttempts :=
  Compat.Executed.withRaws_contract executed raws

example : True := by
  fail_if_success have := Compat.St
  fail_if_success have := Compat.M
  fail_if_success have := Compat.EvalM
  fail_if_success have := Compat.condList
  fail_if_success have := Compat.rewriteList
  fail_if_success have := Compat.rewriteCtrl
  fail_if_success have := Compat.executionState
  fail_if_success have := Compat.beamerColorRoles
  fail_if_success have := Compat.InputContext.mk
  fail_if_success have := Compat.InputContext.state
  fail_if_success have := Compat.Executed.state
  fail_if_success have := Compat.RewriteCursor.state
  trivial

end Tests.CompatInterface
