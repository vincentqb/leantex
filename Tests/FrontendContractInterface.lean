module

import LeanTex.Core.TitleContract
import LeanTex.Core.PictureContract

/-! Ordinary consumers can instantiate the frontend's title and picture
contracts. Their induction lemmas and reporting-loop equations stay private. -/

open LeanTex.Core

namespace Tests.FrontendContractInterface

example : Elab.TitleBodyContext → Parse.Raw → Array Parse.Raw :=
  Elab.TitleBodyContext.fill

example (raw : Parse.Raw) : Elab.TitleBodyContext.hole.fill raw = #[raw] := rfl

example (pre post : Array Parse.Raw) (inner : Elab.TitleBodyContext)
    (raw : Parse.Raw) :
    (Elab.TitleBodyContext.around pre post inner).fill raw =
      pre ++ inner.fill raw ++ post := rfl

example (context : Elab.TitleBodyContext) (raw : Parse.Raw) (pos : Pos) :
    (Elab.TitleBodyContext.group context pos).fill raw =
      #[.group (context.fill raw) pos] := rfl

example (ds : Array Diag) (key : String) :
    Elab.PictureKeyNamed ds key ↔
      ∃ d ∈ ds, d.kind = .W0334 ∧ d.subject = some ("picture:set:" ++ key) := Iff.rfl

example (key : String) : ¬ Elab.UnreadPictureSetting #[] key := by
  rintro ⟨before, setting, after, hsets, _⟩
  have hlength := congrArg List.length hsets
  simp at hlength

example (file : String) (p : Elab.Prepared) (earlier : Array Diag)
    (metric : Ir.Pic.LabelMetric) (context : Elab.TitleBodyContext)
    (pos : Pos) (row : String × String) (hrow : row ∈ Elab.beamerInsertAlias) :
    Elab.finishPreparedRuns (fun withdrawn =>
      let phase := Elab.preparedPreamble file p metric withdrawn
      Elab.runPreamble file p earlier phase.1
        { phase.2 with refusedTitleBody := some (context.fill (.ctrl row.1 pos)) }) =
    Elab.finishPreparedRuns (fun withdrawn =>
      let phase := Elab.preparedPreamble file p metric withdrawn
      Elab.runPreamble file p earlier phase.1
        { phase.2 with refusedTitleBody := some (context.fill (.ctrl row.2 pos)) }) :=
  Elab.titleStyle_spelling_agree file p earlier metric context pos row hrow

example (file : String) (raws : Array Parse.Raw) (earlier : Array Diag)
    (metric : Ir.Pic.LabelMetric) (key : String)
    (hdrew : 0 < Elab.enginePictures (Elab.runRaws file raws earlier metric).1.body)
    (hsetting : Elab.UnreadPictureSetting (Elab.prepare file raws).picSets key) :
    (Elab.runRaws file raws earlier metric).2.any (fun d =>
      d.kind == .W0334 && d.subject == some ("picture:set:" ++ key)) = true :=
  Elab.pictureKeys_named file raws earlier metric key hdrew hsetting

example (file : String) (executed : Compat.Executed) (earlier : Array Diag)
    (metric : Ir.Pic.LabelMetric) (key : String)
    (hdrew : 0 < Elab.enginePictures
      (Elab.runExecuted file executed earlier metric).1.body)
    (hsetting : Elab.UnreadPictureSetting (Elab.prepareExecuted file executed).picSets key) :
    Elab.PictureKeyNamed (Elab.runExecuted file executed earlier metric).2 key :=
  Elab.runExecuted_pictureKeys_named file executed earlier metric key hdrew hsetting

example := @Elab.refusedTitleReadout_spelling_agree
example := @Elab.titleStyleMerge_spelling_agree
example := @Elab.applyRefusedTitleStyle_spelling_agree
example := @Elab.runPreamble_spelling_agree
example := @Elab.titleStylePhases_spelling_agree
example := @Elab.reportPictureKeys_named
example := @Elab.finishPictureKeys_named
example := @Elab.completePrepared_pictureKeys_named
example := @Elab.runPrepared_pictureKeys_named
example := @Elab.runPreparedFinal_pictureKeys_named

example : True := by
  fail_if_success have := Elab.titleView_append
  fail_if_success have := Elab.TitleBodyContext.spellingView
  fail_if_success have := Elab.pictureSettingState_run_exact
  fail_if_success have := Elab.reportPictureKeys_run_exact
  fail_if_success have := Elab.pictureSettingStyles_drawer_agree
  fail_if_success have := Elab.keyState_preserves
  fail_if_success have := Elab.keyState_names
  fail_if_success have := Elab.keyFold_preserves
  fail_if_success have := Elab.keyFold_names
  fail_if_success have := Elab.settingState_preserves
  fail_if_success have := Elab.settingState_names
  fail_if_success have := Elab.settingFold_preserves
  fail_if_success have := Elab.settingFold_styles
  fail_if_success have := Elab.named_tally
  trivial

end Tests.FrontendContractInterface
