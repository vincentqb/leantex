module

import LeanTex.Core.PdfContract
import LeanTex.Core.PictureCensus
import LeanTex.Core.MdDesugar

/-! Document consumers see conformance policies, picture conservation, and
Markdown desugaring. Rule implementation and recursive accumulators remain
private; ordinary imports are sufficient for the public contracts. -/

open LeanTex.Core
open LeanTex.Core.Ir

namespace Tests.DocumentContractInterfaces

example : String → PdfContract.Filter := PdfContract.Filter.ofName
example : PdfContract.Contract → PdfContract.Contract → PdfContract.Contract :=
  PdfContract.Contract.meet
example : PdfContract.Contract → PdfContract.Contract → Prop :=
  PdfContract.Contract.le
example : Array String → Except PdfContract.Violation PdfContract.Contract :=
  PdfContract.Contract.ofProfiles
example : PdfContract.Contract → PdfCensus.Census → Option String →
    Array PdfContract.Violation := PdfContract.violations
example : String → OutputContract := PdfContract.Profile.implies

example (a b : PdfContract.Contract) : a.le (a.meet b) ∧ b.le (a.meet b) :=
  PdfContract.meet_covers a b

example {a b : PdfContract.Contract} (h : a.le b) (x : PdfCensus.Census)
    (title : Option String) (hb : PdfContract.violations b x title = #[]) :
    PdfContract.violations a x title = #[] :=
  PdfContract.violations_monotone h x title hb

example (c : PdfContract.Contract) (x : PdfCensus.Census)
    (h : c.needsTitle = true) : PdfContract.violations c x none ≠ #[] :=
  PdfContract.needsTitle_accounts c x h

example : Array Block → Nat := Elab.enginePictures
example (doc : Doc) : Elab.enginePictures (Ir.eraseLocations doc).body =
    Elab.enginePictures doc.body := Elab.eraseLocations_pictureCount_exact doc

example : String → Option String := Md.altSource
example : String → Option String := Md.altReadBack
example : String → String → Array Parse.Raw × Array Diag := Md.desugar
example : String → String → Array Parse.Raw × Array Diag := Md.read

example : True := by
  fail_if_success have := PdfContract.tableSix
  fail_if_success have := PdfContract.Rule.spaceHolds
  fail_if_success have := PdfContract.Rule.langMissing
  fail_if_success have := PdfContract.Rule.info_mono
  fail_if_success have := Elab.pictureCountStep
  fail_if_success have := Elab.inlinePictureCount_id
  fail_if_success have := Md.route
  fail_if_success have := Md.inlListRaws
  fail_if_success have := Md.blkListRaws
  fail_if_success have := Md.itemsRaws
  trivial

end Tests.DocumentContractInterfaces
