module

public import LeanTex.Cli.SlotLoss
public import LeanTex.Core.Image
public import LeanTex.Core.Pdf
public import LeanTex.Core.HtmlDoc

/-! The losses a build names between its image store and its writers, shared by
`Driver.build` and the typeset tier. -/

namespace LeanTex.Cli.PlanLoss

open LeanTex.Core

/-- Each loaded image plan's losses, in store order. -/
public def ledger (store : Image.Store) : Array Diag := Id.run do
  let mut ds : Array Diag := #[]
  for en in store.entries do
    if let some pl := en.info then
      let losses := Image.lossDiags en.src pl
      ds := ds ++ losses
  return ds

/-- The boundary pictures whose drawn box embeds and carries no text alternative. -/
public def pictureAlts (doc : Ir.Doc) (imageSpans : Array (String × Span))
    (store : Image.Store) : Array Diag :=
  Ir.picAltDiags doc (fun src => (imageSpans.find? (·.1 == src)).map (·.2))
    (fun src => store.entries.any fun en => en.src == src && en.info.isSome)

/-- The losses the plan's formats decide over the settled face set: each slot set in a
face not of its kind (W0390), and each unmet contract fact, per artifact (W0701). -/
public def ofPlan (emit : Array Emit) (fs : Font.FontSet) (doc : Ir.Doc) : Array Diag :=
  -- premise: slotLossChecks — carrying a face reports the lost slot, carrying none nothing
  SlotLoss.diags doc.fonts fs doc (SlotLoss.carries emit doc.fontPolicy) ++
    (if emit.contains .pdf then Ir.contractDiags (doc.output.contract.unmet Pdf.profile)
     else #[]) ++
    (if emit.contains .html then Ir.contractDiags (doc.output.contract.unmet HtmlDoc.profile)
     else #[])

end LeanTex.Cli.PlanLoss
