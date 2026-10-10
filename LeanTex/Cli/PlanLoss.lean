module

public import LeanTex.Cli.SlotLoss
public import LeanTex.Core.Image
public import LeanTex.Core.Pdf
public import LeanTex.Core.HtmlDoc

/-! # The losses a build names between its image store and its writers

What the driver decides once the document's images are fulfilled and its
face set settled, and once the plan's formats are known, held as values so
that everything which must count what a build counts reads the function the
build runs. `Driver.build` calls these; so does the typeset tier
(`scripts/typeset.lean`), which once read a hand copy of the driver's
sequence that skipped them and so counted a document's lost mono slot
nowhere. -/

namespace LeanTex.Cli.PlanLoss

open LeanTex.Core

/-- What a store's decoded images gave up on the way in: each loaded plan's
ledger (`Image.lossDiags` — a dropped colour profile, a dropped orientation
tag), in store order. -/
public def ledger (store : Image.Store) : Array Diag := Id.run do
  let mut ds : Array Diag := #[]
  for en in store.entries do
    if let some pl := en.info then
      let losses := Image.lossDiags en.src pl
      ds := ds ++ losses
  return ds

/-- The alternative judge's picture face over a fulfilled store
(`Ir.picAltDiags`): a boundary picture whose drawn box embeds and carries no
text alternative. A picture the tool failed on ships a placeholder box, not
an image, and W0382 has named that loss, so it is not named here again. -/
public def pictureAlts (doc : Ir.Doc) (imageSpans : Array (String × Span))
    (store : Image.Store) : Array Diag :=
  Ir.picAltDiags doc (fun src => (imageSpans.find? (·.1 == src)).map (·.2))
    (fun src => store.entries.any fun en => en.src == src && en.info.isSome)

/-- The losses the plan's formats decide over the settled face set: each
slot an emitted artifact sets in a face that is not of its kind (W0390), and
each declared contract fact an emitted artifact cannot realize, one W0701
per artifact, per fact (`Ir.contract_accounts`). The slot report sees what
this run emits: the PDF embeds the resolved set, an HTML page does so only
under `fontPolicy = embedded`, and a page under its own stylesheet styles
code from its own monospace stack (`SlotLoss.carries`). -/
public def ofPlan (emit : Array Emit) (fs : Font.FontSet) (doc : Ir.Doc) : Array Diag :=
  -- premise: slotLossChecks — one document, one index, two values of the
  -- gate's own condition: carrying a face reports the lost slot, carrying
  -- none reports nothing.
  SlotLoss.diags doc.fonts fs doc (SlotLoss.carries emit doc.fontPolicy) ++
    (if emit.contains .pdf then Ir.contractDiags (doc.output.contract.unmet Pdf.profile)
     else #[]) ++
    (if emit.contains .html then Ir.contractDiags (doc.output.contract.unmet HtmlDoc.profile)
     else #[])

end LeanTex.Cli.PlanLoss
