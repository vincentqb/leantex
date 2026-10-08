module

public import LeanTex.Core.PdfStruct

public section

open LeanTex.Core

/-! Parent-tree coherence is universal in `Pdf.doc_parentTree_covers`.
These boundary cases also retain counterexamples to dropping freshness,
unique ownership, or positional stream numbering from the general claim. -/

private def staleElements : Array Pdf.StructElem :=
  #[{ s := "Document", kids := #[.mcid 0 0] }]

example : ¬ Pdf.Unfilled staleElements := by
  intro h
  exact h { s := "Document", kids := #[.mcid 0 0] }
    (by simp [staleElements]) 0 0 (by simp)

def pdfStructCoherenceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := fun (name : String) (ok : Bool) =>
    unless ok do ref.modify (s!"PDF structure coherence: {name}" :: ·)
  let emptyMarks : Array (Array (Nat × Nat)) := #[]
  t "a pre-existing reference survives fill without a parent entry"
    (Pdf.leafKids staleElements == [] &&
      (Pdf.fill staleElements (Pdf.leafPagesOf 0 emptyMarks))[0]!.kids == #[.mcid 0 0] &&
      ((Pdf.parentTreeOf emptyMarks (Pdf.leafOwners staleElements 0))[0]?).bind (·[0]?)
        == none)
  let es : Array Pdf.StructElem := #[
    { s := "Document", kids := #[.elem 1, .elem 2] },
    { s := "P", kids := #[.leaf 2] },
    { s := "Figure", kids := #[.leaf 0] }]
  let marks := #[#[(0, 2), (1, 0), (2, 2)], #[], #[(0, 0), (1, 99), (2, 2)]]
  let lp := Pdf.leafPagesOf 4 marks
  let owners := Pdf.leafOwners es 4
  let filled := Pdf.fill es lp
  t "sparse ownership keeps unowned slots empty"
    (owners == #[some 2, none, some 1, none])
  t "repeated leaves retain every occurrence and empty pages retain their index"
    (lp == #[#[(0, 1), (2, 0)], #[], #[(0, 0), (0, 2), (2, 2)], #[]])
  t "fill retains element links and assigns references to their leaf's owner"
    (filled[0]!.kids == #[.elem 1, .elem 2] &&
      filled[1]!.kids == #[.mcid 0 0, .mcid 0 2, .mcid 2 2] &&
      filled[2]!.kids == #[.mcid 0 1, .mcid 2 0])
  t "parent entries invert every filled reference"
    (Pdf.parentTreeOf marks owners ==
      #[#[some 1, some 2, some 1], #[], #[some 2, none, some 1]])
  let duplicate : Array Pdf.StructElem :=
    #[{ s := "P", kids := #[.leaf 0] }, { s := "P", kids := #[.leaf 0] }]
  t "duplicate ownership cannot certify the earlier holder"
    ((Pdf.fill duplicate (Pdf.leafPagesOf 1 #[#[(0, 0)]]))[0]!.kids == #[.mcid 0 0] &&
      Pdf.parentTreeOf #[#[(0, 0)]] (Pdf.leafOwners duplicate 1) == #[#[some 1]])
  let single : Array Pdf.StructElem := #[{ s := "P", kids := #[.leaf 0] }]
  let nonpositional := #[#[(9, 0)]]
  t "nonpositional identifiers cannot be used as parent-tree array indices"
    ((Pdf.fill single (Pdf.leafPagesOf 1 nonpositional))[0]!.kids == #[.mcid 0 9] &&
      ((Pdf.parentTreeOf nonpositional (Pdf.leafOwners single 1))[0]?).bind (·[9]?)
        == none)
