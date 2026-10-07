module

public import LeanTex.Core.Ir
import all LeanTex.Core.Ir

namespace LeanTex.Core.Elab

open Ir

/-- Only an engine picture block contributes to this census. -/
private def pictureCountStep (n : Nat) : Block → Nat
  | .picture _ => n + 1
  | _ => n

/-- Engine pictures at every body depth. Boundary images have no picture
block and cannot silence losses in engine pictures beside them. -/
public def enginePictures (blocks : Array Block) : Nat :=
  Ir.foldBlocks pictureCountStep (fun n _ => n) 0 blocks

mutual

private theorem inlinePictureCount_id (n : Nat) (x : Inline) :
    foldInline (fun n _ => n) n x = n := by
  match x with
  | .styled _ body | .colored _ _ body | .located _ body | .role _ body
  | .link _ body | .decorated _ body | .onSteps _ body | .footnote _ body =>
    exact inlineListPictureCount_id n body.toList
  | .altSteps _ active other =>
    simp only [foldInline, inlineListPictureCount_id]
  | .text _ | .math _ _ | .formula _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .fill | .hspace _ _ | .rule _ _ _
  | .strut _ | .italicCorr _ | .pageNumber | .pageCount | .linebreak _ => rfl

private theorem inlineListPictureCount_id (n : Nat) (xs : List Inline) :
    foldInlineList (fun n _ => n) n xs = n := by
  match xs with
  | [] => rfl
  | x :: rest =>
    rw [foldInlineList, inlinePictureCount_id n x, inlineListPictureCount_id n rest]

end

private theorem cellsPictureCount_id (n : Nat) (xs : List (Array Inline)) :
    foldTableCells (fun n _ => n) n xs = n := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simpa only [foldTableCells, inlineListPictureCount_id] using ih

private theorem rowsPictureCount_id (n : Nat) (xs : List (Array (Array Inline))) :
    foldTableRows (fun n _ => n) n xs = n := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simpa only [foldTableRows, cellsPictureCount_id] using ih

private theorem algPictureCount_id (n : Nat) (xs : List AlgLine) :
    foldAlgLines (fun n _ => n) n xs = n := by
  induction xs with
  | nil => rfl
  | cons line _ ih =>
    cases h : line.comment <;>
      simpa only [foldAlgLines, h, inlineListPictureCount_id] using ih

private theorem mapBlockListWith_toList (gp : Pic.Picture → Pic.Picture)
    (f : Inline → Inline) (finish : Array Inline → Array Inline)
    (listing : ListingSpec → ListingSpec) (out : Array Block) (xs : List Block) :
    (mapBlockList gp f out xs finish listing).toList =
      out.toList ++ xs.map (fun b => mapBlock gp f b finish listing) := by
  induction xs generalizing out with
  | nil => simp [mapBlockList]
  | cons _ _ ih => simp [mapBlockList, ih, List.append_assoc]

private theorem mapBlockItemsWith_toList (gp : Pic.Picture → Pic.Picture)
    (f : Inline → Inline) (finish : Array Inline → Array Inline)
    (listing : ListingSpec → ListingSpec) (out : Array (Array Block))
    (xs : List (Array Block)) :
    (mapBlockItems gp f out xs finish listing).toList =
      out.toList ++ xs.map (fun b => mapBlockList gp f #[] b.toList finish listing) := by
  induction xs generalizing out with
  | nil => simp [mapBlockItems]
  | cons _ _ ih => simp [mapBlockItems, ih, List.append_assoc]

private theorem mapBlockColsWith_toList (gp : Pic.Picture → Pic.Picture)
    (f : Inline → Inline) (finish : Array Inline → Array Inline)
    (listing : ListingSpec → ListingSpec) (out : Array (BoxWidth × Array Block))
    (xs : List (BoxWidth × Array Block)) :
    (mapBlockCols gp f out xs finish listing).toList =
      out.toList ++ xs.map (fun b => (b.1, mapBlockList gp f #[] b.2.toList finish listing)) := by
  induction xs generalizing out with
  | nil => simp [mapBlockCols]
  | cons x _ ih => cases x; simp [mapBlockCols, ih, List.append_assoc]

mutual

private theorem mapBlock_pictureCount (gp : Pic.Picture → Pic.Picture)
    (f : Inline → Inline) (finish : Array Inline → Array Inline)
    (listing : ListingSpec → ListingSpec) (n : Nat) (b : Block) :
    foldBlock pictureCountStep (fun n _ => n) n (mapBlock gp f b finish listing) =
      foldBlock pictureCountStep (fun n _ => n) n b := by
  match b with
  | .para _ | .equation _ _ | .section _ _ _ _ | .framefoot _ | .logo _ =>
    simp only [mapBlock, foldBlock, pictureCountStep, inlineListPictureCount_id]
  | .list _ items =>
    simp only [mapBlock, foldBlock, pictureCountStep, mapBlockItemsWith_toList, List.nil_append]
    exact mapItems_pictureCount gp f finish listing n items.toList
  | .columns cols =>
    simp only [mapBlock, foldBlock, pictureCountStep, mapBlockColsWith_toList, List.nil_append]
    exact mapCols_pictureCount gp f finish listing n cols.toList
  | .center body | .ragged _ body | .quote body | .abstract body
  | .role _ body | .link _ body | .spaced _ body | .onSteps _ body
  | .only _ body | .nav _ body | .note body
  | .titled _ _ body | .frame _ _ _ _ body | .float _ _ _ body _ =>
    simp only [mapBlock, foldBlock, pictureCountStep, inlineListPictureCount_id,
      mapBlockListWith_toList, List.nil_append]
    exact mapList_pictureCount gp f finish listing n body.toList
  | .altSteps _ active other =>
    simp only [mapBlock, foldBlock, pictureCountStep, mapBlockListWith_toList, List.nil_append]
    rw [mapList_pictureCount gp f finish listing n active.toList,
      mapList_pictureCount gp f finish listing _ other.toList]
  | .table _ _ _ _ _ _ =>
    simp only [mapBlock, foldBlock, pictureCountStep, rowsPictureCount_id]
  | .algorithm _ _ _ =>
    simp only [mapBlock, foldBlock, pictureCountStep, algPictureCount_id]
  | .verbatim _ _ _ | .bibliography _ _ _ | .setPalette _ | .setTokens _
  | .pagebreak | .rule _ _ _ | .picture _ => rfl

private theorem mapList_pictureCount (gp : Pic.Picture → Pic.Picture)
    (f : Inline → Inline) (finish : Array Inline → Array Inline)
    (listing : ListingSpec → ListingSpec) (n : Nat) (xs : List Block) :
    foldBlockList pictureCountStep (fun n _ => n) n
      (xs.map (fun b => mapBlock gp f b finish listing)) =
      foldBlockList pictureCountStep (fun n _ => n) n xs := by
  match xs with
  | [] => rfl
  | x :: rest =>
    rw [List.map_cons, foldBlockList, mapBlock_pictureCount gp f finish listing n x,
      mapList_pictureCount gp f finish listing _ rest, foldBlockList]

private theorem mapItems_pictureCount (gp : Pic.Picture → Pic.Picture)
    (f : Inline → Inline) (finish : Array Inline → Array Inline)
    (listing : ListingSpec → ListingSpec) (n : Nat) (xs : List (Array Block)) :
    foldBlockItems pictureCountStep (fun n _ => n) n
      (xs.map (fun b => mapBlockList gp f #[] b.toList finish listing)) =
      foldBlockItems pictureCountStep (fun n _ => n) n xs := by
  match xs with
  | [] => rfl
  | x :: rest =>
    simp only [List.map_cons, foldBlockItems, mapBlockListWith_toList, List.nil_append]
    rw [mapList_pictureCount gp f finish listing n x.toList,
      mapItems_pictureCount gp f finish listing _ rest]

private theorem mapCols_pictureCount (gp : Pic.Picture → Pic.Picture)
    (f : Inline → Inline) (finish : Array Inline → Array Inline)
    (listing : ListingSpec → ListingSpec) (n : Nat) (xs : List (BoxWidth × Array Block)) :
    foldBlockCols pictureCountStep (fun n _ => n) n
      (xs.map (fun b => (b.1, mapBlockList gp f #[] b.2.toList finish listing))) =
      foldBlockCols pictureCountStep (fun n _ => n) n xs := by
  match xs with
  | [] => rfl
  | (_, body) :: rest =>
    simp only [List.map_cons, foldBlockCols, mapBlockListWith_toList, List.nil_append]
    rw [mapList_pictureCount gp f finish listing n body.toList,
      mapCols_pictureCount gp f finish listing _ rest]

end

/-- An inline, listing or picture-payload rewrite preserves the number of
engine picture blocks, for arbitrary nested block structure. -/
public theorem mapBlocksPic_pictureCount_exact (gp : Pic.Picture → Pic.Picture)
    (f : Inline → Inline) (finish : Array Inline → Array Inline)
    (listing : ListingSpec → ListingSpec) (blocks : Array Block) :
    enginePictures (mapBlocksPic gp f blocks finish listing) = enginePictures blocks := by
  simp only [enginePictures, foldBlocks, mapBlocksPic, mapBlockListWith_toList, List.nil_append]
  exact mapList_pictureCount gp f finish listing 0 blocks.toList

/-- Final source-location erasure does not change the gate on unread
picture settings. Both artifacts receive this same document body. -/
public theorem eraseLocations_pictureCount_exact (doc : Doc) :
    enginePictures (Ir.eraseLocations doc).body = enginePictures doc.body := by
  exact mapBlocksPic_pictureCount_exact _ _ _ _ doc.body

end LeanTex.Core.Elab
