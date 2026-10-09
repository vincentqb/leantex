module

public import LeanTex.Core.Pdf
import all LeanTex.Core.Pdf

namespace LeanTex.Core.Pdf

/-! The producer's two emission transcripts partition its allocation.
The statements concern source ids, independently of bytes or parsing. -/

private theorem count_flatMap_cons {α : Type} (xs : List α)
    (f : α → Nat) (g : α → List Nat) (n : Nat) :
    (xs.flatMap fun x => f x :: g x).count n =
      (xs.map f).count n + (xs.flatMap g).count n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.count_append, List.count_cons,
      List.map_cons, ih]
    omega

private theorem allocation_perm (t : ObjTable) :
    (([1, 2] ++ (List.range t.nf).flatMap (fun k =>
        [ObjTable.type0Id k, ObjTable.cidId k, ObjTable.fdId k]) ++
      [t.infoId] ++
      (if t.nOut == 0 then [] else t.outlineRootId ::
        (List.range t.nOut).map t.outlineItemId) ++
      (List.range t.np).map t.pageId ++
      [t.structTreeRoot, t.parentTree, t.namespaceId] ++
      (List.range t.nElems).map t.structElemId) ++
      ((List.range t.np).map t.contentId ++
        ((t.imgIds.zip t.imgSpans).toList.flatMap fun p : Nat × Nat =>
          List.range' p.1 p.2) ++
        (List.range t.nf).flatMap (fun k => [ObjTable.toUniId k, t.fileId k]) ++
        [t.xmpId]) ++ (List.range t.nStm).map t.objStmId ++ [t.xrefId]).Perm t.ids.toList := by
  apply List.perm_iff_count.mpr
  intro n
  have split3 := count_flatMap_cons (List.range t.nf) ObjTable.type0Id
    (fun k => [ObjTable.cidId k, ObjTable.fdId k]) n
  have split2 := count_flatMap_cons (List.range t.nf) ObjTable.cidId
    (fun k => [ObjTable.fdId k]) n
  have split4 := count_flatMap_cons (List.range t.nf) ObjTable.type0Id
    (fun k => [ObjTable.cidId k, ObjTable.fdId k, ObjTable.toUniId k]) n
  have split3' := count_flatMap_cons (List.range t.nf) ObjTable.cidId
    (fun k => [ObjTable.fdId k, ObjTable.toUniId k]) n
  have split2' := count_flatMap_cons (List.range t.nf) ObjTable.fdId
    (fun k => [ObjTable.toUniId k]) n
  have splitfiles := count_flatMap_cons (List.range t.nf) ObjTable.toUniId
    (fun k => [t.fileId k]) n
  have splitpages := count_flatMap_cons (List.range t.np) t.pageId
    (fun k => [t.contentId k]) n
  by_cases ho : t.nOut == 0
  all_goals simp only [ObjTable.ids, ho, Bool.false_eq_true, ↓reduceIte,
    Array.toList_append, Array.toList_flatMap,
    Array.toList_map, Array.toList_range, Array.toList_range',
    List.count_append,
    split3, split2, split4, split3', split2', splitfiles, splitpages,
    ← List.map_eq_flatMap,
    List.count_cons, List.count_nil, Nat.add_zero, Nat.zero_add]
  all_goals ac_rfl

/-- The actual compressed and direct transcripts, with the object-stream
ids and the xref's, are a permutation of every allocated slot. Thus no
source id can be silently replaced by another emission with the same
number. -/
public theorem prepare_allocation_exact (geom : Layout.Geom) (fs : Font.FontSet)
    (pages : Array Layout.PageOut) (info : Ir.Meta) (imgs : Image.Store)
    (outline : Array Layout.OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (ops : Array (Array ContentOp)) (programs : Array (ByteArray × Bool)) :
    let p := prepare geom fs pages info imgs outline streams tree ops programs
    (p.compressed.map Prod.fst ++ p.direct.toList.map Row.id ++
      (List.range p.table.nStm).map p.table.objStmId ++ [p.table.xrefId]).Perm
        p.table.ids.toList := by
  dsimp only
  rw [prepare_compressed_ids_exact, prepare_direct_ids_exact]
  exact allocation_perm _

/-- Every producer allocation is the consecutive positive range named
by its trailer, regardless of caches, images, or structure input. -/
public theorem prepare_ids_exact (geom : Layout.Geom) (fs : Font.FontSet)
    (pages : Array Layout.PageOut) (info : Ir.Meta) (imgs : Image.Store)
    (outline : Array Layout.OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (ops : Array (Array ContentOp)) (programs : Array (ByteArray × Bool)) :
    let p := prepare geom fs pages info imgs outline streams tree ops programs
    p.table.ids.toList = List.range' 1 (p.table.size - 1) := by
  dsimp only
  rw [prepare_table_exact]
  exact objTable_ids_exact ..

/-- The writer always has the catalog to compress, so it always writes at
least one object stream. -/
public theorem prepare_compressed_ne_nil (geom : Layout.Geom) (fs : Font.FontSet)
    (pages : Array Layout.PageOut) (info : Ir.Meta) (imgs : Image.Store)
    (outline : Array Layout.OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (ops : Array (Array ContentOp)) (programs : Array (ByteArray × Bool)) :
    (prepare geom fs pages info imgs outline streams tree ops programs).compressed ≠ [] := by
  intro h
  have hc := prepare_compressed_ids_exact geom fs pages info imgs outline streams tree ops programs
  dsimp only at hc
  rw [h] at hc
  simp at hc

/-- The production emissions themselves have unique ids; this is
stronger than allocation coverage and prevents last-write-wins aliases. -/
public theorem prepare_emission_inj (geom : Layout.Geom) (fs : Font.FontSet)
    (pages : Array Layout.PageOut) (info : Ir.Meta) (imgs : Image.Store)
    (outline : Array Layout.OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (ops : Array (Array ContentOp)) (programs : Array (ByteArray × Bool)) :
    let p := prepare geom fs pages info imgs outline streams tree ops programs
    (p.compressed.map Prod.fst ++ p.direct.toList.map Row.id ++
      (List.range p.table.nStm).map p.table.objStmId ++ [p.table.xrefId]).Nodup := by
  apply (prepare_allocation_exact geom fs pages info imgs outline streams tree ops programs).symm.nodup
  rw [prepare_ids_exact]
  exact List.nodup_range' 1

end LeanTex.Core.Pdf
