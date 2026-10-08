module

import LeanTex.Core.ListMark
import LeanTex.Core.Struct

/-! Ordinary clients can build markers, read the semantic tree and use its
census contracts. The reduction checks pin exactly the bodies read by
HtmlDoc, Elab, Layout and PdfStruct; the negative checks keep the supporting
decoders, numbering step and alternative-census implementation private. -/

open LeanTex.Core

namespace Tests.StructureInterface

example : Bool → Nat → Nat → (Char → Bool) → Array Ir.Inline := ListMark.marker
example : Bool → Nat → String := ListMark.scalars
example : List Char → Nat := ListMark.romanVal

example (n : Nat) :
    ListMark.arabicN n = String.ofList (ListMark.digitsRev n).reverse := rfl

example (n : Nat) :
    ListMark.AlphN n = ListMark.letterN 'A'.toNat n := rfl

example {m n : Nat} (h : ListMark.arabicN m = ListMark.arabicN n) : m = n :=
  ListMark.arabicN_inj h

example {level m n : Nat} (hl : level ≠ 3)
    (h : ListMark.enumLabel level m = ListMark.enumLabel level n) : m = n :=
  ListMark.enumLabel_inj hl h

example (level n : Nat) (covered : Char → Bool) :
    Ir.plainText (ListMark.marker true level n covered) = ListMark.enumLabel level n :=
  ListMark.ordered_marker_shows_order level n covered

example : BEq Struct.Kind := inferInstance
example : Repr Struct.Leaf := inferInstance
example : Inhabited Struct.Node := inferInstance
example : Repr Struct.Tree := inferInstance

example : Ir.Doc → Struct.Tree := Struct.ofDoc
example : Struct.Tree → String := Struct.Tree.text
example : Struct.Tree → Array (Nat × Struct.Leaf) := Struct.Tree.leaves
example : Struct.Tree → Array Ir.HeadingLevel := Struct.Tree.headings
example : Struct.Tree → Array (Option String × Ir.Alt) := Struct.Tree.alts

example (doc : Ir.Doc) : (Struct.ofDoc doc).text = Ir.blocksText doc.body :=
  Struct.ofDoc_text doc

example (bs : Array Ir.Block) :
    Struct.headings (Struct.ofBlocks bs) = Ir.headingLevels bs :=
  Struct.structTree_headings_covers bs

example (bs : Array Ir.Block) :
    Struct.alts (Struct.ofBlocks bs) = Struct.irAlts bs :=
  Struct.structTree_alts_covers bs

example (k : Nat) (ns : List Struct.Node) :
    (Struct.leavesList #[] (Struct.numberList k #[] ns).1.toList).size =
      (Struct.leavesList #[] ns).size :=
  Struct.numberList_leafCount k ns

example (xs : Array Ir.Inline) :
    Struct.leafCountBlocks #[.para xs] = Struct.leafCountInlines xs := by
  simp [Struct.leafCountBlocks, Struct.blocksRaw, Struct.blockRaw, Struct.leaves,
    Struct.leavesList_cons_exact, Struct.leavesOne_node_exact,
    Struct.leavesList_nil_exact, Struct.leafCountInlines]

example (out : Array (Nat × Struct.Leaf)) (id : Nat) (l : Struct.Leaf) :
    Struct.foldNode Struct.leavesFold out (.leaf id l) = out.push (id, l) := by
  rw [Struct.foldNode_leaf_exact]
  rfl

example (kind : Struct.Kind) (kids : Array Struct.Node) :
    Struct.leavesOne #[] (.node kind kids) = Struct.leavesList #[] kids.toList := by
  rw [Struct.leavesOne, Struct.foldNode_node_exact]
  simp [Struct.leavesFold, Struct.leavesList]

example : (Struct.Leaf.picture .decorative).held = false := rfl
example : Struct.Kind.outlineDescends .aside = false := rfl

-- The exposed block equation can name its title builder, but ordinary
-- clients cannot unfold that builder's implementation.
example : Array Ir.Inline → Array Struct.Node := Struct.titleRaw

example (_xs : Array Ir.Inline) : True := by
  fail_if_success
    have : Struct.titleRaw _xs =
        if _xs.isEmpty then #[] else #[.node .title (Struct.inlinesRaw #[] _xs.toList)] := by
      rfl
  trivial

example : True := by
  fail_if_success have := LeanTex.Core.ListMark.digitVal
  fail_if_success have := LeanTex.Core.ListMark.undigitsRev
  fail_if_success have := LeanTex.Core.ListMark.romanTable
  fail_if_success have := LeanTex.Core.ListMark.romanCharVal
  fail_if_success have := LeanTex.Core.ListMark.itemGlyph
  fail_if_success have := LeanTex.Core.Struct.cellsRaw
  fail_if_success have := LeanTex.Core.Struct.numberOne
  fail_if_success have := LeanTex.Core.Struct.leafTextFold
  fail_if_success have := LeanTex.Core.Struct.headingsFold
  fail_if_success have := LeanTex.Core.Struct.altsFold
  fail_if_success have := LeanTex.Core.Struct.altPush
  fail_if_success have := LeanTex.Core.Struct.range'_join
  trivial

end Tests.StructureInterface
