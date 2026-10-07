module

public import LeanTex.Core.PdfFontContract
import all LeanTex.Core.Pdf
import all LeanTex.Core.PdfCensus
import all LeanTex.Core.PdfRead

namespace LeanTex.Core.Pdf
open PdfRead PdfCensus

/-! The production object dictionaries satisfy the embedding census.
The reader composition supplies recovered source values; these proofs
establish the font links from the actual preparation code. -/

private theorem find_choice {α : Type} (p : α → Bool)
    (c : Prop) [Decidable c] (xs ys : Array α) :
    (if c then xs else ys).find? p = if c then xs.find? p else ys.find? p := by
  split <;> rfl

private theorem catalog_not_font (root : Option Nat) (xmp : Nat)
    (lang : Option String) (structRoot : Nat) :
    kindOf (catalogDict root xmp lang structRoot) ≠ .font := by
  rw [kindOf_catalog_exact _ (by simp [catalogDict, Obj.get?, Array.find?_append])]
  decide

/-- The dictionaries actually prepared for native fonts satisfy the
read-side census when their source values and references are recovered.
The recovery premises are discharged by the complete reader composition;
the construction of font and descriptor links is proved here. -/
public theorem prepare_census_fonts_exact (geom : Layout.Geom) (fs : Font.FontSet)
    (pages : Array Layout.PageOut) (info : Ir.Meta) (imgs : Image.Store)
    (outline : Array Layout.OutlineEntry)
    (streams : Array (ByteArray × Option ByteArray)) (tree : Struct.Tree)
    (ops : Array (Array ContentOp)) (programs : Array (ByteArray × Bool))
    (trailer : Obj) (es : Array Entry)
    (hfonts : ∀ e ∈ fontEntries es,
      (e.num, e.val) ∈
        (prepare geom fs pages info imgs outline streams tree ops programs).compressed)
    (href : ∀ id v,
      (id,v) ∈ (prepare geom fs pages info imgs outline streams tree ops programs).compressed →
        deref es (.ref id 0) = v) :
    (ofEntries trailer es).fontsEmbedded = true := by
  apply (census_fontsEmbedded_exact trailer es).2
  intro e he
  have hf : kindOf e.val = .font := by
    exact beq_iff_eq.mp (Array.mem_filter.mp he).2
  have hm := hfonts e he
  generalize ht : (prepare geom fs pages info imgs outline streams tree ops programs).table = t
  simp only [prepare, Id.run, pure, bind] at ht
  simp only [prepare, Id.run, pure, bind] at hm href
  rw [ht] at hm href
  generalize hk : keepOf (usedAll fs pages) = keep at hm href
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hm
  rcases hm with (((((hcat | hpages) | hfont) | hinfo) | hout) | hpage) | hstruct
  · rw [hcat.2] at hf
    exact False.elim (catalog_not_font _ _ _ _ hf)
  · rw [hpages.2, kindOf_pages_exact _ (by simp [Obj.get?])] at hf
    contradiction
  · obtain ⟨k, hk, hrow⟩ := List.mem_flatMap.mp hfont
    apply fontObjects_rows_embedded_exact _ k _ _ _ es e hrow hf
    apply href
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply List.mem_flatMap.mpr
    exact ⟨k, hk, by simp [FontObjects.rows]⟩
  · rw [hinfo.2] at hf
    apply False.elim
    apply kindOf_no_subtype_not_font _ ?_ ?_ hf
    all_goals
      cases info.title <;> cases info.author <;> cases info.subject <;> cases info.keywords <;>
        simp [Obj.get?]
  · split at hout
    · simp at hout
    · simp only [List.mem_cons, Prod.mk.injEq] at hout
      rcases hout with hroot | hitems
      · rw [hroot.2] at hf
        exact False.elim (kindOf_no_subtype_not_font _
          (by simp [Obj.get?]) (by simp [Obj.get?]) hf)
      · obtain ⟨⟨ol, k⟩, hk, heq⟩ := List.mem_map.mp hitems
        have hv := congrArg Prod.snd heq
        dsimp only at hv
        rw [← hv] at hf
        apply False.elim
        apply kindOf_no_subtype_not_font _ ?_ ?_ hf
        all_goals
          cases ol.page <;> cases ol.url <;>
            simp only [Obj.get?, Array.find?_append, find_choice,
              Array.find?_empty] <;> simp
  · obtain ⟨i, hi, heq⟩ := List.mem_map.mp hpage
    have hv := congrArg Prod.snd heq
    dsimp only at hv
    rw [← hv, kindOf_page_exact _ (by simp [Obj.get?, Array.find?_append])] at hf
    contradiction
  · rcases hstruct with (hroot | hparent | hns) | helems
    · rw [hroot.2] at hf
      apply False.elim
      apply kindOf_no_subtype_not_font _ ?_ ?_ hf
      all_goals
        simp only [Obj.get?, Array.find?_append, find_choice,
          Array.find?_empty]
        simp
    · rw [hparent.2] at hf
      exact False.elim (kindOf_no_subtype_not_font _
        (by simp [Obj.get?]) (by simp [Obj.get?]) hf)
    · rw [hns.2] at hf
      split at hf <;>
        exact False.elim (kindOf_no_subtype_not_font _
          (by simp [Obj.get?]) (by simp [Obj.get?]) hf)
    · obtain ⟨⟨se, i⟩, hi, heq⟩ := List.mem_map.mp helems
      have hv := congrArg Prod.snd heq
      dsimp only at hv
      rw [← hv] at hf
      apply False.elim
      apply kindOf_no_subtype_not_font _ ?_ ?_ hf
      all_goals
        cases se.alt <;> cases se.lang <;> cases se.actualText <;>
          simp only [Obj.get?, Array.find?_append, find_choice,
            Array.find?_empty] <;> simp

end LeanTex.Core.Pdf
