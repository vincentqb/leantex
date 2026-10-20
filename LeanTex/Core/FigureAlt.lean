module

public import LeanTex.Core.Ir
public import LeanTex.Core.Diag

/-! An SVG figure's own `<title>` as the alternative of an image whose document declares none (SVG 2 §5.9). -/

namespace LeanTex.Core.FigureAlt

open LeanTex.Core LeanTex.Core.Ir

/-- An image whose alternative is undeclared takes its source's title, where it has one. -/
@[expose] public def titleLeaf (titles : Array (String × String)) (x : Inline) : Inline :=
  match x with
  | .image src size alt =>
    match alt, titles.find? (·.1 == src) with
    | .undeclared, some (_, t) => .image src size (Alt.declare t)
    | .undeclared, none | .decorative, _ | .described _, _ | .citing _, _ => x
  | .text _ | .math _ _ | .formula _ _ _ | .styled _ _ | .colored _ _ _ | .located _ _
  | .role _ _ | .link _ _ | .label _ | .ref _ _ _ _ | .decorated _ _ | .boxed _ _ | .fill | .hspace _ _
  | .rule _ _ _ | .pageNumber | .pageCount | .linebreak _ | .strut _ | .italicCorr _
  | .onSteps _ _ | .altSteps _ _ _ | .icon _ _ | .cite _ _ | .cited _ _ _ | .footnote _ _
  | .marginNote _ _ => x

/-- Every image of the body and the running head and foot whose alternative is undeclared and whose
source names a title takes it, a picture's labels aside; logos stay decorative. -/
public def titled (titles : Array (String × String)) (doc : Doc) : Doc :=
  let logos := logoImageSrcs doc
  let titles := titles.filter fun (src, t) => !logos.contains src && !t.trimAscii.isEmpty
  if titles.isEmpty then doc else
  { doc with body := mapBlocks (titleLeaf titles) doc.body
             head := doc.head.map (mapInlines (titleLeaf titles))
             foot := doc.foot.map (mapInlines (titleLeaf titles)) }

/-- The diagnostics without each N0376 a figure's title answered. -/
public def unanswered (titles : Array (String × String)) (shipped : Doc) (diags : Array Diag) :
    Array Diag :=
  let still := imagesSansAlt shipped
  diags.filter fun d => !(d.kind == .N0376 && d.subject.any fun s =>
    titles.any (·.1 == s) && !still.contains s)

public theorem titled_id (doc : Doc) : titled #[] doc = doc := by
  simp [titled]

public theorem unanswered_accounts (titles : Array (String × String)) (shipped : Doc)
    (diags : Array Diag) (d : Diag) (hd : d ∈ diags) (hn : d ∉ unanswered titles shipped diags) :
    (d.kind == .N0376) = true ∧ ∃ s, d.subject = some s ∧ (∃ t, (s, t) ∈ titles) ∧
      s ∉ imagesSansAlt shipped := by
  simp only [unanswered, Array.mem_filter, hd, true_and, Bool.not_eq_true'] at hn
  simp only [Bool.not_eq_false, Bool.and_eq_true] at hn
  obtain ⟨hk, hs⟩ := hn
  refine ⟨hk, ?_⟩
  cases hsub : d.subject with
  | none => simp [hsub] at hs
  | some s =>
    simp only [hsub, Option.any_some, Bool.and_eq_true, Array.any_eq_true, beq_iff_eq,
      Bool.not_eq_true'] at hs
    obtain ⟨⟨i, hi, hxs⟩, hstill⟩ := hs
    refine ⟨s, rfl, ⟨titles[i].2, ?_⟩, ?_⟩
    · rw [← hxs]
      exact Array.getElem_mem hi
    · intro hm
      have : (imagesSansAlt shipped).contains s = true := Array.contains_iff_mem.mpr hm
      rw [this] at hstill
      cases hstill

end LeanTex.Core.FigureAlt
