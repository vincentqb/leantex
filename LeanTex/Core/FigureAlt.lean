module

public import LeanTex.Core.Ir
public import LeanTex.Core.Diag

/-!
# A figure's own title as its alternative

An SVG may name itself: its root's `<title>` is the figure's accessible
name in every viewer that reads the file (SVG 2 §5.9). Where the document
declares no alternative for the image — no `alt=`, no `artifact`, no
caption — that title is the alternative both artifacts ship: one IR value
(`Ir.Alt.described`), so the PDF's structure element and the page's name
read the same words. A declared alternative, a decorative mark and a
caption all stand; and a logo is decorative furniture by role, whatever its
file says (`Ir.logoImageSrcs`).
-/

namespace LeanTex.Core.FigureAlt

open LeanTex.Core LeanTex.Core.Ir

/-- One leaf: an image whose alternative is undeclared takes its source's
title, where the source has one; every other node is itself. -/
@[expose] public def titleLeaf (titles : Array (String × String)) (x : Inline) : Inline :=
  match x with
  | .image src size alt =>
    match alt, titles.find? (·.1 == src) with
    | .undeclared, some (_, t) => .image src size (Alt.declare t)
    | .undeclared, none | .decorative, _ | .described _, _ => x
  | .text _ | .math _ _ | .formula _ _ _ | .styled _ _ | .colored _ _ _ | .located _ _
  | .role _ _ | .link _ _ | .label _ | .ref _ _ _ _ | .decorated _ _ | .fill | .hspace _ _
  | .rule _ _ _ | .pageNumber | .pageCount | .linebreak _ | .strut _ | .italicCorr _
  | .onSteps _ _ | .altSteps _ _ _ | .icon _ _ | .cite _ _ | .footnote _ _ => x

/-- **Every image of the document whose alternative is undeclared and whose
source names a title takes it**: the body, the running head and foot. A
picture's labels are not this map's leaves (`Ir.mapBlocks`): an image a
picture label sets is the picture's ink, named by the picture's own
alternative. Logos keep their decorative role. -/
public def titled (titles : Array (String × String)) (doc : Doc) : Doc :=
  let logos := logoImageSrcs doc
  let titles := titles.filter fun (src, t) => !logos.contains src && !t.trimAscii.isEmpty
  if titles.isEmpty then doc else
  { doc with body := mapBlocks (titleLeaf titles) doc.body
             head := doc.head.map (mapInlines (titleLeaf titles))
             foot := doc.foot.map (mapInlines (titleLeaf titles)) }

/-- The document's diagnostics with each N0376 a figure's title answered
taken out: an image its source's title names ships an alternative, so the
judge's census of the shipped document (`Ir.imagesSansAlt`) no longer
holds it. Every other diagnostic stands, an N0376 for a titled source the
shipped document still lacks an alternative for included. -/
public def unanswered (titles : Array (String × String)) (shipped : Doc) (diags : Array Diag) :
    Array Diag :=
  let still := imagesSansAlt shipped
  diags.filter fun d => !(d.kind == .N0376 && d.subject.any fun s =>
    titles.any (·.1 == s) && !still.contains s)

/-- **No title, no change** (`_id`): a document whose figures name no title
is the document itself. -/
public theorem titled_id (doc : Doc) : titled #[] doc = doc := by
  simp [titled]

/-- **A dropped diagnostic is paid for** (`_accounts`): `unanswered` keeps
every diagnostic but an N0376 whose source a title names and whose shipped
image holds an alternative — what drops it is the alternative the shipped
document carries, never the title alone. -/
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
