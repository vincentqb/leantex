module

public import LeanTex.Core.HtmlDoc
public import LeanTex.Core.HtmlReadProof
import all LeanTex.Core.HtmlDoc

/-! The text the HTML emitter's inline nodes hold, against the IR's plain text. -/

namespace LeanTex.Core.HtmlDoc

open LeanTex.Core LeanTex.Core.Ir LeanTex.Core.Dim LeanTex.Core.Html

mutual

-- conserves: none — a predicate the proof reads in the emitter's own recursion shape
/-- Whether the emitted nodes hold an inline's plain text: no picture, formula, icon, note, overlay
alternation or paged reference inside, nor an aside where `asides` sets margin notes apart. -/
@[expose] public def inkPlainList (asides : Bool) : List Inline → Bool
  | [] => true
  | x :: rest => inkPlainOne asides x && inkPlainList asides rest

@[expose] public def inkPlainOne (asides : Bool) : Inline → Bool
  | .text _ | .math _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _
  | .pageNumber | .pageCount | .label _ | .cite _ _ | .linebreak _ => true
  | .styled _ body | .colored _ _ body | .located _ body | .role _ body | .link _ body
  | .decorated _ body | .boxed _ body | .onSteps _ body | .cited _ _ body =>
    inkPlainList asides body.toList
  | .marginNote _ body => !asides && inkPlainList asides body.toList
  | .ref _ form _ _ => !form.paged
  | .image _ _ _ | .formula _ _ _ | .icon _ _ | .footnote _ _ | .altSteps _ _ _ => false

end

/-- The characters a node array's text holds, white space aside. -/
private abbrev seen (a : Array Node) : List Char := (Node.inkList a.toList).filter inked

private abbrev plain (s : String) : List Char := s.toList.filter inked

private theorem inkList_append (a b : List Node) :
    Node.inkList (a ++ b) = Node.inkList a ++ Node.inkList b := by
  induction a with
  | nil => rfl
  | cons n rest ih => simp [Html.inkList_cons, ih]

private theorem seen_push (a : Array Node) (n : Node) :
    seen (a.push n) = seen a ++ (Node.ink n).filter inked := by
  simp only [seen, Array.toList_push, inkList_append, List.filter_append]
  congr 1

private theorem seen_append (a b : Array Node) : seen (a ++ b) = seen a ++ seen b := by
  simp [seen, inkList_append]

@[simp] private theorem seen_empty : seen #[] = [] := rfl

private theorem ink_elemFn (tag : String) (kids : Array Node) (a : Array (String × String))
    (h : (HtmlRead.lower tag == "style" || HtmlRead.lower tag == "script") = false) :
    (Node.ink (Html.elem tag kids a)).filter inked = seen kids := by
  simp [Html.elem, Html.ink_elem, h, seen]

private theorem ink_text (s : String) : (Node.ink (Html.text s)).filter inked = plain s := rfl

private theorem plainText_one_list (x : Inline) (rest : List Inline) :
    plain (Ir.plainTextList (x :: rest)) =
      plain (Ir.plainTextOne x) ++ plain (Ir.plainTextList rest) := by
  simp [plain, Ir.plainTextList, List.filter_append]

private theorem seen_hspace (cfg : Config) (acc : Array Node) (e : Affine Measure) (keep : Bool) :
    seen (inlineNodeInto cfg acc (.hspace e keep)) = seen acc := by
  simp only [inlineNodeInto]
  split <;> simp [seen_push, ink_elemFn, HtmlRead.lower]

private theorem nodesInto_cons (cfg : Config) (acc : Array Node) (x : Inline) (rest : List Inline) :
    (inlineNodesInto cfg acc (x :: rest) = inlineNodesInto cfg acc rest ∧
      Ir.plainTextOne x = "") ∨
    inlineNodesInto cfg acc (x :: rest) = inlineNodesInto cfg (inlineNodeInto cfg acc x) rest := by
  cases x with
  | hspace e keep =>
    cases keep with
    | false => right; simp only [inlineNodesInto]
    | true =>
      simp only [inlineNodesInto]
      split
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr rfl
  | _ => right; simp only [inlineNodesInto]

@[simp] private theorem inked_space : inked ' ' = false := rfl

private theorem seen_single (n : Node) : seen #[n] = (Node.ink n).filter inked := by
  simpa using seen_push #[] n

private theorem seen_pair (m n : Node) :
    seen #[m, n] = (Node.ink m).filter inked ++ (Node.ink n).filter inked := by
  simpa [seen_single] using seen_push #[m] n

mutual

private theorem nodesInto_seen (cfg : Config) (acc : Array Node) :
    ∀ xs : List Inline, inkPlainList cfg.marginAsides xs = true →
      seen (inlineNodesInto cfg acc xs) = seen acc ++ plain (Ir.plainTextList xs)
  | [] => fun _ => by simp [inlineNodesInto, plain, Ir.plainTextList]
  | x :: rest => fun h => by
    simp only [inkPlainList, Bool.and_eq_true] at h
    rw [plainText_one_list]
    rcases nodesInto_cons cfg acc x rest with ⟨he, hs⟩ | he
    · rw [he, nodesInto_seen cfg acc rest h.2, hs]
      rfl
    · rw [he, nodesInto_seen cfg _ rest h.2, nodeInto_seen cfg acc x h.1, List.append_assoc]

private theorem nodeInto_seen (cfg : Config) (acc : Array Node) (x : Inline)
    (h : inkPlainOne cfg.marginAsides x = true) :
    seen (inlineNodeInto cfg acc x) = seen acc ++ plain (Ir.plainTextOne x) := by
  match x with
  | .text s => simp [inlineNodeInto, seen_push, ink_text, Ir.plainTextOne]
  | .math d src =>
    cases d <;> simp [inlineNodeInto, seen_push, seen_single, ink_elemFn, ink_text, HtmlRead.lower,
      Ir.plainTextOne]
  | .styled st body =>
    simp only [inkPlainOne] at h
    have ih := fun (c : Config) (hc : c.marginAsides = cfg.marginAsides) =>
      nodesInto_seen c #[] body.toList (hc ▸ h)
    simp only [seen_empty, List.nil_append] at ih
    cases st <;> simp [inlineNodeInto, seen_push, ink_elemFn, HtmlRead.lower, ih, Ir.plainTextOne]
    split
    · rename_i hk
      have := ih { cfg with mathStyles := cfg.mathStyles.push .normal } rfl
      rw [hk] at this
      simp [← this]
    · simp [seen_push, ink_elemFn, HtmlRead.lower, ih]
  | .colored _ _ body =>
    simp only [inkPlainOne] at h
    have ih := fun (c : Config) (hc : c.marginAsides = cfg.marginAsides) =>
      nodesInto_seen c #[] body.toList (hc ▸ h)
    simp only [seen_empty, List.nil_append] at ih
    simp [inlineNodeInto, seen_push, ink_elemFn, HtmlRead.lower, ih, Ir.plainTextOne]
  | .decorated kind body =>
    simp only [inkPlainOne] at h
    have ih := fun (c : Config) (hc : c.marginAsides = cfg.marginAsides) =>
      nodesInto_seen c #[] body.toList (hc ▸ h)
    simp only [seen_empty, List.nil_append] at ih
    cases kind <;> simp [inlineNodeInto, seen_push, ink_elemFn, HtmlRead.lower, ih, Ir.plainTextOne]
  | .boxed b body =>
    simp only [inkPlainOne] at h
    have ih := fun (c : Config) (hc : c.marginAsides = cfg.marginAsides) =>
      nodesInto_seen c #[] body.toList (hc ▸ h)
    simp only [seen_empty, List.nil_append] at ih
    simp only [inlineNodeInto]
    repeat' split
    all_goals simp [seen_pair, seen_push, ink_elemFn, HtmlRead.lower, ih, Ir.plainTextOne]
  | .onSteps spec body =>
    simp only [inkPlainOne] at h
    have ih := fun (c : Config) (hc : c.marginAsides = cfg.marginAsides) =>
      nodesInto_seen c #[] body.toList (hc ▸ h)
    simp only [seen_empty, List.nil_append] at ih
    simp only [inlineNodeInto, overlayNode]
    split
    · cases hl : spec.last <;>
        simp [seen_push, seen_single, ink_elemFn, HtmlRead.lower, ih, Ir.plainTextOne, stepEndNodes]
    · simp [seen_push, ink_elemFn, HtmlRead.lower, ih, Ir.plainTextOne]
  | .link url body =>
    simp only [inkPlainOne] at h
    have ih := fun (c : Config) (hc : c.marginAsides = cfg.marginAsides) =>
      nodesInto_seen c #[] body.toList (hc ▸ h)
    simp only [seen_empty, List.nil_append] at ih
    simp only [inlineNodeInto]
    split
    · exact nodesInto_seen cfg acc body.toList h
    · simp [seen_push, ink_elemFn, HtmlRead.lower, ih, Ir.plainTextOne]
  | .role n body =>
    simp only [inkPlainOne] at h
    have ih := fun (c : Config) (hc : c.marginAsides = cfg.marginAsides) =>
      nodesInto_seen c #[] body.toList (hc ▸ h)
    simp only [seen_empty, List.nil_append] at ih
    simp only [inlineNodeInto]
    split
    · simp [seen_append, ih, Ir.plainTextOne]
    split
    · exact nodesInto_seen cfg acc body.toList h
    repeat' split
    all_goals simp [seen_push, ink_elemFn, ink_text, HtmlRead.lower, ih, Ir.plainTextOne]
  | .located _ body =>
    simp only [inkPlainOne] at h
    simp only [inlineNodeInto, Ir.plainTextOne]
    exact nodesInto_seen cfg acc body.toList h
  | .cited _ _ body =>
    simp only [inkPlainOne] at h
    simp only [inlineNodeInto, Ir.plainTextOne]
    exact nodesInto_seen cfg acc body.toList h
  | .ref key form text target =>
    simp only [inkPlainOne, Bool.not_eq_true'] at h
    simp only [inlineNodeInto, h, Bool.false_eq_true, ↓reduceIte]
    cases target with
    | none => simp [seen_push, ink_text, Ir.plainTextOne]
    | some a =>
      simp only
      split <;> simp [seen_push, seen_single, ink_elemFn, ink_text, HtmlRead.lower, Ir.plainTextOne]
  | .label key =>
    simp [inlineNodeInto, seen_push, ink_elemFn, HtmlRead.lower, Ir.plainTextOne, labelSpan]
  | .cite _ keys => simp [inlineNodeInto, seen_push, ink_text, Ir.plainTextOne]
  | .fill => simp [inlineNodeInto, seen_push, ink_elemFn, HtmlRead.lower, Ir.plainTextOne]
  | .rule _ _ _ => simp [inlineNodeInto, seen_push, ink_elemFn, HtmlRead.lower, Ir.plainTextOne]
  | .hspace e keep => rw [seen_hspace]; simp [Ir.plainTextOne]
  | .strut _ | .italicCorr _ | .pageNumber | .pageCount => simp [inlineNodeInto, Ir.plainTextOne]
  | .linebreak extra =>
    simp only [inlineNodeInto]
    split <;> simp [seen_push, ink_elemFn, HtmlRead.lower, Ir.plainTextOne]
  | .marginNote m body =>
    simp only [inkPlainOne, Bool.and_eq_true, Bool.not_eq_true'] at h
    have ih := fun (c : Config) (hc : c.marginAsides = cfg.marginAsides) =>
      nodesInto_seen c #[] body.toList (hc ▸ h.2)
    simp only [seen_empty, List.nil_append] at ih
    simp [inlineNodeInto, h.1, seen_push, ink_elemFn, HtmlRead.lower, ih, Ir.plainTextOne]
  | .image _ _ _ | .formula _ _ _ | .icon _ _ | .footnote _ _ | .altSteps _ _ _ =>
    simp [inkPlainOne] at h

end

/-- The emitted nodes of inline content hold its plain text (irText's characters,
`Ir.locatedText_erased`), white space aside, wherever `inkPlainList` holds of it. -/
public theorem inlines_projects (cfg : Config) (xs : Array Inline)
    (h : inkPlainList cfg.marginAsides xs.toList = true) :
    (Node.inkList (inlines cfg xs).toList).filter inked =
      (Ir.plainText xs).toList.filter inked := by
  have := nodesInto_seen cfg #[] xs.toList h
  simp only [seen_empty, List.nil_append] at this
  exact this

end LeanTex.Core.HtmlDoc
