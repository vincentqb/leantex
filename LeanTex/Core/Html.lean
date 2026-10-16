module

namespace LeanTex.Core.Html

/-! Typed HTML tree and its renderer: text and attribute values are escaped, and a
`style` or `script` payload cannot close its own element. -/

def escapeCharText (c : Char) : List Char :=
  if c == '&' then "&amp;".toList
  else if c == '<' then "&lt;".toList
  else if c == '>' then "&gt;".toList
  else [c]

def needsText (c : Char) : Bool := c == '&' || c == '<' || c == '>'

def escapeStepText (acc : String) (c : Char) : String :=
  if c == '&' then acc ++ "&amp;"
  else if c == '<' then acc ++ "&lt;"
  else if c == '>' then acc ++ "&gt;"
  else acc.push c

/-- The text with `&`, `<` and `>` replaced by their references; a text holding none is returned
as it stands. -/
public def escapeText (s : String) : String :=
  if s.contains needsText then s.foldl escapeStepText "" else s
where
  go : List Char → List Char
    | [] => []
    | c :: rest => escapeCharText c ++ go rest

def escapeCharAttr (c : Char) : List Char :=
  if c == '&' then "&amp;".toList
  else if c == '<' then "&lt;".toList
  else if c == '>' then "&gt;".toList
  else if c == '"' then "&quot;".toList
  else if c == '\'' then "&#39;".toList
  else [c]

def needsAttr (c : Char) : Bool := c == '&' || c == '<' || c == '>' || c == '"' || c == '\''

def escapeStepAttr (acc : String) (c : Char) : String :=
  if c == '&' then acc ++ "&amp;"
  else if c == '<' then acc ++ "&lt;"
  else if c == '>' then acc ++ "&gt;"
  else if c == '"' then acc ++ "&quot;"
  else if c == '\'' then acc ++ "&#39;"
  else acc.push c

/-- The attribute value with `&`, `<`, `>` and both quotes replaced by their references; a value
holding none is returned as it stands. -/
public def escapeAttr (s : String) : String :=
  if s.contains needsAttr then s.foldl escapeStepAttr "" else s
where
  go : List Char → List Char
    | [] => []
    | c :: rest => escapeCharAttr c ++ go rest

theorem escapeCharText_no_lt (c : Char) : '<' ∉ escapeCharText c := by
  unfold escapeCharText
  split
  · decide
  · split
    · decide
    · split
      · decide
      · simp only [List.mem_singleton]
        intro hc
        exact absurd hc.symm (by simp_all)

theorem escapeCharAttr_no_quote (c : Char) : '"' ∉ escapeCharAttr c := by
  unfold escapeCharAttr
  split
  · decide
  · split
    · decide
    · split
      · decide
      · split
        · decide
        · split
          · decide
          · simp only [List.mem_singleton]
            intro hc
            exact absurd hc.symm (by simp_all)

theorem escapeStepText_go (l : List Char) (acc : String) :
    (l.foldl escapeStepText acc).toList = acc.toList ++ escapeText.go l := by
  induction l generalizing acc with
  | nil => simp [escapeText.go]
  | cons c rest ih =>
    simp only [List.foldl_cons, escapeText.go, ih, ← List.append_assoc]
    congr 1
    unfold escapeStepText escapeCharText
    split
    · simp_all [String.toList_append]
    · split
      · simp_all [String.toList_append]
      · split
        · simp_all [String.toList_append]
        · simp [String.toList_push]

theorem escapeText_go_plain (l : List Char) (h : l.any needsText = false) :
    escapeText.go l = l := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    have hc : escapeCharText c = [c] := by
      have := h.1
      unfold needsText at this
      unfold escapeCharText
      simp_all
    simp only [escapeText.go, hc, ih h.2, List.singleton_append]

/-- The escaper is its character-by-character specification. -/
theorem escapeText_spec (s : String) :
    escapeText s = String.ofList (escapeText.go s.toList) := by
  apply String.ext
  rw [String.toList_ofList]
  unfold escapeText
  split
  · rw [String.foldl_eq_foldl_toList, escapeStepText_go]
    rfl
  · next h =>
    rw [escapeText_go_plain _ (by simpa [String.contains_bool_eq] using h)]

theorem escapeStepAttr_go (l : List Char) (acc : String) :
    (l.foldl escapeStepAttr acc).toList = acc.toList ++ escapeAttr.go l := by
  induction l generalizing acc with
  | nil => simp [escapeAttr.go]
  | cons c rest ih =>
    simp only [List.foldl_cons, escapeAttr.go, ih, ← List.append_assoc]
    congr 1
    unfold escapeStepAttr escapeCharAttr
    split
    · simp_all [String.toList_append]
    · split
      · simp_all [String.toList_append]
      · split
        · simp_all [String.toList_append]
        · split
          · simp_all [String.toList_append]
          · split
            · simp_all [String.toList_append]
            · simp [String.toList_push]

theorem escapeAttr_go_plain (l : List Char) (h : l.any needsAttr = false) :
    escapeAttr.go l = l := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    have hc : escapeCharAttr c = [c] := by
      have := h.1
      unfold needsAttr at this
      unfold escapeCharAttr
      simp_all
    simp only [escapeAttr.go, hc, ih h.2, List.singleton_append]

/-- The escaper is its character-by-character specification. -/
theorem escapeAttr_spec (s : String) :
    escapeAttr s = String.ofList (escapeAttr.go s.toList) := by
  apply String.ext
  rw [String.toList_ofList]
  unfold escapeAttr
  split
  · rw [String.foldl_eq_foldl_toList, escapeStepAttr_go]
    rfl
  · next h =>
    rw [escapeAttr_go_plain _ (by simpa [String.contains_bool_eq] using h)]

public theorem escapeText_no_lt (s : String) : '<' ∉ (escapeText s).toList := by
  simp only [escapeText_spec, String.toList_ofList]
  suffices h : ∀ l : List Char, '<' ∉ escapeText.go l by exact h s.toList
  intro l
  induction l with
  | nil => simp [escapeText.go]
  | cons c rest ih =>
    simp only [escapeText.go, List.mem_append, not_or]
    exact ⟨escapeCharText_no_lt c, ih⟩

public theorem escapeAttr_no_quote (s : String) : '"' ∉ (escapeAttr s).toList := by
  simp only [escapeAttr_spec, String.toList_ofList]
  suffices h : ∀ l : List Char, '"' ∉ escapeAttr.go l by exact h s.toList
  intro l
  induction l with
  | nil => simp [escapeAttr.go]
  | cons c rest ih =>
    simp only [escapeAttr.go, List.mem_append, not_or]
    exact ⟨escapeCharAttr_no_quote c, ih⟩

def escapeCharJson (c : Char) : List Char :=
  if c == '"' then "\\u0022".toList
  else if c == '\\' then "\\u005c".toList
  else if c == '<' then "\\u003c".toList
  else if c == '\n' then "\\n".toList
  else if c == '\t' then "\\t".toList
  else if c == '\r' then "\\r".toList
  else if c.toNat < 0x20 then []
  else [c]

/-- Escape a JSON string value for a script data block (RFC 8259 §7): quote, backslash and `<`
become `\uXXXX`, newline, tab and return keep their short escapes, and other C0 controls are
dropped. -/
public def escapeJson (s : String) : String :=
  String.ofList (go #[] s.toList).toList
where
  go (acc : Array Char) : List Char → Array Char
    | [] => acc
    | c :: rest => go (acc ++ (escapeCharJson c).toArray) rest

private theorem escapeCharJson_safe (c : Char) :
    '"' ∉ escapeCharJson c ∧ '<' ∉ escapeCharJson c := by
  unfold escapeCharJson
  split
  · decide
  · split
    · decide
    · split
      · decide
      · split
        · decide
        · split
          · decide
          · split
            · decide
            · split
              · decide
              · next h1 _ h3 _ _ _ _ =>
                simp only [List.mem_singleton]
                constructor
                · intro hc
                  exact absurd hc.symm (by simp_all)
                · intro hc
                  exact absurd hc.symm (by simp_all)

private theorem escapeJson_go_safe (l : List Char) (acc : Array Char)
    (hacc : '"' ∉ acc.toList ∧ '<' ∉ acc.toList) :
    '"' ∉ (escapeJson.go acc l).toList ∧ '<' ∉ (escapeJson.go acc l).toList := by
  induction l generalizing acc with
  | nil => simpa [escapeJson.go] using hacc
  | cons c rest ih =>
    simp only [escapeJson.go]
    apply ih
    have hc := escapeCharJson_safe c
    simp only [Array.toList_append, List.mem_append, not_or]
    exact ⟨⟨hacc.1, hc.1⟩, ⟨hacc.2, hc.2⟩⟩

public theorem escapeJson_no_quote (s : String) : '"' ∉ (escapeJson s).toList := by
  simp only [escapeJson, String.toList_ofList]
  exact (escapeJson_go_safe s.toList #[] (by simp)).1

public theorem escapeJson_no_lt (s : String) : '<' ∉ (escapeJson s).toList := by
  simp only [escapeJson, String.toList_ofList]
  exact (escapeJson_go_safe s.toList #[] (by simp)).2

public inductive Node where
  | text (s : String)
  | elem (tag : String) (attrs : Array (String × String)) (kids : Array Node)
  /-- Stylesheet content, unescaped; the renderer replaces a payload containing its end tag. -/
  | style (css : String)
  /-- Script content under the `style` contract; a non-JavaScript `type` makes it a data block. -/
  | script (attrs : Array (String × String)) (js : String)
  deriving Inhabited

public def voidTags : List String :=
  ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta",
   "source", "track", "wbr"]

/-- Elements whose whitespace is significant, printed without indentation inside. -/
public def preserveTags : List String := ["pre", "code", "textarea"]

/-- Elements whose children print without added newlines, which would render as spaces. -/
def phrasingTags : List String :=
  ["p", "h1", "h2", "h3", "h4", "h5", "h6", "li", "span", "a", "strong", "em",
   "code", "u", "s", "figcaption", "dt", "dd", "th", "td", "title", "caption", "label",
   "text", "tspan"]

@[expose] public def elem (tag : String) (kids : Array Node := #[])
    (attrs : Array (String × String) := #[]) : Node :=
  .elem tag attrs kids

@[expose] public def text (s : String) : Node := .text s

@[expose] public def Node.tag? : Node → Option String
  | .elem tag _ _ => some tag
  | .text _ => none
  | .style _ => none
  | .script _ _ => none

/-- A walk over a tree in document order: what a text, style or script node adds, the context an
element and its children are read under (`none` leaves the element unread), and what an element it
reads adds, under that context, before its children and, under its parent's, after them. -/
public structure Walk (σ α : Type) where
  text : σ → α → String → α := fun _ acc _ => acc
  style : σ → α → String → α := fun _ acc _ => acc
  script : σ → α → Array (String × String) → String → α := fun _ acc _ _ => acc
  inner : σ → String → Array (String × String) → Option σ := fun ctx _ _ => some ctx
  enter : σ → α → String → Array (String × String) → Array Node → α := fun _ acc _ _ _ => acc
  leave : σ → α → α := fun _ acc => acc

/-- A rewrite of a tree: each element's attributes, what each text node becomes, and each style
sheet. -/
public structure Rewrite where
  attrs : String → Array (String × String) → Array (String × String) := fun _ attrs => attrs
  text : String → Array Node := fun s => #[.text s]
  style : String → String := fun css => css

mutual

public def Walk.node {σ α : Type} (w : Walk σ α) (ctx : σ) (acc : α) : Node → α
  | .text s => w.text ctx acc s
  | .style css => w.style ctx acc css
  | .script attrs js => w.script ctx acc attrs js
  | .elem tag attrs kids =>
    match w.inner ctx tag attrs with
    | some c => w.leave ctx (w.list c (w.enter c acc tag attrs kids) kids.toList)
    | none => acc

public def Walk.list {σ α : Type} (w : Walk σ α) (ctx : σ) (acc : α) : List Node → α
  | [] => acc
  | n :: rest => w.list ctx (w.node ctx acc n) rest

end

mutual

public def Rewrite.node (r : Rewrite) (acc : Array Node) : Node → Array Node
  | .text s => acc.append (r.text s)
  | .style css => acc.push (.style (r.style css))
  | .script attrs js => acc.push (.script attrs js)
  | .elem tag attrs kids => acc.push (.elem tag (r.attrs tag attrs) (r.list #[] kids.toList))

public def Rewrite.list (r : Rewrite) (acc : Array Node) : List Node → Array Node
  | [] => acc
  | n :: rest => r.list (r.node acc n) rest

end

public theorem Walk.list_nil_exact {σ α : Type} (w : Walk σ α) (ctx : σ) (acc : α) :
    w.list ctx acc [] = acc := by
  simp only [Walk.list]

public theorem Walk.list_cons_exact {σ α : Type} (w : Walk σ α) (ctx : σ) (acc : α) (n : Node)
    (rest : List Node) : w.list ctx acc (n :: rest) = w.list ctx (w.node ctx acc n) rest := by
  simp only [Walk.list]

public theorem Walk.node_text_exact {σ α : Type} (w : Walk σ α) (ctx : σ) (acc : α) (s : String) :
    w.node ctx acc (.text s) = w.text ctx acc s := by
  simp only [Walk.node]

public theorem Walk.node_style_exact {σ α : Type} (w : Walk σ α) (ctx : σ) (acc : α)
    (css : String) : w.node ctx acc (.style css) = w.style ctx acc css := by
  simp only [Walk.node]

public theorem Walk.node_script_exact {σ α : Type} (w : Walk σ α) (ctx : σ) (acc : α)
    (attrs : Array (String × String)) (js : String) :
    w.node ctx acc (.script attrs js) = w.script ctx acc attrs js := by
  simp only [Walk.node]

public theorem Walk.node_elem_exact {σ α : Type} (w : Walk σ α) (ctx : σ) (acc : α)
    (tag : String) (attrs : Array (String × String)) (kids : Array Node) :
    w.node ctx acc (.elem tag attrs kids) =
      match w.inner ctx tag attrs with
      | some c => w.leave ctx (w.list c (w.enter c acc tag attrs kids) kids.toList)
      | none => acc := by
  simp only [Walk.node]
  cases w.inner ctx tag attrs <;> rfl

public theorem Rewrite.list_nil_exact (r : Rewrite) (acc : Array Node) : r.list acc [] = acc := by
  simp only [Rewrite.list]

public theorem Rewrite.list_cons_exact (r : Rewrite) (acc : Array Node) (n : Node)
    (rest : List Node) : r.list acc (n :: rest) = r.list (r.node acc n) rest := by
  simp only [Rewrite.list]

public theorem Rewrite.node_text_exact (r : Rewrite) (acc : Array Node) (s : String) :
    r.node acc (.text s) = acc.append (r.text s) := by
  simp only [Rewrite.node]

public theorem Rewrite.node_style_exact (r : Rewrite) (acc : Array Node) (css : String) :
    r.node acc (.style css) = acc.push (.style (r.style css)) := by
  simp only [Rewrite.node]

public theorem Rewrite.node_script_exact (r : Rewrite) (acc : Array Node)
    (attrs : Array (String × String)) (js : String) :
    r.node acc (.script attrs js) = acc.push (.script attrs js) := by
  simp only [Rewrite.node]

public theorem Rewrite.node_elem_exact (r : Rewrite) (acc : Array Node) (tag : String)
    (attrs : Array (String × String)) (kids : Array Node) :
    r.node acc (.elem tag attrs kids) =
      acc.push (.elem tag (r.attrs tag attrs) (r.list #[] kids.toList)) := by
  simp only [Rewrite.node]

/-- The accumulator with each attribute appended, its value escaped. -/
private def attrsInto (acc : String) (attrs : Array (String × String)) : String :=
  attrs.foldl (init := acc) fun acc (k, v) =>
    if v.isEmpty then acc ++ " " ++ k else acc ++ " " ++ k ++ "=\"" ++ escapeAttr v ++ "\""

private def isInlineOnly (kids : Array Node) : Bool :=
  kids.all fun k =>
    match k with
    | .text _ => true
    | _ => false

private def hasTerm (term : List Char) : List Char → Bool
  | [] => false
  | c :: rest => term.isPrefixOf (c :: rest) || hasTerm term rest

/-- Whether some character of `payload`, lowered, is the first of `endTag`, without which
`endTag` cannot occur. -/
private def mayHold (endTag payload : String) : Bool :=
  match endTag.toList with
  | [] => true
  | c :: _ => payload.contains fun x => x.toLower == c

private theorem hasTerm_absent (c : Char) (rest l : List Char) (h : c ∉ l) :
    hasTerm (c :: rest) l = false := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    have hd : c ≠ d := fun e => h (e ▸ List.mem_cons_self ..)
    simp only [hasTerm, List.isPrefixOf, Bool.or_eq_false_iff]
    exact ⟨by simp [hd], ih (fun m => h (List.mem_cons_of_mem _ m))⟩

private theorem hasTerm_of_mayHold (endTag payload : String) (h : mayHold endTag payload = false) :
    hasTerm endTag.toList (payload.toList.map Char.toLower) = false := by
  unfold mayHold at h
  split at h
  · contradiction
  · next c rest he =>
    rw [he]
    apply hasTerm_absent
    simp only [String.contains_bool_eq, List.any_eq_false, beq_iff_eq] at h
    simp only [List.mem_map, not_exists, not_and]
    exact fun x hx e => h x hx e

/-- The payload, or `/* removed */` when it contains `endTag` in any ASCII case. -/
private def rawPayload (endTag payload : String) : String :=
  if mayHold endTag payload && hasTerm endTag.toList (payload.toList.map Char.toLower) then
    "/* removed */"
  else payload

private theorem rawPayload_no_terminator (endTag payload : String)
    (h : hasTerm endTag.toList ("/* removed */".toList.map Char.toLower) = false) :
    hasTerm endTag.toList ((rawPayload endTag payload).toList.map Char.toLower) = false := by
  unfold rawPayload
  split
  · exact h
  · next hc =>
    cases hm : mayHold endTag payload
    · exact hasTerm_of_mayHold endTag payload hm
    · simpa [hm] using hc

private theorem rawPayload_style_no_terminator (payload : String) :
    hasTerm "</style".toList
      ((rawPayload "</style" payload).toList.map Char.toLower) = false :=
  rawPayload_no_terminator _ _ (by decide)

private theorem rawPayload_script_no_terminator (payload : String) :
    hasTerm "</script".toList
      ((rawPayload "</script" payload).toList.map Char.toLower) = false :=
  rawPayload_no_terminator _ _ (by decide)

mutual

private def renderInto (acc : String) (n : Node) (indent : Nat) : String :=
  let pad := "".pushn ' ' (2 * indent)
  match n with
  | .text s => acc ++ pad ++ escapeText s ++ "\n"
  | .style css =>
    acc ++ pad ++ "<style>\n" ++ rawPayload "</style" css ++ "\n" ++ pad ++ "</style>\n"
  | .script attrs js =>
    attrsInto (acc ++ pad ++ "<script") attrs ++ ">\n" ++
      rawPayload "</script" js ++ "\n" ++ pad ++ "</script>\n"
  | .elem tag attrs kids =>
    let opened := attrsInto (acc ++ pad ++ "<" ++ tag) attrs ++ ">"
    if voidTags.contains tag then
      opened ++ "\n"
    else if preserveTags.contains tag || phrasingTags.contains tag ||
        isInlineOnly kids then
      inlineRenderListInto opened kids.toList ++ "</" ++ tag ++ ">\n"
    else
      renderListInto (opened ++ "\n") kids.toList (indent + 1)
        ++ pad ++ "</" ++ tag ++ ">\n"

private def inlineRenderInto (acc : String) (n : Node) : String :=
  match n with
  | .text s => acc ++ escapeText s
  | .style css => acc ++ "<style>" ++ rawPayload "</style" css ++ "</style>"
  | .script attrs js =>
    attrsInto (acc ++ "<script") attrs ++ ">" ++ rawPayload "</script" js ++ "</script>"
  | .elem tag attrs kids =>
    let opened := attrsInto (acc ++ "<" ++ tag) attrs ++ ">"
    if voidTags.contains tag then opened
    else inlineRenderListInto opened kids.toList ++ "</" ++ tag ++ ">"

private def renderListInto (acc : String) : List Node → Nat → String
  | [], _ => acc
  | k :: rest, indent => renderListInto (renderInto acc k indent) rest indent

private def inlineRenderListInto (acc : String) : List Node → String
  | [] => acc
  | k :: rest => inlineRenderListInto (inlineRenderInto acc k) rest

end

public def render (n : Node) (indent : Nat) : String :=
  renderInto "" n indent

public def document (lang : String) (head body : Array Node) : String :=
  "<!DOCTYPE html>\n" ++
  inlineRenderTop (elem "html" #[elem "head" head, elem "body" body]
    #[("lang", lang)])
where
  inlineRenderTop (n : Node) : String := render n 0

public theorem document_declares_lang (lang : String) (head body : Array Node) :
    document lang head body =
      "<!DOCTYPE html>\n" ++
        render (elem "html" #[elem "head" head, elem "body" body]
          #[("lang", lang)]) 0 := by
  rfl

end LeanTex.Core.Html
