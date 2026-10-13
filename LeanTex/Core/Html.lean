module

namespace LeanTex.Core.Html

/-! Typed HTML tree and its renderer: text and attribute values are escaped, and a
`style` or `script` payload cannot close its own element. -/

def escapeCharText (c : Char) : List Char :=
  if c == '&' then "&amp;".toList
  else if c == '<' then "&lt;".toList
  else if c == '>' then "&gt;".toList
  else [c]

public def escapeText (s : String) : String :=
  String.ofList (go s.toList)
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

public def escapeAttr (s : String) : String :=
  String.ofList (go s.toList)
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

public theorem escapeText_no_lt (s : String) : '<' ∉ (escapeText s).toList := by
  simp only [escapeText, String.toList_ofList]
  suffices h : ∀ l : List Char, '<' ∉ escapeText.go l by exact h s.toList
  intro l
  induction l with
  | nil => simp [escapeText.go]
  | cons c rest ih =>
    simp only [escapeText.go, List.mem_append, not_or]
    exact ⟨escapeCharText_no_lt c, ih⟩

public theorem escapeAttr_no_quote (s : String) : '"' ∉ (escapeAttr s).toList := by
  simp only [escapeAttr, String.toList_ofList]
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

private def attrString (attrs : Array (String × String)) : String :=
  String.join (attrs.toList.map fun (k, v) =>
    if v.isEmpty then s!" {k}" else s!" {k}=\"{escapeAttr v}\"")

private def isInlineOnly (kids : Array Node) : Bool :=
  kids.all fun k =>
    match k with
    | .text _ => true
    | _ => false

private def hasTerm (term : List Char) : List Char → Bool
  | [] => false
  | c :: rest => term.isPrefixOf (c :: rest) || hasTerm term rest

/-- The payload, or `/* removed */` when it contains `endTag` in any ASCII case. -/
private def rawPayload (endTag payload : String) : String :=
  if hasTerm endTag.toList (payload.toList.map Char.toLower) then "/* removed */"
  else payload

private theorem rawPayload_no_terminator (endTag payload : String)
    (h : hasTerm endTag.toList ("/* removed */".toList.map Char.toLower) = false) :
    hasTerm endTag.toList ((rawPayload endTag payload).toList.map Char.toLower) = false := by
  unfold rawPayload
  split
  · exact h
  · next hc => exact Bool.not_eq_true _ ▸ hc

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
    acc ++ pad ++ "<script" ++ attrString attrs ++ ">\n" ++
      rawPayload "</script" js ++ "\n" ++ pad ++ "</script>\n"
  | .elem tag attrs kids =>
    let open' := "<" ++ tag ++ attrString attrs ++ ">"
    if voidTags.contains tag then
      acc ++ pad ++ open' ++ "\n"
    else if preserveTags.contains tag || phrasingTags.contains tag ||
        isInlineOnly kids then
      inlineRenderListInto (acc ++ pad ++ open') kids.toList ++ "</" ++ tag ++ ">\n"
    else
      renderListInto (acc ++ pad ++ open' ++ "\n") kids.toList (indent + 1)
        ++ pad ++ "</" ++ tag ++ ">\n"

private def inlineRenderInto (acc : String) (n : Node) : String :=
  match n with
  | .text s => acc ++ escapeText s
  | .style css => acc ++ "<style>" ++ rawPayload "</style" css ++ "</style>"
  | .script attrs js =>
    acc ++ "<script" ++ attrString attrs ++ ">" ++ rawPayload "</script" js ++ "</script>"
  | .elem tag attrs kids =>
    let open' := "<" ++ tag ++ attrString attrs ++ ">"
    if voidTags.contains tag then acc ++ open'
    else inlineRenderListInto (acc ++ open') kids.toList ++ "</" ++ tag ++ ">"

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
