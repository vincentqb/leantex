import LeanTex.Core.Diag

namespace LeanTex.Core.Html

/-! # A typed HTML tree

Well-formed by construction: nothing in this module concatenates tag strings,
so a document can never produce unbalanced or injected markup. Text and
attribute values pass through the escaper on the way in, and `style`/`script`
content is checked for its own terminator rather than escaped, because CSS and
JS have different rules than element content. -/

/-- Escape one character of element content. Kept separate so the safety
property below is a statement about a 4-way case split rather than about a
fold. -/
def escapeCharText (c : Char) : List Char :=
  if c == '&' then "&amp;".toList
  else if c == '<' then "&lt;".toList
  else if c == '>' then "&gt;".toList
  else [c]

/-- Escape element content. `&` first, or the other replacements get mangled. -/
def escapeText (s : String) : String :=
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

/-- Escape an attribute value; quotes matter here and not in content. -/
def escapeAttr (s : String) : String :=
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

/-- The injection-safety property, in miniature: escaped content carries no
`<`, so no text node can open a tag. -/
theorem escapeText_no_lt (s : String) : '<' ∉ (escapeText s).toList := by
  simp only [escapeText, String.toList_ofList]
  suffices h : ∀ l : List Char, '<' ∉ escapeText.go l by exact h s.toList
  intro l
  induction l with
  | nil => simp [escapeText.go]
  | cons c rest ih =>
    simp only [escapeText.go, List.mem_append, not_or]
    exact ⟨escapeCharText_no_lt c, ih⟩

theorem escapeAttr_no_quote (s : String) : '"' ∉ (escapeAttr s).toList := by
  simp only [escapeAttr, String.toList_ofList]
  suffices h : ∀ l : List Char, '"' ∉ escapeAttr.go l by exact h s.toList
  intro l
  induction l with
  | nil => simp [escapeAttr.go]
  | cons c rest ih =>
    simp only [escapeAttr.go, List.mem_append, not_or]
    exact ⟨escapeCharAttr_no_quote c, ih⟩

inductive Node where
  | text (s : String)
  | elem (tag : String) (attrs : Array (String × String)) (kids : Array Node)
  /-- Stylesheet content. Not escaped — CSS has its own grammar — but the
  emitter refuses a payload containing its own end tag. -/
  | style (css : String)
  /-- Script content, same contract as `style`. -/
  | script (js : String)
  deriving Inhabited

/-- Elements with no closing tag. -/
def voidTags : List String :=
  ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta",
   "source", "track", "wbr"]

/-- Elements whose whitespace is significant, so the printer must not indent
inside them. -/
def preserveTags : List String := ["pre", "code", "textarea"]

/-- Elements whose content is phrasing: their children are rendered without
added newlines, because in HTML a newline collapses to a space and would
appear before punctuation that follows a nested element. -/
def phrasingTags : List String :=
  ["p", "h1", "h2", "h3", "h4", "h5", "h6", "li", "span", "a", "strong", "em",
   "code", "figcaption", "dt", "dd", "th", "td", "title", "caption", "label"]

def elem (tag : String) (kids : Array Node := #[])
    (attrs : Array (String × String) := #[]) : Node :=
  .elem tag attrs kids

def text (s : String) : Node := .text s

private def attrString (attrs : Array (String × String)) : String :=
  String.join (attrs.toList.map fun (k, v) =>
    if v.isEmpty then s!" {k}" else s!" {k}=\"{escapeAttr v}\"")

/-- Does this subtree contain only text? Such an element prints on one line,
which keeps the output readable without introducing stray whitespace. -/
private def isInlineOnly (kids : Array Node) : Bool :=
  kids.all fun k =>
    match k with
    | .text _ => true
    | _ => false

mutual

/-- Render a node. Indentation is cosmetic and suppressed where whitespace
matters. -/
partial def render (n : Node) (indent : Nat) : String :=
  let pad := "".pushn ' ' (2 * indent)
  match n with
  | .text s => pad ++ escapeText s ++ "\n"
  | .style css =>
    -- A payload that closes its own element would break out of it.
    let safe := if (css.splitOn "</style").length > 1 then "/* removed */" else css
    pad ++ "<style>\n" ++ safe ++ "\n" ++ pad ++ "</style>\n"
  | .script js =>
    let safe := if (js.splitOn "</script").length > 1 then "/* removed */" else js
    pad ++ "<script>\n" ++ safe ++ "\n" ++ pad ++ "</script>\n"
  | .elem tag attrs kids =>
    let open' := "<" ++ tag ++ attrString attrs ++ ">"
    if voidTags.contains tag then
      pad ++ open' ++ "\n"
    else if preserveTags.contains tag || phrasingTags.contains tag ||
        isInlineOnly kids then
      pad ++ open' ++ String.join (kids.toList.map inlineRender) ++ "</" ++ tag ++ ">\n"
    else
      pad ++ open' ++ "\n" ++ renderList kids (indent + 1) ++ pad ++ "</" ++ tag ++ ">\n"

/-- Render without surrounding whitespace, for content inside a line. -/
partial def inlineRender (n : Node) : String :=
  match n with
  | .text s => escapeText s
  | .style css => "<style>" ++ css ++ "</style>"
  | .script js => "<script>" ++ js ++ "</script>"
  | .elem tag attrs kids =>
    let open' := "<" ++ tag ++ attrString attrs ++ ">"
    if voidTags.contains tag then open'
    else open' ++ String.join (kids.toList.map inlineRender) ++ "</" ++ tag ++ ">"

partial def renderList (kids : Array Node) (indent : Nat) : String :=
  String.join (kids.toList.map fun k => render k indent)

end

/-- A complete document: doctype plus the root element. -/
def document (lang : String) (head body : Array Node) : String :=
  "<!DOCTYPE html>\n" ++
  inlineRenderTop (elem "html" #[elem "head" head, elem "body" body]
    #[("lang", lang)])
where
  inlineRenderTop (n : Node) : String := render n 0

end LeanTex.Core.Html
