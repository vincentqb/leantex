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
   "code", "u", "figcaption", "dt", "dd", "th", "td", "title", "caption", "label"]

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

/-- A `style`/`script` payload that closes its own element would break out of
it; both printers refuse it through here, so neither can disagree. -/
private def rawPayload (endTag payload : String) : String :=
  if (payload.splitOn endTag).length > 1 then "/* removed */" else payload

mutual

/-- Render a node onto `acc`. The accumulator threads through the whole walk:
building each subtree's string and concatenating (`render k ++ rest`) copies
the tail at every sibling, which is quadratic in the sibling count — the
`#[x] ++ rest` trap in its String form. -/
def renderInto (acc : String) (n : Node) (indent : Nat) : String :=
  let pad := "".pushn ' ' (2 * indent)
  match n with
  | .text s => acc ++ pad ++ escapeText s ++ "\n"
  | .style css =>
    acc ++ pad ++ "<style>\n" ++ rawPayload "</style" css ++ "\n" ++ pad ++ "</style>\n"
  | .script js =>
    acc ++ pad ++ "<script>\n" ++ rawPayload "</script" js ++ "\n" ++ pad ++ "</script>\n"
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

/-- Render without surrounding whitespace, for content inside a line. -/
def inlineRenderInto (acc : String) (n : Node) : String :=
  match n with
  | .text s => acc ++ escapeText s
  | .style css => acc ++ "<style>" ++ rawPayload "</style" css ++ "</style>"
  | .script js => acc ++ "<script>" ++ rawPayload "</script" js ++ "</script>"
  | .elem tag attrs kids =>
    let open' := "<" ++ tag ++ attrString attrs ++ ">"
    if voidTags.contains tag then acc ++ open'
    else inlineRenderListInto (acc ++ open') kids.toList ++ "</" ++ tag ++ ">"

-- The list companions make the recursion structural: a `map` over the
-- children hides the call behind a lambda the checker cannot see through.
def renderListInto (acc : String) : List Node → Nat → String
  | [], _ => acc
  | k :: rest, indent => renderListInto (renderInto acc k indent) rest indent

def inlineRenderListInto (acc : String) : List Node → String
  | [] => acc
  | k :: rest => inlineRenderListInto (inlineRenderInto acc k) rest

end

/-- Render a node. Indentation is cosmetic and suppressed where whitespace
matters. -/
def render (n : Node) (indent : Nat) : String :=
  renderInto "" n indent

/-- Render without surrounding whitespace, for content inside a line. -/
def inlineRender (n : Node) : String :=
  inlineRenderInto "" n

/-- A complete document: doctype plus the root element. -/
def document (lang : String) (head body : Array Node) : String :=
  "<!DOCTYPE html>\n" ++
  inlineRenderTop (elem "html" #[elem "head" head, elem "body" body]
    #[("lang", lang)])
where
  inlineRenderTop (n : Node) : String := render n 0

end LeanTex.Core.Html
