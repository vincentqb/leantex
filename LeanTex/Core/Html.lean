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

/-- Escape one character of a JSON string embedded in a `<script>` data
block. RFC 8259 §7 lets any character be written as `\uXXXX`, so the three
that could break the embedding are: the quote (would end the JSON string),
the backslash (would start an escape), and `<` (could begin `</script>`,
the one sequence a script data block cannot contain — HTML §4.12.1.3's
restrictions for contents of script elements). The named C0 escapes RFC
8259 spells keep their two-character forms; the remaining C0 controls,
which RFC 8259 forbids raw and which have no meaning in metadata, are
dropped. Every branch is a concrete literal, which is what lets the two
safety theorems below close by `decide`. -/
def escapeCharJson (c : Char) : List Char :=
  if c == '"' then "\\u0022".toList
  else if c == '\\' then "\\u005c".toList
  else if c == '<' then "\\u003c".toList
  else if c == '\n' then "\\n".toList
  else if c == '\t' then "\\t".toList
  else if c == '\r' then "\\r".toList
  else if c.toNat < 0x20 then []
  else [c]

/-- Escape a JSON string value for embedding in a script data block. The
accumulator threads through the walk (the `#[x] ++ rest` trap). -/
def escapeJson (s : String) : String :=
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

/-- The JSON injection claim, in miniature: escaped content carries no raw
quote, so no value can end its own string and smuggle structure into the
object around it. -/
theorem escapeJson_no_quote (s : String) : '"' ∉ (escapeJson s).toList := by
  simp only [escapeJson, String.toList_ofList]
  exact (escapeJson_go_safe s.toList #[] (by simp)).1

/-- And no `<` at all: the escaped payload can never contain `</script`, so
the `rawPayload` guard below never fires on it and the data block reaches
the page intact rather than as `/* removed */`. -/
theorem escapeJson_no_lt (s : String) : '<' ∉ (escapeJson s).toList := by
  simp only [escapeJson, String.toList_ofList]
  exact (escapeJson_go_safe s.toList #[] (by simp)).2

inductive Node where
  | text (s : String)
  | elem (tag : String) (attrs : Array (String × String)) (kids : Array Node)
  /-- Stylesheet content. Not escaped — CSS has its own grammar — but the
  emitter refuses a payload containing its own end tag. -/
  | style (css : String)
  /-- Script content, same contract as `style`. The attrs carry a `type`:
  a script with a non-JavaScript MIME type is a data block (HTML §4.12.1),
  which is how JSON-LD rides without emitting behaviour. -/
  | script (attrs : Array (String × String)) (js : String)
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

/-- Does `term` occur in `l`? A structural scan so the refusal below can be a
theorem rather than an example; `String.splitOn` recurses on positions the
kernel cannot see through. -/
private def hasTerm (term : List Char) : List Char → Bool
  | [] => false
  | c :: rest => term.isPrefixOf (c :: rest) || hasTerm term rest

/-- A `style`/`script` payload that closes its own element would break out of
it; both printers refuse it through here, so neither can disagree. Browsers
match end tags ASCII-case-insensitively, so the payload is lowered before the
scan; the terminator literals are already lowercase and omit the final `>`,
which is what also catches `</script >` and `</script/`. -/
private def rawPayload (endTag payload : String) : String :=
  if hasTerm endTag.toList (payload.toList.map Char.toLower) then "/* removed */"
  else payload

/-- The guard's contract, the module's remaining injection claim: whatever
payload arrives, the emitted string never contains the terminator in any ASCII
case. Conditional on the replacement literal being clean, which `decide`
discharges below. -/
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

/-- Render a node onto `acc`. The accumulator threads through the whole walk:
building each subtree's string and concatenating (`render k ++ rest`) copies
the tail at every sibling, which is quadratic in the sibling count — the
`#[x] ++ rest` trap in its String form. -/
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

/-- Render without surrounding whitespace, for content inside a line. -/
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

-- The list companions make the recursion structural: a `map` over the
-- children hides the call behind a lambda the checker cannot see through.
private def renderListInto (acc : String) : List Node → Nat → String
  | [], _ => acc
  | k :: rest, indent => renderListInto (renderInto acc k indent) rest indent

private def inlineRenderListInto (acc : String) : List Node → String
  | [] => acc
  | k :: rest => inlineRenderListInto (inlineRenderInto acc k) rest

end

/-- Render a node. Indentation is cosmetic and suppressed where whitespace
matters. -/
def render (n : Node) (indent : Nat) : String :=
  renderInto "" n indent

/-- A complete document: doctype plus the root element. -/
def document (lang : String) (head body : Array Node) : String :=
  "<!DOCTYPE html>\n" ++
  inlineRenderTop (elem "html" #[elem "head" head, elem "body" body]
    #[("lang", lang)])
where
  inlineRenderTop (n : Node) : String := render n 0

end LeanTex.Core.Html
