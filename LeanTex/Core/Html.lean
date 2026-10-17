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

private theorem hasTerm_iff (term l : List Char) (hne : term ≠ []) :
    hasTerm term l = true ↔ term <:+: l := by
  induction l with
  | nil => simp [hasTerm, List.infix_nil, hne]
  | cons c rest ih => simp [hasTerm, List.infix_cons_iff, List.isPrefixOf_iff_prefix, ih]

/-- A byte lowered as `Char.toLower` lowers the ASCII character it encodes. -/
def lowerByte (b : UInt8) : UInt8 := if (65 : UInt8) ≤ b && b ≤ 90 then b + 32 else b

/-- Whether `term` occurs in a byte list. -/
def hasTermBytes (term : List UInt8) : List UInt8 → Bool
  | [] => false
  | b :: rest => term.isPrefixOf (b :: rest) || hasTermBytes term rest

/-- A character's low byte, its UTF-8 encoding when it is ASCII. -/
def byteOf (c : Char) : UInt8 := c.val.toUInt8

theorem lowerByte_high (b : UInt8) (hb : 128 ≤ b.toNat) : lowerByte b = b := by
  unfold lowerByte
  have : ((65 : UInt8) ≤ b && b ≤ 90) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, UInt8.not_le]
    right
    rw [UInt8.lt_iff_toNat_lt]
    simp
    omega
  rw [this]
  rfl

theorem lowerByte_ascii_table : ∀ n : Fin 128,
    lowerByte (byteOf (Char.ofNat n)) = byteOf (Char.ofNat n).toLower := by
  decide +kernel

theorem lowerByte_ascii (c : Char) (hc : c.toNat < 128) :
    lowerByte (byteOf c) = byteOf c.toLower := by
  have := lowerByte_ascii_table ⟨c.toNat, hc⟩
  simpa [Char.ofNat_toNat] using this

theorem toLower_ascii_table : ∀ n : Fin 128, (Char.ofNat n).toLower.toNat < 128 := by
  decide +kernel

theorem toLower_ascii (c : Char) (hc : c.toNat < 128) : c.toLower.toNat < 128 := by
  have := toLower_ascii_table ⟨c.toNat, hc⟩
  simpa [Char.ofNat_toNat] using this

theorem toLower_high (c : Char) (hc : 128 ≤ c.toNat) : c.toLower = c := by
  unfold Char.toLower
  split
  · next h =>
    exfalso
    have hz : c.val ≤ 'Z'.val := h.2
    rw [UInt32.le_iff_toNat_le] at hz
    have : c.val.toNat = c.toNat := Char.toNat_val
    have hZ : ('Z'.val).toNat = 90 := by decide
    omega
  · rfl

theorem or_high (x k : UInt8) (hk : 128 ≤ k.toNat) : 128 ≤ (x ||| k).toNat := by
  rw [UInt8.toNat_or]
  exact Nat.le_trans hk Nat.right_le_or

theorem utf8Size_one_iff (c : Char) : c.utf8Size = 1 ↔ c.toNat < 128 := by
  rw [Char.utf8Size_eq_one_iff, UInt32.le_iff_toNat_le]
  have : c.val.toNat = c.toNat := Char.toNat_val
  have h127 : (127 : UInt32).toNat = 127 := rfl
  omega

/-- Every byte encoding a character outside ASCII is at least 128. -/
theorem utf8EncodeChar_high (c : Char) (hc : 128 ≤ c.toNat) :
    ∀ b ∈ String.utf8EncodeChar c, 128 ≤ b.toNat := by
  have h1 : c.utf8Size ≠ 1 := fun h => by have := (utf8Size_one_iff c).mp h; omega
  have hle := Char.utf8Size_le_four c
  have hpos := Char.utf8Size_pos c
  intro b hb
  rcases (by omega : c.utf8Size = 2 ∨ c.utf8Size = 3 ∨ c.utf8Size = 4) with h | h | h
  · rw [String.utf8EncodeChar_eq_cons_cons h] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> exact or_high _ _ (by decide)
  · rw [String.utf8EncodeChar_eq_cons_cons_cons h] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> exact or_high _ _ (by decide)
  · rw [String.utf8EncodeChar_eq_cons_cons_cons_cons h] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> exact or_high _ _ (by decide)

theorem byteOf_toNat (c : Char) (hc : c.toNat < 128) : (byteOf c).toNat = c.toNat := by
  show c.val.toUInt8.toNat = c.toNat
  rw [UInt32.toNat_toUInt8]
  have : c.val.toNat = c.toNat := Char.toNat_val
  omega

theorem byteOf_beq (c d : Char) (hc : c.toNat < 128) (hd : d.toNat < 128) :
    (byteOf c == byteOf d) = (c == d) := by
  by_cases h : c = d
  · subst h; rw [beq_self_eq_true, beq_self_eq_true]
  · have hne : byteOf c ≠ byteOf d := fun e => h (Char.toNat_inj.mp (by
      rw [← byteOf_toNat c hc, ← byteOf_toNat d hd, e]))
    rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h]

def AsciiTerm (term : List Char) : Prop := ∀ c ∈ term, c.toNat < 128

instance (term : List Char) : Decidable (AsciiTerm term) :=
  inferInstanceAs (Decidable (∀ c ∈ term, c.toNat < 128))

theorem prefix_bytes (term : List Char) (hterm : AsciiTerm term) (cs : List Char) :
    (term.map byteOf).isPrefixOf ((cs.flatMap String.utf8EncodeChar).map lowerByte) =
      term.isPrefixOf (cs.map Char.toLower) := by
  induction term generalizing cs with
  | nil => simp [List.isPrefixOf]
  | cons t ts ih =>
    have ht : t.toNat < 128 := hterm t (List.mem_cons_self ..)
    have hts : AsciiTerm ts := fun c hc => hterm c (List.mem_cons_of_mem _ hc)
    cases cs with
    | nil => rfl
    | cons c cs =>
      by_cases hc : c.toNat < 128
      · have h1 : c.utf8Size = 1 := (utf8Size_one_iff c).mpr hc
        rw [List.flatMap_cons, String.utf8EncodeChar_eq_singleton h1]
        simp only [List.cons_append, List.nil_append, List.map_cons, List.isPrefixOf]
        have hb : lowerByte c.val.toUInt8 = byteOf c.toLower := lowerByte_ascii c hc
        rw [hb, byteOf_beq t c.toLower ht (toLower_ascii c hc), ih hts cs]
      · have hc' : 128 ≤ c.toNat := by omega
        have hne : String.utf8EncodeChar c ≠ [] := by
          intro h
          have hl := String.length_utf8EncodeChar c
          rw [h, List.length_nil] at hl
          have := Char.utf8Size_pos c
          omega
        obtain ⟨b, bs, hbs⟩ : ∃ b bs, String.utf8EncodeChar c = b :: bs := by
          cases h : String.utf8EncodeChar c with
          | nil => exact absurd h hne
          | cons b bs => exact ⟨b, bs, rfl⟩
        have hb : 128 ≤ b.toNat :=
          utf8EncodeChar_high c hc' b (by rw [hbs]; exact List.mem_cons_self ..)
        rw [List.flatMap_cons, hbs]
        simp only [List.cons_append, List.map_cons, List.isPrefixOf]
        rw [toLower_high c hc']
        have hl : lowerByte b = b := lowerByte_high b hb
        have h1 : (byteOf t == lowerByte b) = false := by
          rw [hl]; apply beq_eq_false_iff_ne.mpr; intro e
          have := byteOf_toNat t ht; rw [e] at this; omega
        have h2 : (t == c) = false := by
          apply beq_eq_false_iff_ne.mpr; intro e; subst e; omega
        simp only [h1, h2, Bool.false_and]

theorem hasTermBytes_skip (tb : List UInt8) (t : UInt8) (ht : t.toNat < 128)
    (hts : tb.head? = some t) (hs : List UInt8) (hhigh : ∀ b ∈ hs, 128 ≤ b.toNat)
    (rest : List UInt8) :
    hasTermBytes tb (hs.map lowerByte ++ rest) = hasTermBytes tb rest := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    have hh : 128 ≤ h.toNat := hhigh h (List.mem_cons_self ..)
    have ih' := ih (fun b hb => hhigh b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, List.cons_append, hasTermBytes]
    rw [ih']
    cases tb with
    | nil => simp at hts
    | cons a as =>
      simp at hts; subst hts
      have hl : lowerByte h = h := lowerByte_high h hh
      have : (a == lowerByte h) = false := by
        rw [hl]; apply beq_eq_false_iff_ne.mpr; intro e; rw [e] at ht; omega
      simp only [List.isPrefixOf, this, Bool.false_and, Bool.false_or]

theorem hasTerm_bytes (term : List Char) (hterm : AsciiTerm term) (hne : term ≠ [])
    (cs : List Char) :
    hasTermBytes (term.map byteOf) ((cs.flatMap String.utf8EncodeChar).map lowerByte) =
      hasTerm term (cs.map Char.toLower) := by
  obtain ⟨t, ts, rfl⟩ : ∃ t ts, term = t :: ts := by
    cases term with
    | nil => exact absurd rfl hne
    | cons t ts => exact ⟨t, ts, rfl⟩
  have ht : t.toNat < 128 := hterm t (List.mem_cons_self ..)
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hp := prefix_bytes (t :: ts) hterm (c :: cs)
    by_cases hc : c.toNat < 128
    · have h1 : c.utf8Size = 1 := (utf8Size_one_iff c).mpr hc
      have e : ((c :: cs).flatMap String.utf8EncodeChar).map lowerByte =
          lowerByte c.val.toUInt8 :: (cs.flatMap String.utf8EncodeChar).map lowerByte := by
        rw [List.flatMap_cons, String.utf8EncodeChar_eq_singleton h1]; rfl
      rw [e] at hp ⊢
      simp only [List.map_cons] at hp ih ⊢
      simp only [hasTermBytes, hasTerm]
      rw [hp, ih]
    · have hc' : 128 ≤ c.toNat := by omega
      rw [List.flatMap_cons, List.map_append,
        hasTermBytes_skip _ (byteOf t) (by rw [byteOf_toNat t ht]; exact ht) rfl _
          (utf8EncodeChar_high c hc'), ih]
      simp only [List.map_cons, hasTerm, toLower_high c hc']
      have h2 : (t :: ts).isPrefixOf (c :: cs.map Char.toLower) = false := by
        simp only [List.isPrefixOf]
        have : (t == c) = false := by apply beq_eq_false_iff_ne.mpr; intro e; subst e; omega
        rw [this, Bool.false_and]
      rw [h2, Bool.false_or]

/-- Whether `term`'s bytes start at offset `i` of `s`'s UTF-8 bytes, lowered. -/
def termAt (s : String) : List UInt8 → Nat → Bool
  | [], _ => true
  | t :: ts, i =>
    if h : i < s.utf8ByteSize then
      t == lowerByte (s.getUTF8Byte ⟨i⟩ (String.Pos.Raw.lt_iff.mpr h)) && termAt s ts (i + 1)
    else false

/-- Whether `term`'s bytes stand at some offset from `i` on of `s`'s UTF-8 bytes, lowered, the
first byte compared before the rest. -/
def termFrom (s : String) (term : List UInt8) (i : Nat) : Bool :=
  if h : i < s.utf8ByteSize then
    let here := match term with
      | [] => true
      | t :: ts =>
        t == lowerByte (s.getUTF8Byte ⟨i⟩ (String.Pos.Raw.lt_iff.mpr h)) && termAt s ts (i + 1)
    here || termFrom s term (i + 1)
  else false
termination_by s.utf8ByteSize - i

theorem bytes_length (s : String) : s.toByteArray.data.toList.length = s.utf8ByteSize := by
  rw [Array.length_toList, ByteArray.size_data, String.size_toByteArray]

theorem termAt_eq (s : String) (ts : List UInt8) (i : Nat) :
    termAt s ts i = ts.isPrefixOf ((s.toByteArray.data.toList.drop i).map lowerByte) := by
  induction ts generalizing i with
  | nil => simp [termAt, List.isPrefixOf]
  | cons t ts ih =>
    unfold termAt
    split
    · next h =>
      have hlt : i < s.toByteArray.data.toList.length := by rw [bytes_length]; exact h
      rw [List.drop_eq_getElem_cons hlt]
      simp only [List.map_cons, List.isPrefixOf]
      rw [ih (i + 1)]
      simp only [String.getUTF8Byte_eq_getElem, Array.getElem_toList]
      rfl
    · next h =>
      have hle : s.toByteArray.data.toList.length ≤ i := by rw [bytes_length]; omega
      rw [List.drop_of_length_le hle]
      rfl

theorem termFrom_eq (s : String) (term : List UInt8) (i : Nat) :
    termFrom s term i = hasTermBytes term ((s.toByteArray.data.toList.drop i).map lowerByte) := by
  unfold termFrom
  split
  · next h =>
    have hlt : i < s.toByteArray.data.toList.length := by rw [bytes_length]; exact h
    have hhere : (match term with
        | [] => true
        | t :: ts => t == lowerByte (s.getUTF8Byte ⟨i⟩ (String.Pos.Raw.lt_iff.mpr h)) &&
            termAt s ts (i + 1)) = termAt s term i := by
      cases term with
      | nil => rfl
      | cons t ts => simp only [termAt, h, ↓reduceDIte]
    rw [hhere, termAt_eq, termFrom_eq s term (i + 1), List.drop_eq_getElem_cons hlt]
    simp only [List.map_cons, hasTermBytes]
  · next h =>
    have hle : s.toByteArray.data.toList.length ≤ i := by rw [bytes_length]; omega
    rw [List.drop_of_length_le hle]
    rfl
termination_by s.utf8ByteSize - i

private theorem termFrom_spec (s : String) (term : List Char) (hterm : AsciiTerm term)
    (hne : term ≠ []) :
    termFrom s (term.map byteOf) 0 = hasTerm term (s.toList.map Char.toLower) := by
  rw [termFrom_eq, List.drop_zero, ← hasTerm_bytes term hterm hne s.toList,
    ← String.utf8Encode_toList]
  simp [List.utf8Encode]

/-- Whether `s`, ASCII-lowered, holds the lowercase ASCII `term`, read off its UTF-8 bytes. -/
public def holdsTerm (s term : String) : Bool := termFrom s (term.toList.map byteOf) 0

/-- `holdsTerm` finds exactly the occurrences a character-by-character search of the lowered
text finds. -/
public theorem holdsTerm_exact (s term : String) (hterm : ∀ c ∈ term.toList, c.toNat < 128)
    (hne : term.toList ≠ []) :
    holdsTerm s term = true ↔ term.toList <:+: s.toList.map Char.toLower := by
  unfold holdsTerm
  rw [termFrom_spec s term.toList hterm hne, hasTerm_iff _ _ hne]

/-- The payload, or `/* removed */` when it contains `endTag` in any ASCII case. -/
private def rawPayload (endTag payload : String) : String :=
  if holdsTerm payload endTag then "/* removed */" else payload

private theorem rawPayload_no_terminator (endTag payload : String)
    (hterm : AsciiTerm endTag.toList) (hne : endTag.toList ≠ [])
    (h : hasTerm endTag.toList ("/* removed */".toList.map Char.toLower) = false) :
    hasTerm endTag.toList ((rawPayload endTag payload).toList.map Char.toLower) = false := by
  unfold rawPayload
  split
  · exact h
  · next hc =>
    unfold holdsTerm at hc
    rw [termFrom_spec payload endTag.toList hterm hne] at hc
    simpa using hc

private theorem rawPayload_style_no_terminator (payload : String) :
    hasTerm "</style".toList
      ((rawPayload "</style" payload).toList.map Char.toLower) = false :=
  rawPayload_no_terminator _ _ (by decide) (by decide) (by decide)

private theorem rawPayload_script_no_terminator (payload : String) :
    hasTerm "</script".toList
      ((rawPayload "</script" payload).toList.map Char.toLower) = false :=
  rawPayload_no_terminator _ _ (by decide) (by decide) (by decide)

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
