module

public import LeanTex.Core.Html
public import Std.Data.HashSet

namespace LeanTex.Core.HtmlResource

/-- Media an embedded rendering URL may carry: inert images, font programs and validated SVG. -/
public inductive Media where
  | png | jpeg | ico | svg | ttf | otf
  deriving BEq, Repr

@[expose] public def Media.mime : Media → String
  | .png => "image/png"
  | .jpeg => "image/jpeg"
  | .ico => "image/x-icon"
  | .svg => "image/svg+xml"
  | .ttf => "font/ttf"
  | .otf => "font/otf"

/-- The byte at `i`, or zero past the end. -/
@[inline] private def byteAt (bytes : ByteArray) (i : Nat) : UInt8 :=
  if h : i < bytes.size then bytes[i] else 0

/-- The base64 alphabet's character for a sextet (RFC 4648 §4). -/
@[inline] private def sextet (k : UInt8) : UInt8 :=
  if k < 26 then k + 65 else if k < 52 then k + 71 else if k < 62 then k - 4
  else if k == 62 then 43 else 47

/-- Every sextet's character is RFC 4648's base64 alphabet at that index. -/
theorem sextet_rfc4648 :
    (List.range 64).map (fun k => (sextet k.toUInt8).toNat) =
      "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.map Char.toNat := by
  decide

private theorem sextet_lt (k : UInt8) : sextet k < 128 := by
  unfold sextet
  have := k.toNat_lt
  split
  · next h => simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_add] at h ⊢; simp at h ⊢; omega
  · split
    · next h => simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_add] at h ⊢; simp at h ⊢; omega
    · split
      · next h1 h2 h3 =>
        simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_sub] at h1 h2 h3 ⊢
        simp at h1 h2 h3 ⊢; omega
      · split <;> decide

private theorem ascii_char (n : Nat) (h : n < 128) :
    (Char.ofNat n).utf8Size = 1 ∧ (Char.ofNat n).toUInt8 = n.toUInt8 := by
  have hv : n.isValidChar := Or.inl (by omega)
  simp only [Char.ofNat, hv, ↓reduceDIte, Char.ofNatAux, Char.utf8Size, Char.toUInt8]
  constructor
  · simp [UInt32.le_iff_toNat_le]; omega
  · simp [UInt32.toUInt8, UInt8.ofNat]

/-- `n` bytes, each ASCII, so the string they spell needs no validation. -/
private abbrev AsciiOf (n : Nat) := { b : ByteArray // b.size = n ∧ ∀ i (h : i < b.size), b[i] < 128 }

private theorem isValidUTF8_of_ascii (b : ByteArray) (h : ∀ i (hi : i < b.size), b[i] < 128) :
    b.IsValidUTF8 := by
  refine .intro (b.data.toList.map fun x => Char.ofNat x.toNat) ?_
  have hl : ∀ l : List UInt8, (∀ x ∈ l, x < 128) →
      (l.map fun x => Char.ofNat x.toNat).flatMap String.utf8EncodeChar = l := by
    intro l hl
    induction l with
    | nil => rfl
    | cons x xs ih =>
      have hx : x < 128 := hl x (List.mem_cons_self ..)
      obtain ⟨h1, h2⟩ := ascii_char x.toNat hx
      have hv : (Char.ofNat x.toNat).val.toUInt8 = x := by
        have h3 : (Char.ofNat x.toNat).val.toUInt8 = x.toNat.toUInt8 := h2
        rw [h3, Nat.toUInt8_eq, UInt8.ofNat_toNat]
      simp only [List.map_cons, List.flatMap_cons, String.utf8EncodeChar_eq_singleton h1, hv,
        List.singleton_append]
      rw [ih fun y hy => hl y (List.mem_cons_of_mem _ hy)]
  have hall : ∀ x ∈ b.data.toList, x < 128 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hi' : i < b.size := by simpa [← ByteArray.size_data] using hi
    simpa [ByteArray.getElem_eq_getElem_data] using h i hi'
  rw [List.utf8Encode, hl _ hall]
  ext1
  simp

@[inline] private def setAscii (out : AsciiOf n) (i : Nat) (x : UInt8) (hx : x < 128)
    (hi : i < n) : AsciiOf n :=
  ⟨out.1.set i x (by rw [out.2.1]; exact hi), by
    have hs : (out.1.set i x (by rw [out.2.1]; exact hi)).size = out.1.size := by
      simp [← ByteArray.size_data, ByteArray.data_set]
    refine ⟨hs.trans out.2.1, fun j hj => ?_⟩
    simp only [ByteArray.getElem_eq_getElem_data, ByteArray.data_set, Array.getElem_set]
    split
    · exact hx
    · exact out.2.2 j (by rw [hs] at hj; exact hj)⟩

/-- `a` doubled until it holds at least `n` bytes. -/
private def grown (n : Nat) (a : ByteArray) (ha : 0 < a.size) : ByteArray :=
  if a.size < n then grown n (a ++ a) (by simp; omega) else a
termination_by n - a.size
decreasing_by simp; omega

private theorem grown_spec (n : Nat) (a : ByteArray) (ha : 0 < a.size)
    (h : ∀ i (hi : i < a.size), a[i] < 128) :
    n ≤ (grown n a ha).size ∧ ∀ i (hi : i < (grown n a ha).size), (grown n a ha)[i] < 128 := by
  unfold grown
  split
  · next hlt =>
    apply grown_spec
    intro i hi
    by_cases hia : i < a.size
    · rw [ByteArray.getElem_append_left hia]; exact h i hia
    · rw [ByteArray.getElem_append_right (by omega)]; exact h _ _
  · next hge => exact ⟨by omega, h⟩
termination_by n - a.size
decreasing_by simp; omega

/-- `n` bytes of `=`, base64's padding, built by doubling. -/
private def pads (n : Nat) : AsciiOf n :=
  let one : ByteArray := ⟨#[61]⟩
  have hone : ∀ i (hi : i < one.size), one[i] < 128 := by
    intro i hi
    have : i = 0 := by simp [one, ByteArray.size] at hi; omega
    have h61 : one[i] = 61 := by subst this; rfl
    rw [h61]; decide
  let spec := grown_spec n one (by decide) hone
  let a := grown n one (by decide)
  ⟨a.extract 0 n, by
    refine ⟨by simp [a]; omega, fun i hi => ?_⟩
    rw [ByteArray.getElem_extract]
    exact spec.2 _ _⟩

/-- 4096 bytes of padding, the block a buffer is filled from. -/
private def block : AsciiOf 4096 := pads 4096

private theorem fill_size (a : ByteArray) (k : Nat) (hk : k ≤ 4096) :
    (block.1.copySlice 0 a a.size k).size = a.size + k := by
  rw [ByteArray.copySlice_eq_append]
  simp only [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_data, block.2.1]
  omega

/-- `a` filled with padding to `n` bytes, a block at a time within its capacity. -/
private def fill (n : Nat) (a : ByteArray) : ByteArray :=
  if a.size < n then fill n (block.1.copySlice 0 a a.size (min 4096 (n - a.size))) else a
termination_by n - a.size
decreasing_by rw [fill_size _ _ (Nat.min_le_left _ _)]; omega

private theorem fill_spec (n : Nat) (a : ByteArray) (ha : a.size ≤ n)
    (h : ∀ i (hi : i < a.size), a[i] < 128) :
    (fill n a).size = n ∧ ∀ i (hi : i < (fill n a).size), (fill n a)[i] < 128 := by
  unfold fill
  split
  · next hlt =>
    have hs := fill_size a (min 4096 (n - a.size)) (Nat.min_le_left _ _)
    apply fill_spec
    · omega
    · intro i hi
      have hb := block.2.2
      have hb1 := block.2.1
      simp only [ByteArray.copySlice_eq_append] at hi ⊢
      by_cases hia : i < a.size
      · rw [ByteArray.getElem_append_left (by simp [ByteArray.size_append]; omega),
          ByteArray.getElem_append_left (by simp; omega),
          ByteArray.getElem_extract]
        exact h _ (by omega)
      · rw [ByteArray.getElem_append_left (by simp [ByteArray.size_append, hb1]; omega),
          ByteArray.getElem_append_right (by simp; omega),
          ByteArray.getElem_extract]
        exact hb _ (by simp [ByteArray.size_extract, ByteArray.size_append, hb1] at hi ⊢; omega)
  · next hge => exact ⟨by omega, h⟩
termination_by n - a.size
decreasing_by rw [fill_size _ _ (Nat.min_le_left _ _)]; omega

/-- `n` bytes of `=` in a buffer of exactly that capacity. -/
private def padsExact (n : Nat) : AsciiOf n :=
  let spec := fill_spec n (ByteArray.emptyWithCapacity n) (Nat.zero_le n)
    (fun _ hi => absurd hi (Nat.not_lt_zero _))
  ⟨fill n (ByteArray.emptyWithCapacity n), spec.1, spec.2⟩

/-- RFC 4648's base64 alphabet as bytes, read by a sextet's index. -/
private def alphabet : ByteArray := ⟨(Array.range 64).map fun k => sextet k.toUInt8⟩

private theorem alphabet_size : alphabet.size = 64 := by
  simp [alphabet, ← ByteArray.size_data]

/-- The alphabet is RFC 4648's, a sextet's character at its index. -/
theorem alphabet_rfc4648 : alphabet.data.toList.map UInt8.toNat =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.map Char.toNat := by
  rw [← sextet_rfc4648]
  simp [alphabet, Array.toList_map, Array.toList_range, List.map_map, Function.comp_def]

/-- The alphabet's character for the low six bits of `k`. -/
@[inline] private def char (k : UInt32) : UInt8 :=
  alphabet[(k &&& 63).toNat]'(by
    rw [alphabet_size, UInt32.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide))

private theorem char_lt (k : UInt32) : char k < 128 := by
  simp only [char, alphabet, ByteArray.getElem_eq_getElem_data, Array.getElem_map,
    Array.getElem_range]
  exact sextet_lt _

/-- The four characters of each whole group of three bytes from `i`, written from `o`. -/
private def groups (bytes : ByteArray) (out : AsciiOf n) (i o : Nat) : AsciiOf n :=
  if h : i + 2 < bytes.size ∧ o + 3 < n then
    let x := (bytes[i].toUInt32 <<< 16) ||| (bytes[i + 1].toUInt32 <<< 8) ||| bytes[i + 2].toUInt32
    let out := setAscii out o (char (x >>> 18)) (char_lt _) (by omega)
    let out := setAscii out (o + 1) (char (x >>> 12)) (char_lt _) (by omega)
    let out := setAscii out (o + 2) (char (x >>> 6)) (char_lt _) (by omega)
    let out := setAscii out (o + 3) (char x) (char_lt _) (by omega)
    groups bytes out (i + 3) (o + 4)
  else out
termination_by bytes.size - i

public def base64 (bytes : ByteArray) : String :=
  let n := (bytes.size + 2) / 3 * 4
  let out := groups bytes (padsExact n) 0 0
  let whole := bytes.size / 3 * 3
  let o := bytes.size / 3 * 4
  let a := (byteAt bytes whole).toUInt32
  let b := (byteAt bytes (whole + 1)).toUInt32
  let out : AsciiOf n :=
    if h : whole < bytes.size ∧ o + 1 < n then
      let out := setAscii out o (char (a >>> 2)) (char_lt _) (by omega)
      let out := setAscii out (o + 1) (char ((a <<< 4) ||| (b >>> 4))) (char_lt _) h.2
      if h2 : whole + 1 < bytes.size ∧ o + 2 < n then
        setAscii out (o + 2) (char (b <<< 2)) (char_lt _) h2.2
      else out
    else out
  String.fromUTF8 out.1 (isValidUTF8_of_ascii out.1 out.2.2)

/-- A resource's data URL (RFC 2397). -/
public def dataUrl (media : Media) (bytes : ByteArray) : String :=
  let payload := base64 bytes
  "data:" ++ media.mime ++ ";base64," ++ payload

/-- Captured bytes and their media; the data URL is computed on its first read and kept. -/
public structure Embedded where
  media : Media
  bytes : ByteArray
  cachedUri : Thunk String := Thunk.mk fun _ => dataUrl media bytes
  cachedUri_exact : cachedUri.get = dataUrl media bytes := by rfl

public instance : BEq Embedded where
  beq a b := a.media == b.media && a.bytes == b.bytes

public def Embedded.uri (r : Embedded) : String := r.cachedUri.get

public theorem Embedded.uri_exact (r : Embedded) : r.uri = dataUrl r.media r.bytes :=
  r.cachedUri_exact

/-- Whether the bytes may render: SVG among `svgChecked`, other media by their format signature. -/
public def Embedded.ready (svgChecked : Array ByteArray) (r : Embedded) : Bool :=
  match r.media with
  | .svg => svgChecked.contains r.bytes
  | .png => r.bytes.extract 0 8 == ⟨#[137, 80, 78, 71, 13, 10, 26, 10]⟩
  | .jpeg => r.bytes.extract 0 3 == ⟨#[255, 216, 255]⟩
  | .ico => r.bytes.extract 0 4 == ⟨#[0, 0, 1, 0]⟩
  | .ttf => r.bytes.extract 0 4 == ⟨#[0, 1, 0, 0]⟩
  | .otf => r.bytes.extract 0 4 == "OTTO".toUTF8

public inductive Request where
  | url (value : String)
  | localFragment (value : String)
  | script (value : String)
  | refused (reason : String)
  deriving BEq, Repr

private inductive CssState where
  | plain | slash | comment | star | quoted (quote : Char) | escaped (quote : Char) | url
  deriving BEq

private structure CssScan where
  state : CssState := .plain
  word : String := ""
  requests : Array Request := #[]

/-- The CSS functions the scanner admits besides `url()`, which it reads as a request; any other
function is refused. -/
private def cssFunction (word : String) : Bool :=
  ["var", "calc", "min", "max", "clamp", "env", "rgb", "rgba", "hsl", "hsla",
   "oklab", "oklch", "lab", "lch", "color", "color-mix", "light-dark",
   "linear-gradient", "radial-gradient", "conic-gradient", "repeating-linear-gradient",
   "repeating-radial-gradient", "repeating-conic-gradient", "cubic-bezier", "steps",
   "linear", "translate", "translatex", "translatey", "translatez", "translate3d",
   "scale", "scalex", "scaley", "scalez", "scale3d", "rotate", "rotatex", "rotatey",
   "rotatez", "rotate3d", "skew", "skewx", "skewy", "matrix", "matrix3d",
   "perspective", "inset", "circle", "ellipse", "polygon", "path", "blur",
   "brightness", "contrast", "drop-shadow", "grayscale", "hue-rotate", "invert",
   "opacity", "saturate", "sepia", "counter", "counters", "repeat", "minmax",
   "fit-content", "format", "tech", "is", "where", "not", "has", "nth-child",
   "nth-last-child", "nth-of-type", "nth-last-of-type", "lang", "dir", "selector",
   "supports", "scroll", "view", "attr", "anchor", "anchor-size"].contains word

private def flushWord (s : CssScan) : CssScan :=
  let word := s.word.toLower
  let bad := word.startsWith "@" &&
    !["@font-face", "@media", "@supports", "@keyframes", "@container", "@page",
      "@layer", "@counter-style", "@property", "@starting-style"].contains word
  { s with word := "", requests := if bad then
      s.requests.push (.refused ("unsupported CSS at-rule: " ++ word)) else s.requests }

private def cssPlain (s : CssScan) (c : Char) : CssScan :=
  -- `@` starts a token even after hyphens, so `<!--@import` still reads as an at-rule
  if c == '@' then { flushWord s with word := "@" }
  else if c.isAlphanum || c == '-' || c == '_' then
    { s with word := s.word.push c }
  else if c == '(' then
    let word := s.word.toLower
    if word == "url" then { s with state := .url, word := "" }
    else
      let s := flushWord s
      if word.isEmpty || cssFunction word then s else
        { s with requests := s.requests.push (.refused ("unsupported CSS function: " ++ word)) }
  else
    let s := flushWord s
    if c == '/' then { s with state := .slash }
    else if c == '"' || c == '\'' then { s with state := .quoted c }
    else s

private def cssStep (s : CssScan) (c : Char) : CssScan :=
  if c == '\u0000' || (c.toNat < 32 && !c.isWhitespace) then
    { s with requests := s.requests.push (.refused "unsupported CSS control character") }
  else match s.state with
  | .quoted q =>
    if c == '\\' then { s with state := .escaped q }
    else if c == q then { s with state := .plain }
    else if c == '\n' || c == '\r' || c == '\u000c' then
      { s with requests := s.requests.push (.refused "unterminated CSS string") }
    else s
  | .escaped q => { s with state := .quoted q }
  | .comment => if c == '*' then { s with state := .star } else s
  | .star => if c == '/' then { s with state := .plain }
    else if c == '*' then s else { s with state := .comment }
  | .plain | .slash | .url =>
    if c == '\\' then
      { s with requests := s.requests.push (.refused "unsupported CSS identifier or URL escape") }
    else match s.state with
    | .plain => cssPlain s c
    | .slash => if c == '*' then { s with state := .comment }
      else cssPlain { s with state := .plain } c
    | .url =>
      if c == ')' then
        let v := s.word.trimAscii.toString
        let v := if (v.startsWith "\"" && v.endsWith "\"") ||
            (v.startsWith "'" && v.endsWith "'") then (v.drop 1 |>.dropEnd 1).toString else v
        { s with state := .plain, word := "", requests := s.requests.push (.url v) }
      else { s with word := s.word.push c }
    | .quoted _ | .escaped _ | .comment | .star => s

/-- The rendering dependencies of a stylesheet; unsupported syntax becomes a refused request. -/
public def cssRequests (css : String) : Array Request :=
  let s := flushWord (css.foldl cssStep {})
  let requests := if s.state == .plain || s.state == .slash then s.requests else
    s.requests.push (.refused "unterminated CSS token")
  if Html.holdsTerm css "</style" then
    requests.push (.refused "CSS contains an HTML raw-text terminator")
  else requests

private def attr (attrs : Array (String × String)) (name : String) : String :=
  ((attrs.find? fun a => a.1.toLower == name).map (·.2)).getD ""

private def navigation (tag : String) (attrs : Array (String × String)) : Bool :=
  tag == "a" || tag == "area" ||
    (tag == "link" && (attr attrs "rel" == "canonical" ||
      (attr attrs "rel" == "alternate" && attr attrs "type" == "text/markdown")))

private def passiveTag (tag : String) : Bool :=
  ["html", "head", "body", "meta", "title", "link", "a", "area", "abbr", "address",
   "article", "aside", "b", "blockquote", "br", "caption", "cite", "code", "col",
   "colgroup", "dd", "del", "details", "dfn", "div", "dl", "dt", "em", "figcaption",
   "figure", "footer", "h1", "h2", "h3", "h4", "h5", "h6", "header", "hr", "i",
   "img", "ins", "kbd", "li", "main", "mark", "nav", "ol", "p", "picture", "pre",
   "q", "rp", "rt", "ruby", "s", "samp", "section", "small", "source", "span",
   "strong", "sub", "summary", "sup", "table", "tbody", "td", "tfoot", "th", "thead",
   "time", "tr", "u", "ul", "var", "wbr", "svg", "g", "path", "rect", "circle",
   "ellipse", "line", "polyline", "polygon", "text", "tspan", "defs", "use", "symbol",
   "clippath", "mask", "lineargradient", "radialgradient", "stop", "pattern", "marker",
   "desc", "foreignobject", "math", "mrow", "mi", "mn", "mo", "mtext", "mspace", "ms", "merror",
   "mfrac", "msqrt", "mroot", "mstyle", "mpadded", "mphantom", "mfenced", "menclose",
   "msub", "msup", "msubsup", "munder", "mover", "munderover", "mmultiscripts",
   "mprescripts", "none", "mtable", "mtr", "mtd", "mlabeledtr", "semantics"].contains tag

/-- Attributes whose fragment reference resolves inside the same SVG tree. -/
private def svgReferenceAttr (tag name : String) : Bool :=
  if name == "href" || name == "xlink:href" then
    ["use", "lineargradient", "radialgradient", "pattern"].contains tag
  else
    ["svg", "g", "path", "rect", "circle", "ellipse", "line", "polyline", "polygon",
      "text", "tspan", "defs", "use", "symbol", "clippath", "mask", "lineargradient",
      "radialgradient", "stop", "pattern", "marker"].contains tag &&
    ["fill", "stroke", "filter", "clip-path", "mask", "marker", "marker-start",
      "marker-mid", "marker-end"].contains name

/-- One attribute's rendering dependencies, or its refusal. -/
public def attrRequest (tag : String) (attrs : Array (String × String)) (kv : String × String) :
    Array Request :=
  let (name, value) := kv
  if name.isEmpty || !name.toList.all (fun c =>
      c.isAlphanum || c == '-' || c == '_' || c == ':') then
    #[.refused "unsupported HTML attribute name"]
  else
  let name := name.toLower
  if name.startsWith "on" ||
      ["srcdoc", "xml:base", "http-equiv", "is", "attributionsrc"].contains name then
    #[.refused ("unsupported active HTML attribute: " ++ name)]
  else if Html.scriptLink name value then
    #[.refused "a link whose URL runs script"]
  else if svgReferenceAttr tag name then
    let refs := if name == "href" || name == "xlink:href" then #[Request.url value]
      else cssRequests value
    refs.map (fun r => match r with
      | .url value => if value.startsWith "#" then .localFragment value else r
      | .localFragment _ | .script _ | .refused _ => r)
  else if name == "style" || ["fill", "stroke", "filter", "clip-path", "mask",
      "marker", "marker-start", "marker-mid", "marker-end", "cursor"].contains name then
    cssRequests value
  else if ["src", "srcset", "imagesrcset", "poster", "background", "data"].contains name ||
      ((name == "href" || name == "xlink:href") && !navigation tag attrs) then
    -- a generated srcset is one data URL with no descriptor, so it is not split
    #[.url value]
  else #[]

public def attrRequests (tag : String) (attrs : Array (String × String)) : Array Request :=
  attrs.foldl (init := #[]) fun acc kv =>
    let more := attrRequest tag attrs kv
    acc ++ more

mutual
  /-- The rendering dependencies of a node; raw style and script are refused outside HTML
  raw-text contexts. -/
  public def nodeRequests (rawTextAllowed : Bool) (acc : Array Request) : Html.Node → Array Request
    | .text _ => acc
    | .style css =>
      if !rawTextAllowed then
        acc.push (.refused "raw HTML style is inside an unsupported parsing context")
      else
        let refs := cssRequests css
        acc ++ refs
    | .script attrs js =>
      if !rawTextAllowed then
        acc.push (.refused "raw HTML script is inside an unsupported parsing context")
      else
        let acc := acc ++ attrRequests "script" attrs
        -- `<!--` enters the script escape states, where a closing tag becomes payload
        let acc := if (attrs.any fun a => a.1.toLower == "src") || js.contains '\u0000' ||
            Html.holdsTerm js "</script" || Html.holdsTerm js "<!--" then
          acc.push (.refused "a script carries a source, a NUL or HTML raw-text control syntax") else acc
        if attr attrs "type" == "application/ld+json" then acc
        else acc.push (.script js)
    | .elem tag attrs kids =>
      let tag := tag.toLower
      let acc := acc ++ attrRequests tag attrs
      let acc := if passiveTag tag then acc else
        acc.push (.refused ("unsupported active HTML element: " ++ tag))
      let rawTextAllowed := rawTextAllowed && passiveTag tag &&
        !["svg", "foreignobject", "math", "title"].contains tag && !Html.voidTags.contains tag
      listRequests rawTextAllowed acc kids.toList

  public def listRequests (rawTextAllowed : Bool) (acc : Array Request) : List Html.Node → Array Request
    | [] => acc
    | node :: rest => listRequests rawTextAllowed (nodeRequests rawTextAllowed acc node) rest
end

/-- Artifact-specific: a `foreignObject` subtree keeps raw payloads refused. -/
public theorem foreignObject_requests_exact (rawTextAllowed : Bool) (acc : Array Request)
    (attrs : Array (String × String)) (kids : Array Html.Node) :
    nodeRequests rawTextAllowed acc (.elem "foreignObject" attrs kids) =
      listRequests false (acc ++ attrRequests "foreignobject" attrs) kids.toList := by
  simp only [nodeRequests, String.toLower, String.map_eq_internal]
  cases rawTextAllowed <;> rfl

public def requests (head body : Array Html.Node) : Array Request :=
  listRequests true (listRequests true #[] head.toList) body.toList

/-- Whether a request resolves: a URL to a ready embedded resource, a fragment, or a declared
script; a navigation link is no request but where its URL runs script, so its other URL schemes
are outside the gate. -/
public def resolves (resources : Array Embedded) (svgChecked : Array ByteArray)
    (scripts : Array String) : Request → Bool
  | .url value => resources.any (fun r => r.ready svgChecked && r.uri == value)
  | .localFragment value => value.startsWith "#" && value.length > 1 &&
      !value.toList.any Char.isWhitespace
  | .script value => scripts.any fun s => !s.isEmpty && value == s
  | .refused _ => false

/-- The URIs of the ready resources, as a concrete index so preparation runs once. -/
public def compile (resources : Array Embedded) (svgChecked : Array ByteArray) : Std.HashSet String :=
  Std.HashSet.ofArray (resources.filterMap fun r =>
    if r.ready svgChecked then some r.uri else none)

public def resolvesCompiled (urls : Std.HashSet String) (scripts : Array String) : Request → Bool
  | .url value => urls.contains value
  | request => resolves #[] #[] scripts request

/-- Artifact-specific. -/
public theorem compile_exact (resources : Array Embedded) (svgChecked : Array ByteArray)
    (scripts : Array String) : resolvesCompiled (compile resources svgChecked) scripts =
      resolves resources svgChecked scripts := by
  funext request
  cases request with
  | url value =>
    apply Bool.eq_iff_iff.mpr
    simp only [resolvesCompiled, compile, resolves]
    rw [Array.any_eq_true']
    simp
  | localFragment value => rfl
  | script value => rfl
  | refused reason => rfl

public theorem compile_admission_exact (resources : Array Embedded) (svgChecked : Array ByteArray)
    (scripts : Array String) (projected : Array Request) :
    (projected.find? fun r => !resolvesCompiled (compile resources svgChecked) scripts r) = none ↔
      projected.all (resolves resources svgChecked scripts) = true := by
  rw [compile_exact, Array.find?_eq_none, Array.all_eq_true']
  simp

/-- Artifact-specific. -/
public theorem style_context_refused_exact (resources : Array Embedded) (svgChecked : Array ByteArray)
    (scripts : Array String) (acc : Array Request) (css : String) :
    (nodeRequests false acc (.style css)).all (resolves resources svgChecked scripts) = false := by
  simp [nodeRequests, resolves]

public theorem script_context_refused_exact (resources : Array Embedded) (svgChecked : Array ByteArray)
    (scripts : Array String) (acc : Array Request) (attrs : Array (String × String)) (js : String) :
    (nodeRequests false acc (.script attrs js)).all
      (resolves resources svgChecked scripts) = false := by
  simp [nodeRequests, resolves]

/-- A page whose rendering requests all resolve against its embedded resources. -/
public structure ClosedPage (scripts : Array String) where
  lang : String
  head : Array Html.Node
  body : Array Html.Node
  resources : Array Embedded
  svgChecked : Array ByteArray
  closed : (requests head body).all (resolves resources svgChecked scripts) = true

public def ClosedPage.render (page : ClosedPage scripts) : String :=
  Html.document page.lang page.head page.body

/-- A request's reference as a diagnostic quotes it: a data URL cut before its payload,
long values truncated. -/
public def referenceLabel (value : String) : String :=
  let shown := if value.toLower.startsWith "data:" then
      (value.takeWhile (· != ',')).toString ++ ",…"
    else value
  (if shown.length > 160 then (shown.take 160).toString ++ "…" else shown).quote

/-- Close a page, or name the first request that does not resolve. -/
public def close (resources : Array Embedded) (svgChecked : Array ByteArray)
    (scripts : Array String) (lang : String) (head body : Array Html.Node) :
    Except String (ClosedPage scripts) :=
  let urls := compile resources svgChecked
  let projected := requests head body
  match h : projected.find? (fun r => !resolvesCompiled urls scripts r) with
  | none =>
    .ok { lang, head, body, resources, svgChecked, closed :=
      (compile_admission_exact resources svgChecked scripts projected).mp h }
  | some r => .error (match r with
      | .url value => "HTML rendering URL " ++ referenceLabel value ++
          " has no embedded, validated resource"
      | .localFragment value =>
        let label := referenceLabel value
        "unsupported SVG fragment reference " ++ label
      | .script _ => "an HTML script is none of the scripts the page declares"
      | .refused why => why)

/-- Artifact-specific. -/
public theorem close_covers (resources : Array Embedded) (svgChecked : Array ByteArray)
    (scripts : Array String) (lang : String) (head body : Array Html.Node) {page : ClosedPage scripts}
    (h : close resources svgChecked scripts lang head body = .ok page) :
    page.render = Html.document lang head body ∧
      ∀ r ∈ requests head body, resolves resources svgChecked scripts r = true := by
  dsimp only [close] at h
  split at h
  · next hc =>
    cases h
    exact ⟨rfl, Array.all_eq_true'.mp
      ((compile_admission_exact resources svgChecked scripts _).mp hc)⟩
  · contradiction

/-- A page `close` returns is the one it was given. -/
public theorem close_fields {resources : Array Embedded} {svgChecked : Array ByteArray}
    {scripts : Array String} {lang : String} {head body : Array Html.Node} {page : ClosedPage scripts}
    (h : close resources svgChecked scripts lang head body = .ok page) :
    page.lang = lang ∧ page.head = head ∧ page.body = body := by
  dsimp only [close] at h
  split at h
  · cases h; exact ⟨rfl, rfl, rfl⟩
  · contradiction

end LeanTex.Core.HtmlResource
