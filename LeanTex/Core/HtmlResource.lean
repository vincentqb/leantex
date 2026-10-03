import LeanTex.Core.Html

namespace LeanTex.Core.HtmlResource

/-- Only inert binary images, font programs, and externally checked SVGs
can supply a rendering URL. CSS and executable documents are not opaque data. -/
inductive Media where
  | png | jpeg | ico | svg | ttf | otf
  deriving BEq, Repr

def Media.mime : Media → String
  | .png => "image/png"
  | .jpeg => "image/jpeg"
  | .ico => "image/x-icon"
  | .svg => "image/svg+xml"
  | .ttf => "font/ttf"
  | .otf => "font/otf"

def base64 (bytes : ByteArray) : String := Id.run do
  let alphabet := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toUTF8
  let mut out := ByteArray.emptyWithCapacity ((bytes.size + 2) / 3 * 4)
  for i in [0:(bytes.size + 2) / 3] do
    let a := bytes[i * 3]?.getD 0
    let b := bytes[i * 3 + 1]?.getD 0
    let c := bytes[i * 3 + 2]?.getD 0
    out := out.push (alphabet[(a >>> 2).toNat]?.getD 61)
    out := out.push (alphabet[(((a &&& 3) <<< 4) ||| (b >>> 4)).toNat]?.getD 61)
    out := out.push (if i * 3 + 1 < bytes.size then
      alphabet[(((b &&& 15) <<< 2) ||| (c >>> 6)).toNat]?.getD 61 else 61)
    out := out.push (if i * 3 + 2 < bytes.size then alphabet[(c &&& 63).toNat]?.getD 61 else 61)
  return String.fromUTF8! out

structure Embedded where
  media : Media
  bytes : ByteArray
  deriving BEq

def Embedded.uri (r : Embedded) : String :=
  "data:" ++ r.media.mime ++ ";base64," ++ base64 r.bytes

/-- SVG approval names the exact bytes passed through the driver's existing
parsed-XML validator. That validator and binary/browser decoders are external
trust boundaries; no theorem here claims to implement XML or browser semantics. -/
def Embedded.ready (svgChecked : Array ByteArray) (r : Embedded) : Bool :=
  match r.media with
  | .svg => svgChecked.contains r.bytes
  | .png => r.bytes.extract 0 8 == ⟨#[137, 80, 78, 71, 13, 10, 26, 10]⟩
  | .jpeg => r.bytes.extract 0 3 == ⟨#[255, 216, 255]⟩
  | .ico => r.bytes.extract 0 4 == ⟨#[0, 0, 1, 0]⟩
  | .ttf => r.bytes.extract 0 4 == ⟨#[0, 1, 0, 0]⟩
  | .otf => r.bytes.extract 0 4 == "OTTO".toUTF8

inductive Request where
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

/-- A deliberately bounded CSS vocabulary. Unknown functions and at-rules
are refused, including string-taking image()/image-set(), imports, identifier/URL escapes,
and local() font lookup. Escapes inside inert strings retain their CSS meaning. Extending the vocabulary owes a dependency reading. -/
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
   "supports", "scroll", "view"].contains word

private def flushWord (s : CssScan) : CssScan :=
  let word := s.word.toLower
  let bad := word.startsWith "@" &&
    !["@font-face", "@media", "@supports", "@keyframes", "@container", "@page",
      "@layer", "@counter-style", "@property", "@starting-style"].contains word
  { s with word := "", requests := if bad then
      s.requests.push (.refused ("unsupported CSS at-rule: " ++ word)) else s.requests }

private def cssPlain (s : CssScan) (c : Char) : CssScan :=
  -- An at-keyword starts a token, even after the hyphens of HTML's CSS
  -- comment opener. Absorbing @ into that word would hide a string import.
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

/-- Projection of rendering dependencies from the supported CSS subset.
Refusals remain requests, so unsupported syntax cannot disappear from the gate. -/
def cssRequests (css : String) : Array Request :=
  let s := flushWord (css.foldl cssStep {})
  let requests := if s.state == .plain || s.state == .slash then s.requests else
    s.requests.push (.refused "unterminated CSS token")
  if (css.toLower.splitOn "</style").length > 1 then
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
   "desc", "math", "mrow", "mi", "mn", "mo", "mtext", "mspace", "ms", "merror",
   "mfrac", "msqrt", "mroot", "mstyle", "mpadded", "mphantom", "mfenced", "menclose",
   "msub", "msup", "msubsup", "munder", "mover", "munderover", "mmultiscripts",
   "mprescripts", "none", "mtable", "mtr", "mtd", "mlabeledtr", "semantics"].contains tag

/-- SVG reference attributes resolve a fragment in the same SVG tree. A
fragment in a fetch context (CSS url(), image src, or srcset) is not evidence
of closure: the browser can fetch the current document URL. -/
private def svgReferenceAttr (tag name : String) : Bool :=
  if name == "href" || name == "xlink:href" then
    ["use", "lineargradient", "radialgradient", "pattern"].contains tag
  else
    ["svg", "g", "path", "rect", "circle", "ellipse", "line", "polyline", "polygon",
      "text", "tspan", "defs", "use", "symbol", "clippath", "mask", "lineargradient",
      "radialgradient", "stop", "pattern", "marker"].contains tag &&
    ["fill", "stroke", "filter", "clip-path", "mask", "marker", "marker-start",
      "marker-mid", "marker-end"].contains name

private def attrRequests (tag : String) (attrs : Array (String × String)) : Array Request :=
  attrs.foldl (init := #[]) fun acc (name, value) =>
    if name.isEmpty || !name.toList.all (fun c =>
        c.isAlphanum || c == '-' || c == '_' || c == ':') then
      acc.push (.refused "unsupported HTML attribute name")
    else
    let name := name.toLower
    if name.startsWith "on" || ["srcdoc", "xml:base", "http-equiv", "is"].contains name then
      acc.push (.refused ("unsupported active HTML attribute: " ++ name))
    else if svgReferenceAttr tag name then
      let refs := if name == "href" || name == "xlink:href" then #[Request.url value]
        else cssRequests value
      acc ++ refs.map (fun r => match r with
        | .url value => if value.startsWith "#" then .localFragment value else r
        | .localFragment _ | .script _ | .refused _ => r)
    else if name == "style" || ["fill", "stroke", "filter", "clip-path", "mask",
        "marker", "marker-start", "marker-mid", "marker-end", "cursor"].contains name then
      let refs := cssRequests value
      acc ++ refs
    else if ["src", "srcset", "imagesrcset", "poster", "background", "data"].contains name ||
        ((name == "href" || name == "xlink:href") && !navigation tag attrs) then
      -- Generated srcset carries one data URL with no descriptor. Any richer
      -- srcset must be modeled explicitly, rather than split at data's comma.
      acc.push (.url value)
    else acc

mutual
  /-- A typed artifact walk, not an IR walk: declarations and nested children
  contribute to the same dependency list, including hidden/media-selected nodes.
  Raw payloads are checked only in HTML parsing contexts. SVG/MathML, title
  RCDATA, and discarded void children do not have the raw-text semantics this
  projection relies on. The refusal latches through their whole subtree,
  conservatively including foreign-content integration points. -/
  def nodeRequests (rawTextAllowed : Bool) (acc : Array Request) : Html.Node → Array Request
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
        let acc := if (attrs.any fun a => a.1.toLower == "src") ||
            (js.toLower.splitOn "</script").length > 1 then
          acc.push (.refused "a script carries a source or raw-text terminator") else acc
        if attr attrs "type" == "application/ld+json" then acc
        else acc.push (.script js)
    | .elem tag attrs kids =>
      let tag := tag.toLower
      let acc := acc ++ attrRequests tag attrs
      let acc := if passiveTag tag then acc else
        acc.push (.refused ("unsupported active HTML element: " ++ tag))
      let rawTextAllowed := rawTextAllowed && passiveTag tag &&
        !["svg", "math", "title"].contains tag && !Html.voidTags.contains tag
      listRequests rawTextAllowed acc kids.toList

  def listRequests (rawTextAllowed : Bool) (acc : Array Request) : List Html.Node → Array Request
    | [] => acc
    | node :: rest => listRequests rawTextAllowed (nodeRequests rawTextAllowed acc node) rest
end

def requests (head body : Array Html.Node) : Array Request :=
  listRequests true (listRequests true #[] head.toList) body.toList

def resolves (resources : Array Embedded) (svgChecked : Array ByteArray)
    (deckScript : String) : Request → Bool
  | .url value => resources.any (fun r => r.ready svgChecked && r.uri == value)
  | .localFragment value => value.startsWith "#" && value.length > 1 &&
      !value.toList.any Char.isWhitespace
  | .script value => !deckScript.isEmpty && value == deckScript
  | .refused _ => false

/-- Artifact-specific: no resource evidence can certify a raw style in a
context where the dependency projection does not model its parsing. -/
theorem style_context_refused_exact (resources : Array Embedded) (svgChecked : Array ByteArray)
    (deckScript : String) (acc : Array Request) (css : String) :
    (nodeRequests false acc (.style css)).all (resolves resources svgChecked deckScript) = false := by
  simp [nodeRequests, resolves]

/-- The same context refusal holds for every script payload and MIME type,
including an otherwise admitted deck script or inert JSON data block. -/
theorem script_context_refused_exact (resources : Array Embedded) (svgChecked : Array ByteArray)
    (deckScript : String) (acc : Array Request) (attrs : Array (String × String)) (js : String) :
    (nodeRequests false acc (.script attrs js)).all
      (resolves resources svgChecked deckScript) = false := by
  simp [nodeRequests, resolves]

/-- Publication owns this checked tree. The constructor owes the computed
closure check, not a claim about a different tree or a sidecar manifest. -/
structure ClosedPage (deckScript : String) where
  lang : String
  head : Array Html.Node
  body : Array Html.Node
  resources : Array Embedded
  svgChecked : Array ByteArray
  closed : (requests head body).all (resolves resources svgChecked deckScript) = true

def ClosedPage.render (page : ClosedPage deckScript) : String :=
  Html.document page.lang page.head page.body

/-- A diagnostic names the reference, never an embedded payload. Long names
are bounded and quoting keeps control characters out of terminal output. -/
def referenceLabel (value : String) : String :=
  let shown := if value.toLower.startsWith "data:" then
      (value.takeWhile (· != ',')).toString ++ ",…"
    else value
  reprStr (if shown.length > 160 then (shown.take 160).toString ++ "…" else shown)

/-- The only successful construction path checks every projected request.
Unknown/remote/data-only claims all fail without matching captured evidence. -/
def close (resources : Array Embedded) (svgChecked : Array ByteArray)
    (deckScript lang : String) (head body : Array Html.Node) : Except String (ClosedPage deckScript) :=
  if h : (requests head body).all (resolves resources svgChecked deckScript) = true then
    .ok { lang, head, body, resources, svgChecked, closed := h }
  else
    let why := ((requests head body).find? fun r =>
      !resolves resources svgChecked deckScript r).map fun r => match r with
      | .url value => "HTML rendering URL " ++ referenceLabel value ++
          " has no embedded, validated resource"
      | .localFragment value =>
        let label := referenceLabel value
        "unsupported SVG fragment reference " ++ label
      | .script _ => "an HTML script is not the constant deck script"
      | .refused why => why
    .error (why.getD "the HTML resource closure check failed")

/-- Artifact-specific: successful checked emission covers the actual tree's
rendering projection. SVG readiness is exact-byte external-validator evidence;
this is not a kernel proof of XML parsing, decoding, or browser execution. -/
theorem close_covers (resources : Array Embedded) (svgChecked : Array ByteArray)
    (deckScript lang : String) (head body : Array Html.Node) {page : ClosedPage deckScript}
    (h : close resources svgChecked deckScript lang head body = .ok page) :
    page.render = Html.document lang head body ∧
      ∀ r ∈ requests head body, resolves resources svgChecked deckScript r = true := by
  unfold close at h
  split at h
  · next hc =>
    cases h
    refine ⟨rfl, ?_⟩
    intro r hr
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hr
    exact Array.all_eq_true.mp hc i hi
  · contradiction

end LeanTex.Core.HtmlResource
