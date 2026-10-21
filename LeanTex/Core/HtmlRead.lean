module

public import LeanTex.Core.HtmlEntity
public import LeanTex.Core.Hex

/-! An HTML page read as the HTML Standard's tokenizer and tree builder read it (§13.2), over the
subset this engine writes: the tree it builds where the builder acts as a stack of open elements,
and `none` wherever the standard would repair, reparent or imply an element. -/

namespace LeanTex.Core.HtmlRead

/-- A node of the document tree: text, or an element, its name and its attributes' names
lower-cased as the tokenizer reads them, before SVG's and MathML's case adjustment. -/
public inductive Dom where
  | text (s : String)
  | elem (tag : String) (attrs : Array (String × String)) (kids : Array Dom)
  deriving Inhabited, Repr, BEq

/-- The namespace an element is created in (§13.2.6.1). -/
public inductive Ns where
  | html
  | svg
  | math
  deriving DecidableEq, Repr, Inhabited

/-- A token the tokenizer emits (§13.2.5). -/
public inductive Tok where
  | char (c : Char)
  | start (name : String) (attrs : Array (String × String)) (selfClosing : Bool)
  | stop (name : String)
  | doctype
  deriving Inhabited, Repr

/-- An element open on the stack: its namespace, name, attributes and the children read so far. -/
public structure Frame where
  ns : Ns
  tag : String
  attrs : Array (String × String)
  kids : Array Dom
  deriving Inhabited

/-- A character inserted at the end of an element: appended to its last child when that is text,
else a new text child (§13.2.6.1, "insert a character"). -/
@[expose] public def addChar (kids : Array Dom) (c : Char) : Array Dom :=
  match kids.back? with
  | some (.text s) => kids.pop.push (.text (s.push c))
  | _ => kids.push (.text (String.singleton c))

/-- Characters inserted one by one. -/
@[expose] public def addText (kids : Array Dom) (s : String) : Array Dom :=
  s.toList.foldl addChar kids

/-- An element closed: its frame as a child of the frame below. -/
@[expose] public def Frame.close (f : Frame) : Dom := .elem f.tag f.attrs f.kids

/-- The document-level insertion modes this reading takes (§13.2.4.1); inside the body the
table modes are read off the stack. -/
public inductive Mode where
  | initial
  | beforeHtml
  | beforeHead
  | inHead
  | afterHead
  | inBody
  | afterBody
  | afterAfterBody
  deriving DecidableEq, Repr, Inhabited

/-- How the tokenizer reads an element's content after its start tag (§13.2.5). -/
public inductive Content where
  | data
  | rawtext
  | rcdata
  | script
  deriving DecidableEq, Repr, Inhabited

/-- The tree builder's state: its mode, the stack of open elements with the current node first,
and whether a line feed directly after the last start tag is dropped (`pre`, `listing`). -/
public structure Builder where
  mode : Mode
  stack : List Frame
  dropLF : Bool
  deriving Inhabited

/-! ### Element categories (§13.2.4.2, §13.2.6.5) -/

@[expose] public def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\x0C'

@[expose] public def isAlpha (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

@[expose] public def isAlnum (c : Char) : Bool := isAlpha c || ('0' ≤ c && c ≤ '9')

/-- A name lower-cased as the tokenizer lowers it, ASCII letters only. -/
@[expose] public def lower (s : String) : String := String.ofList (s.toList.map Char.toLower)

/-- HTML elements a start tag reads as void: no content, no end tag. -/
@[expose] public def voidTags : List String :=
  ["area", "base", "br", "col", "embed", "hr", "img", "input", "keygen", "link", "meta",
   "param", "source", "track", "wbr"]

/-- Start tags that close an open `p` in button scope before inserting (§13.2.6.4.7). -/
@[expose] public def closesP : List String :=
  ["address", "article", "aside", "blockquote", "center", "details", "dialog", "dir", "div", "dl",
   "fieldset", "figcaption", "figure", "footer", "header", "hgroup", "main", "menu", "nav", "ol",
   "p", "search", "section", "summary", "ul", "h1", "h2", "h3", "h4", "h5", "h6", "pre",
   "listing", "table", "hr", "li", "dd", "dt"]

@[expose] public def headings : List String := ["h1", "h2", "h3", "h4", "h5", "h6"]

/-- Formatting elements, pushed onto the list of active formatting elements. -/
@[expose] public def formatting : List String :=
  ["a", "b", "big", "code", "em", "font", "i", "nobr", "s", "small", "strike", "strong", "tt", "u"]

/-- HTML start tags this reading inserts in the body as ordinary elements (§13.2.6.4.7, "any
other start tag" and the categories above); any other HTML start tag is outside it. -/
@[expose] public def bodyTags : List String :=
  ["a", "abbr", "address", "article", "aside", "b", "bdi", "bdo", "blockquote", "br", "cite",
   "code", "data", "dd", "del", "details", "dfn", "div", "dl", "dt", "em", "figcaption",
   "figure", "footer", "h1", "h2", "h3", "h4", "h5", "h6", "header", "hgroup", "hr", "i", "img",
   "ins", "kbd", "label", "li", "main", "mark", "nav", "ol", "output", "p", "picture", "pre",
   "q", "s", "samp", "search", "section", "small", "source", "span", "strong", "sub", "summary",
   "sup", "table", "time", "u", "ul", "var", "wbr", "style", "script", "meta", "link"]

/-- Elements of the special category (§13.2.4.2), lower-cased, by namespace. -/
@[expose] public def special (ns : Ns) (t : String) : Bool :=
  match ns with
  | .html => ["address", "applet", "area", "article", "aside", "base", "basefont", "bgsound",
      "blockquote", "body", "br", "button", "caption", "center", "col", "colgroup", "dd",
      "details", "dir", "div", "dl", "dt", "embed", "fieldset", "figcaption", "figure", "footer",
      "form", "frame", "frameset", "h1", "h2", "h3", "h4", "h5", "h6", "head", "header", "hgroup",
      "hr", "html", "iframe", "img", "input", "keygen", "li", "link", "listing", "main",
      "marquee", "menu", "meta", "nav", "noembed", "noframes", "noscript", "object", "ol", "p",
      "param", "plaintext", "pre", "script", "search", "section", "select", "source", "style",
      "summary", "table", "tbody", "td", "template", "textarea", "tfoot", "th", "thead", "title",
      "tr", "track", "ul", "wbr", "xmp"].contains t
  | .math => ["mi", "mo", "mn", "ms", "mtext", "annotation-xml"].contains t
  | .svg => ["foreignobject", "desc", "title"].contains t

/-- The default scope's boundary elements (§13.2.4.2, "has an element in scope"). -/
@[expose] public def scopeBoundary (ns : Ns) (t : String) : Bool :=
  match ns with
  | .html => ["applet", "caption", "html", "table", "td", "th", "marquee", "object",
      "template"].contains t
  | .math => ["mi", "mo", "mn", "ms", "mtext", "annotation-xml"].contains t
  | .svg => ["foreignobject", "desc", "title"].contains t

/-- Whether an HTML element named `t` is open in button scope. -/
@[expose] public def inButtonScope (t : String) : List Frame → Bool
  | [] => false
  | f :: rest =>
    if f.ns == .html && f.tag == t then true
    else if scopeBoundary f.ns f.tag || (f.ns == .html && f.tag == "button") then false
    else inButtonScope t rest

/-- The `li`, `dd` and `dt` start-tag loop (§13.2.6.4.7): whether it would close an open element
named in `names` before stopping at a special element other than `address`, `div` or `p`. -/
@[expose] public def listItemCloses (names : List String) : List Frame → Bool
  | [] => false
  | f :: rest =>
    if f.ns == .html && names.contains f.tag then true
    else if special f.ns f.tag && !(f.ns == .html && ["address", "div", "p"].contains f.tag) then
      false
    else listItemCloses names rest

/-- Whether an `a` is open since the last marker, so the list of active formatting elements holds
one (§13.2.6.4.7, `a` start tag). -/
@[expose] public def openAnchor : List Frame → Bool
  | [] => false
  | f :: rest =>
    if f.ns == .html && f.tag == "a" then true
    else if f.ns == .html && ["td", "th", "caption", "applet", "marquee", "object",
        "template"].contains f.tag then false
    else openAnchor rest

/-- Whether a table cell is open above the nearest table: the builder is in the cell mode. -/
@[expose] public def inCell : List Frame → Bool
  | [] => false
  | f :: rest =>
    if f.ns == .html && (f.tag == "td" || f.tag == "th") then true
    else if f.ns == .html && f.tag == "table" then false
    else inCell rest

/-- Start tags the breakout rule of foreign content pops out of SVG and MathML for (§13.2.6.5). -/
@[expose] public def breakout : List String :=
  ["b", "big", "blockquote", "body", "br", "center", "code", "dd", "div", "dl", "dt", "em",
   "embed", "h1", "h2", "h3", "h4", "h5", "h6", "head", "hr", "i", "img", "li", "listing", "menu",
   "meta", "nobr", "ol", "p", "pre", "ruby", "s", "small", "span", "strong", "strike", "sub",
   "sup", "table", "tt", "u", "ul", "var"]

/-- Whether a foreign element is an integration point for HTML start tags and text: a MathML
text integration point or an HTML integration point (§13.2.6). -/
@[expose] public def integrationPoint (f : Frame) : Bool :=
  match f.ns with
  | .html => false
  | .math => ["mi", "mo", "mn", "ms", "mtext"].contains f.tag ||
      (f.tag == "annotation-xml" && f.attrs.any fun (k, v) =>
        k == "encoding" && (v.toLower == "text/html" || v.toLower == "application/xhtml+xml"))
  | .svg => ["foreignobject", "desc", "title"].contains f.tag

/-- Whether tokens at this stack read under the HTML rules rather than foreign content's. -/
@[expose] public def htmlContext : List Frame → Bool
  | [] => true
  | f :: _ => f.ns == .html || integrationPoint f

/-! ### The tree builder -/

/-- The content a start tag's element is read with, in the HTML namespace. -/
@[expose] public def contentOf (ns : Ns) (name : String) : Content :=
  if ns != .html then .data
  else if name == "style" then .rawtext
  else if name == "script" then .script
  else if name == "title" || name == "textarea" then .rcdata
  else .data

/-- Whether the current node is an HTML element named in `names`. -/
@[expose] public def currentIs (names : List String) : List Frame → Bool
  | f :: _ => f.ns == .html && names.contains f.tag
  | [] => false

/-- Whether the current node is an element whose content the tokenizer reads as text. -/
@[expose] public def inText (stack : List Frame) : Bool :=
  currentIs ["title", "style", "script", "textarea"] stack

/-- Whether the current node puts the builder in a table mode, where only whitespace text and
the table's parts are read. -/
@[expose] public def inTableMode (stack : List Frame) : Bool :=
  currentIs ["table", "colgroup", "thead", "tbody", "tfoot", "tr"] stack

/-- A start tag in the table modes that this reading inserts: the table's own parts at their
places, and style and script through the head rules but in a column group, which they close. -/
@[expose] public def tablePartOk (stack : List Frame) (name : String) : Bool :=
  let headRule := name == "style" || name == "script"
  if currentIs ["table"] stack then
    headRule || ["caption", "colgroup", "thead", "tbody", "tfoot"].contains name
  else if currentIs ["colgroup"] stack then name == "col"
  else if currentIs ["thead", "tbody", "tfoot"] stack then headRule || name == "tr"
  else if currentIs ["tr"] stack then headRule || name == "td" || name == "th"
  else false

/-- Whether an HTML start tag in the body's modes inserts its element where the standard does,
unrepaired: no `p` closed, no heading popped, no list item or anchor closed, no table part out of
place, no element the body's rules leave out. -/
@[expose] public def bodyAccepts (s : List Frame) (name : String) : Bool :=
  if inTableMode s then tablePartOk s name
  else if inCell s && ["caption", "col", "colgroup", "tbody", "td", "tfoot", "th", "thead",
      "tr"].contains name then false
  else if name == "svg" || name == "math" then true
  else bodyTags.contains name &&
    !(closesP.contains name && inButtonScope "p" s) &&
    !(headings.contains name && currentIs headings s) &&
    !(name == "li" && listItemCloses ["li"] s) &&
    !((name == "dd" || name == "dt") && listItemCloses ["dd", "dt"] s) &&
    !(name == "a" && openAnchor s)

/-- Whether a start tag in foreign content inserts an element rather than breaking out. -/
@[expose] public def foreignAccepts (name : String) (attrs : Array (String × String)) : Bool :=
  !(breakout.contains name || (name == "font" && attrs.any fun (k, _) =>
    k == "color" || k == "face" || k == "size"))

/-- The namespace a start tag's element is created in: SVG and MathML roots open their
namespace, foreign content keeps its own, the HTML rules make HTML elements. -/
@[expose] public def nsFor (s : List Frame) (name : String) : Ns :=
  if htmlContext s then
    if name == "svg" then .svg else if name == "math" then .math else .html
  else match s with
    | f :: _ => f.ns
    | [] => .html

/-- Start tags whose dispatch this reading leaves out (§13.2.6): `svg` under a MathML
`annotation-xml` that is no integration point, which the HTML rules take, and `mglyph` or
`malignmark` under a MathML text integration point, which foreign content takes. -/
@[expose] public def dispatchOdd (s : List Frame) (name : String) : Bool :=
  match s with
  | f :: _ =>
    (f.ns == .math && f.tag == "annotation-xml" && !integrationPoint f && name == "svg") ||
      (f.ns == .math && ["mi", "mo", "mn", "ms", "mtext"].contains f.tag &&
        (name == "mglyph" || name == "malignmark"))
  | [] => false

/-- Whether a start tag in the body's modes is read as this reading reads it. -/
@[expose] public def startAccepts (s : List Frame) (name : String)
    (attrs : Array (String × String)) : Bool :=
  !dispatchOdd s name && if htmlContext s then bodyAccepts s name else foreignAccepts name attrs

/-- Whether an element is void as read: HTML void elements, or a self-closed foreign one. -/
@[expose] public def voidAs (ns : Ns) (name : String) (selfClosing : Bool) : Bool :=
  if ns == .html then voidTags.contains name else selfClosing

/-- An element inserted at the current node: pushed, or closed at once when void. -/
@[expose] public def insert (b : Builder) (ns : Ns) (name : String)
    (attrs : Array (String × String)) (void : Bool) : Option Builder :=
  let f : Frame := { ns, tag := name, attrs, kids := #[] }
  if void then
    match b.stack with
    | p :: rest => some { b with stack := { p with kids := p.kids.push f.close } :: rest }
    | [] => none
  else some { b with stack := f :: b.stack }

/-- A character inserted at the current node. -/
@[expose] public def insertChar (b : Builder) (c : Char) : Option Builder :=
  match b.stack with
  | p :: rest => some { b with stack := { p with kids := addChar p.kids c } :: rest }
  | [] => none

/-- The current node closed by its own end tag; any other end tag is outside this reading. -/
@[expose] public def closeCurrent (b : Builder) (name : String) : Option Builder :=
  match b.stack with
  | f :: p :: rest =>
    if f.tag == name then some { b with stack := { p with kids := p.kids.push f.close } :: rest }
    else none
  | _ => none

/-- Head elements this reading inserts: metadata as void, a title, style sheet or script with
its text. -/
@[expose] public def headTags : List String := ["meta", "link", "base", "title", "style", "script"]

/-- A start tag: inserted per the mode, with the content its element is read with; the body's
`pre` and `listing` drop a line feed that follows at once. -/
@[expose] public def start (b : Builder) (name : String) (attrs : Array (String × String))
    (selfClosing : Bool) : Option (Builder × Content) :=
  match b.mode with
  | .beforeHtml => if name == "html" then
      some ({ b with mode := .beforeHead, stack := [{ ns := .html, tag := name, attrs, kids := #[] }] },
        .data)
    else none
  | .beforeHead => if name == "head" then
      (insert b .html name attrs false).map fun b => ({ b with mode := .inHead }, .data)
    else none
  | .inHead =>
    if headTags.contains name then
      (insert b .html name attrs (voidTags.contains name)).map (·, contentOf .html name)
    else none
  | .afterHead => if name == "body" then
      (insert b .html name attrs false).map fun b => ({ b with mode := .inBody }, .data)
    else none
  | .inBody =>
    if startAccepts b.stack name attrs then
      let ns := nsFor b.stack name
      (insert b ns name attrs (voidAs ns name selfClosing)).map fun b' =>
        ({ b' with dropLF := ns == .html && (name == "pre" || name == "listing") },
          contentOf ns name)
    else none
  | _ => none

/-- An end tag: the current node closed, `head` leaving for the after-head mode, `body` and `html`
moving to the after-body modes with the body still open (§13.2.6.4.7). -/
@[expose] public def stop (b : Builder) (name : String) : Option Builder :=
  match b.mode with
  | .inHead => if name == "head" then
      (closeCurrent b name).map fun b => { b with mode := .afterHead }
    else closeCurrent b name
  | .inBody =>
    if name == "body" then
      if currentIs ["body"] b.stack then some { b with mode := .afterBody } else none
    else closeCurrent b name
  | .afterBody => if name == "html" then some { b with mode := .afterAfterBody } else none
  | _ => none

/-- Whether a mode past the document's start keeps a character at this stack: a text element's
content, whitespace, and in the body any text but a null, only whitespace in a table mode. -/
@[expose] public def charKeeps (m : Mode) (s : List Frame) (c : Char) : Bool :=
  inText s || isWs c || (m == .inBody && c != '\x00' && !inTableMode s)

/-- A character token: ignored as whitespace before the head, else inserted where its mode keeps
it. -/
@[expose] public def char (b : Builder) (c : Char) : Option Builder :=
  match b.mode with
  | .initial | .beforeHtml | .beforeHead => if isWs c then some b else none
  | m => if charKeeps m b.stack c then insertChar b c else none

/-- One token through the builder, with the content the tokenizer reads next; a `pre`'s dropped
line feed applies only to the token right after its start tag. -/
@[expose] public def build (b : Builder) : Tok → Option (Builder × Content)
  | .doctype => if b.mode == .initial then some ({ b with mode := .beforeHtml }, .data) else none
  | .start name attrs sc => start { b with dropLF := false } name attrs sc
  | .stop name => (stop { b with dropLF := false } name).map (·, .data)
  | .char c =>
    if b.dropLF && c == '\n' then some ({ b with dropLF := false }, .data)
    else (char { b with dropLF := false } c).map (·, .data)

/-! ### The tokenizer -/

/-- A tag being tokenized: whether it is an end tag, its name, its attributes, and the attribute
being read. -/
public structure TagTok where
  isEnd : Bool
  name : String
  attrs : Array (String × String)
  deriving Inhabited

/-- Where a character reference returns to (§13.2.5.72). -/
public inductive RefRet where
  | data
  | rcdata (name : String)
  | attr (t : TagTok) (key value : String)
  deriving Inhabited

/-- The tokenizer's states this reading takes (§13.2.5); `raw` covers RAWTEXT, RCDATA and script
data, `name` its element's name for the appropriate end tag. -/
public inductive TState where
  | data
  | tagOpen
  | endTagOpen
  | tagName (t : TagTok)
  | beforeAttrName (t : TagTok)
  | attrName (t : TagTok) (key : String)
  | afterAttrName (t : TagTok) (key : String)
  | beforeAttrValue (t : TagTok) (key : String)
  | attrValue (t : TagTok) (key value : String)
  | afterAttrValue (t : TagTok)
  | selfClosing (t : TagTok)
  | markup (seen : List Char)
  | ref (ret : RefRet) (name : List Char)
  | numRef (ret : RefRet) (hex : Bool) (digits : List Char)
  | raw (kind : Content) (name : String)
  | rawLt (kind : Content) (name : String)
  | rawEnd (kind : Content) (name : String) (seen : String)
  deriving Inhabited

/-- The tokenizer and builder together, or the absence a step outside this reading leaves. -/
public structure St where
  tok : TState
  build : Builder
  deriving Inhabited

/-- A token emitted: built, and the tokenizer set to the content its builder asks. -/
@[expose] public def emit (s : St) (t : Tok) (next : TState) : Option St :=
  (HtmlRead.build s.build t).map fun (b, c) =>
    { tok := match c with
        | .data => next
        | k => .raw k (match t with | .start n _ _ => n | _ => ""),
      build := b }

/-- Several character tokens in order. -/
@[expose] public def emitChars (s : St) (cs : List Char) (next : TState) : Option St :=
  match cs with
  | [] => some { s with tok := next }
  | c :: rest => (emit s (.char c) next).bind fun s => emitChars s rest next

/-- The characters a named reference stands for: the five every markup language predefines read
directly, any other through the HTML Standard's table (§13.5). -/
@[expose] public def named (name : String) : Option String :=
  if name == "amp" then some "&" else if name == "lt" then some "<"
  else if name == "gt" then some ">" else if name == "quot" then some "\""
  else if name == "apos" then some "'" else HtmlEntity.lookup name

/-- The character a numeric reference stands for (§13.2.5.80): none, null, surrogates and code
points past Unicode as U+FFFD, the C1 range outside this reading. -/
@[expose] public def numeric (n : Nat) : Option Char :=
  if n == 0 || n > 0x10FFFF || (0xD800 ≤ n && n ≤ 0xDFFF) then some '�'
  else if 0x80 ≤ n && n ≤ 0x9F then none
  else some (Char.ofNat n)

/-- A digit's value in a numeric reference, hexadecimal or decimal. -/
@[expose] public def digitVal (hex : Bool) (c : Char) : Option Nat :=
  if hex then Hex.digit? c else if c.isDigit then some (c.toNat - 48) else none

@[expose] public def digitsValue (hex : Bool) (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * (if hex then 16 else 10) + (digitVal hex c).getD 0) 0

/-- A reference's characters delivered where it returns. -/
@[expose] public def deliver (s : St) (ret : RefRet) (cs : String) : Option St :=
  match ret with
  | .data => emitChars s cs.toList .data
  | .rcdata n => emitChars s cs.toList (.raw .rcdata n)
  | .attr t k v => some { s with tok := .attrValue t k (v ++ cs) }

/-- A finished tag token emitted. -/
@[expose] public def emitTag (s : St) (t : TagTok) (selfClosing : Bool) : Option St :=
  if t.isEnd then
    if t.attrs.isEmpty && !selfClosing then emit s (.stop t.name) .data else none
  else emit s (.start t.name t.attrs selfClosing) .data

/-- An attribute finished: kept unless its name repeats, as the standard drops a repeat. -/
@[expose] public def TagTok.add (t : TagTok) (key value : String) : TagTok :=
  if t.attrs.any (·.1 == key) then t else { t with attrs := t.attrs.push (key, value) }

/-- The text a raw element's partial end tag stands for when it ends no tag, as written. -/
@[expose] public def rawBack (seen : String) : List Char := '<' :: '/' :: seen.toList

/-- One character through the tokenizer (§13.2.5), the builder taking each token it emits. -/
@[expose] public def step (s : St) (c : Char) : Option St :=
  match s.tok with
  | .data =>
    if c == '<' then some { s with tok := .tagOpen }
    else if c == '&' then some { s with tok := .ref .data [] }
    else emit s (.char c) .data
  | .tagOpen =>
    if c == '/' then some { s with tok := .endTagOpen }
    else if c == '!' then some { s with tok := .markup [] }
    else if isAlpha c then some { s with tok := .tagName ⟨false, String.singleton c.toLower, #[]⟩ }
    else none
  | .endTagOpen =>
    if isAlpha c then some { s with tok := .tagName ⟨true, String.singleton c.toLower, #[]⟩ }
    else none
  | .tagName t =>
    if isWs c then some { s with tok := .beforeAttrName t }
    else if c == '/' then some { s with tok := .selfClosing t }
    else if c == '>' then emitTag s t false
    else if c == '\x00' then none
    else some { s with tok := .tagName { t with name := t.name.push c.toLower } }
  | .beforeAttrName t =>
    if isWs c then some s
    else if c == '/' then some { s with tok := .selfClosing t }
    else if c == '>' then emitTag s t false
    else if c == '=' || c == '"' || c == '\'' || c == '<' || c == '\x00' then none
    else some { s with tok := .attrName t (String.singleton c.toLower) }
  | .attrName t k =>
    if isWs c then some { s with tok := .afterAttrName t k }
    else if c == '/' then some { s with tok := .selfClosing (t.add k "") }
    else if c == '>' then emitTag s (t.add k "") false
    else if c == '=' then some { s with tok := .beforeAttrValue t k }
    else if c == '"' || c == '\'' || c == '<' || c == '\x00' then none
    else some { s with tok := .attrName t (k.push c.toLower) }
  | .afterAttrName t k =>
    if isWs c then some s
    else if c == '/' then some { s with tok := .selfClosing (t.add k "") }
    else if c == '=' then some { s with tok := .beforeAttrValue t k }
    else if c == '>' then emitTag s (t.add k "") false
    else if c == '"' || c == '\'' || c == '<' || c == '\x00' then none
    else some { s with tok := .attrName (t.add k "") (String.singleton c.toLower) }
  | .beforeAttrValue t k =>
    if isWs c then some s
    else if c == '"' then some { s with tok := .attrValue t k "" }
    else none
  | .attrValue t k v =>
    if c == '"' then some { s with tok := .afterAttrValue (t.add k v) }
    else if c == '&' then some { s with tok := .ref (.attr t k v) [] }
    else if c == '\x00' then none
    else some { s with tok := .attrValue t k (v.push c) }
  | .afterAttrValue t =>
    if isWs c then some { s with tok := .beforeAttrName t }
    else if c == '/' then some { s with tok := .selfClosing t }
    else if c == '>' then emitTag s t false
    else none
  | .selfClosing t => if c == '>' then emitTag s t true else none
  | .markup seen =>
    let seen := seen ++ [c.toLower]
    if seen == "doctype html>".toList then emit s .doctype .data
    else if seen.isPrefixOf "doctype html>".toList then some { s with tok := .markup seen }
    else none
  | .ref ret name =>
    if name.isEmpty && c == '#' then some { s with tok := .numRef ret false [] }
    else if isAlnum c then some { s with tok := .ref ret (name ++ [c]) }
    else if c == ';' && !name.isEmpty then
      (named (String.ofList name)).bind (deliver s ret)
    else if name.isEmpty then
      (match ret with
        | .data => emit s (.char '&') .data
        | .rcdata n => emit s (.char '&') (.raw .rcdata n)
        | .attr t k v => some { s with tok := .attrValue t k (v.push '&') }).bind
        fun s => step' s c
    else none
  | .numRef ret hex ds =>
    if ds.isEmpty && !hex && (c == 'x' || c == 'X') then some { s with tok := .numRef ret true [] }
    else if (digitVal hex c).isSome then some { s with tok := .numRef ret hex (ds ++ [c]) }
    else if c == ';' && !ds.isEmpty then
      (numeric (digitsValue hex ds)).bind fun ch => deliver s ret (String.singleton ch)
    else none
  | .raw k n =>
    if c == '<' then some { s with tok := .rawLt k n }
    else if c == '&' && k == .rcdata then some { s with tok := .ref (.rcdata n) [] }
    else if c == '\x00' then none
    else emit s (.char c) (.raw k n)
  | .rawLt k n =>
    if c == '/' then some { s with tok := .rawEnd k n "" }
    else if c == '!' && k == .script then none
    else ((emit s (.char '<') (.raw k n)).bind fun s => step' s c)
  | .rawEnd k n seen =>
    if isAlpha c then some { s with tok := .rawEnd k n (seen.push c) }
    else if lower seen == n && c == '>' then emit s (.stop n) .data
    else if lower seen == n && (isWs c || c == '/') then none
    else (emitChars s (rawBack seen) (.raw k n)).bind fun s => step' s c
where
  /-- The reconsumed character in the states it returns to, which never reconsume again. -/
  step' (s : St) (c : Char) : Option St :=
    match s.tok with
    | .data =>
      if c == '<' then some { s with tok := .tagOpen }
      else if c == '&' then some { s with tok := .ref .data [] }
      else emit s (.char c) .data
    | .raw k n =>
      if c == '<' then some { s with tok := .rawLt k n }
      else if c == '&' && k == .rcdata then some { s with tok := .ref (.rcdata n) [] }
      else if c == '\x00' then none
      else emit s (.char c) (.raw k n)
    | .attrValue t k v =>
      if c == '"' then some { s with tok := .afterAttrValue (t.add k v) }
      else if c == '&' then some { s with tok := .ref (.attr t k v) [] }
      else if c == '\x00' then none
      else some { s with tok := .attrValue t k (v.push c) }
    | _ => none

/-- The state before the first character. -/
@[expose] public def init : St := { tok := .data, build := { mode := .initial, stack := [], dropLF := false } }

/-- The end of input (§13.2.6.5, "stop parsing"): the document read when it ends after its `html`
end tag, its body still open. -/
@[expose] public def finish (s : St) : Option Dom :=
  match s.tok, s.build.mode, s.build.stack with
  | .data, .afterAfterBody, [body, html] =>
    some (Frame.close { html with kids := html.kids.push body.close })
  | _, _, _ => none

/-- The document tree the HTML Standard's parser builds from a page's characters, where this
reading covers it; a carriage return, which input preprocessing normalizes, is outside it. -/
public def parse (page : String) : Option Dom :=
  let cs := page.toList
  if cs.contains '\r' then none
  else (cs.foldl (fun s c => s.bind (step · c)) (some init)).bind finish

/-! ### Page text -/

mutual

/-- The text of a node and its descendants in document order after `acc`, leaving out style
sheets and scripts. -/
public def Dom.charsInto (acc : String) : Dom → String
  | .text s => acc ++ s
  | .elem tag _ kids =>
    if tag == "style" || tag == "script" then acc else Dom.charsListInto acc kids.toList

public def Dom.charsListInto (acc : String) : List Dom → String
  | [] => acc
  | d :: rest => Dom.charsListInto (Dom.charsInto acc d) rest

end

/-- The text of a node and its descendants, leaving out style sheets and scripts. -/
public def Dom.chars (d : Dom) : String := d.charsInto ""

/-- The text of nodes in order, leaving out style sheets and scripts. -/
public def Dom.charsList (l : List Dom) : String := Dom.charsListInto "" l

/-- The page's text: what the body's text nodes hold, in order, outside style sheets and scripts,
shown or hidden. -/
public def Dom.bodyText : Dom → Option String
  | .elem "html" _ kids => (kids.toList.find? fun d => match d with
      | .elem "body" _ _ => true
      | .elem .. | .text _ => false).map Dom.chars
  | .elem .. | .text _ => none

/-- The text a page's body holds, read from its characters. -/
public def pageText (page : String) : Option String := (parse page).bind Dom.bodyText

end LeanTex.Core.HtmlRead
