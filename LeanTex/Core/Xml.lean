module

import LeanTex.Core.WhatwgEncoding
import Std.Data.HashSet

/-! A total reader and canonical writer of the XML 1.0 an SVG file is written in; what could
bring meaning from outside the file is refused. -/

namespace LeanTex.Core.Xml

/-- A parsed node: an element with its name as spelled, its attributes in source order and its
children, or character data. -/
public inductive Node where
  | elem (name : String) (attrs : Array (String × String)) (kids : Array Node)
  | text (s : String)
  deriving Repr, Inhabited, BEq

/-- Why bytes are no document this reader accepts: a syntax error at a byte offset, or a refused construct. -/
public inductive Refusal where
  | syntax (pos : Nat) (what : String)
  | declaration (what : String)
  | entity (name : String)
  | instruction (target : String)
  | encoding (name : String)
  | budget (what : String)
  deriving Repr, BEq, Inhabited

/-- The work one document may ask of the reader; the depth, name and text limits are libxml2's defaults. -/
public structure Budget where
  bytes : Nat
  depth : Nat
  nodes : Nat
  name : Nat
  text : Nat
  deriving Repr, Inhabited

@[expose] public def Budget.standard : Budget :=
  { bytes := 256 * 1024 * 1024, depth := 256, nodes := 16000000, name := 50000,
    text := 10000000 }

/-- The byte at `i`, or 256 past the end: one sentinel no byte equals. -/
@[expose] public def at? (b : ByteArray) (i : Nat) : Nat :=
  (b[i]?.map (·.toNat)).getD 256

/-- XML white space (§2.3, production 3). -/
@[expose] public def isSpace (c : Nat) : Bool := c == 32 || c == 9 || c == 10 || c == 13

/-- A byte that may start a name: an ASCII letter, `_`, `:`, or any byte of
a multi-byte character. -/
@[expose] public def nameStart (c : Nat) : Bool :=
  (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95 || c == 58 || (128 ≤ c && c < 256)

/-- A byte that may continue a name: a start byte, a digit, `-`, `.`. -/
@[expose] public def nameByte (c : Nat) : Bool :=
  nameStart c || (48 ≤ c && c ≤ 57) || c == 45 || c == 46

/-- Does the ASCII string `s` stand at `i`? -/
public def bytesAt (b : ByteArray) (i : Nat) (s : String) : Bool :=
  let t := s.toUTF8
  i + t.size ≤ b.size && (Id.run do
    let mut ok := true
    for k in [0:t.size] do
      if at? b (i + k) != at? t k then
        ok := false
        break
    return ok)

/-- The UTF-8 text of `b[i:j]`, empty when that is no UTF-8. -/
public def slice (b : ByteArray) (i j : Nat) : String :=
  (String.fromUTF8? (b.extract i j)).getD ""

/-- A Unicode scalar XML admits in a document (§2.2, production 2). -/
@[expose] public def xmlChar (n : Nat) : Bool :=
  n == 9 || n == 10 || n == 13 || (32 ≤ n && n ≤ 0xD7FF) || (0xE000 ≤ n && n ≤ 0xFFFD) ||
    (0x10000 ≤ n && n ≤ 0x10FFFF)

/-- The first byte offset holding a character XML does not admit, or `none`. -/
public def badCharAt (b : ByteArray) : Option Nat := Id.run do
  for h : i in [0:b.size] do
    let c := b[i].toNat
    if c < 32 && c != 9 && c != 10 && c != 13 then return some i
    if c == 0xEF && at? b (i + 1) == 0xBF && (at? b (i + 2) == 0xBE || at? b (i + 2) == 0xBF) then
      return some i
  return none

/-- The end of the run of `pred` bytes starting at `i`. -/
public def scanWhile (b : ByteArray) (pred : Nat → Bool) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [0:b.size + 1] do
    if pred (at? b j) then j := j + 1 else break
  return j

@[expose] public def skipSpace (b : ByteArray) (i : Nat) : Nat := scanWhile b isSpace i

/-- The first offset at or after `i` where the ASCII string `s` stands, if any. -/
public def find (b : ByteArray) (i : Nat) (s : String) : Option Nat := Id.run do
  let first := at? s.toUTF8 0
  let mut j := i
  for _ in [0:b.size + 1] do
    if j ≥ b.size then return none
    if at? b j == first && bytesAt b j s then return some j
    j := j + 1
  return none

private def declValue (decl : String) (key : String) : Option String :=
  match decl.splitOn key with
  | [_] | [] => none
  | _ :: rest :: _ =>
    let t := (rest.dropWhile fun c => c == ' ' || c == '=' || c == '\t' || c == '\n').toString
    match t.toList with
    | q :: more =>
      if q == '"' || q == '\'' then some (String.ofList (more.takeWhile (· != q))) else none
    | [] => none

private def afterDeclaration (u : ByteArray) (start : Nat) : Except Refusal (ByteArray × Nat) := do
  if !(bytesAt u start "<?xml" && isSpace (at? u (start + 5))) then return (u, start)
  let some close := find u start "?>" | throw (.syntax start "unterminated XML declaration")
  return (u, close + 2)

private def fromUtf16 (be : Bool) (b : ByteArray) (start : Nat) : Except Refusal (ByteArray × Nat) := do
  match WhatwgEncoding.decodeUtf16 be b start with
  | .ok u => afterDeclaration u 0
  | .error i => throw (.syntax i "a UTF-16 code unit that is no character")

/-- The input as UTF-8 and where its content begins (XML 1.0 §4.3.3 and Appendix F, read through
the WHATWG Encoding Standard). -/
public def decode (b : ByteArray) : Except Refusal (ByteArray × Nat) := do
  let b0 := at? b 0
  let b1 := at? b 1
  let b2 := at? b 2
  let b3 := at? b 3
  if (b0 == 0 && b1 == 0 && (b2 == 0xFE && b3 == 0xFF || b2 == 0 && b3 == 0x3C)) ||
      (b0 == 0xFF && b1 == 0xFE && b2 == 0 && b3 == 0) || (b0 == 0x3C && b1 == 0 && b2 == 0 && b3 == 0) then
    throw (.encoding "UTF-32")
  if b0 == 0xEF && b1 == 0xBB && b2 == 0xBF then return ← afterDeclaration b 3
  if b0 == 0xFE && b1 == 0xFF then return ← fromUtf16 true b 2
  if b0 == 0xFF && b1 == 0xFE then return ← fromUtf16 false b 2
  if b0 == 0 && b1 == 0x3C && b2 == 0 && b3 == 0x3F then return ← fromUtf16 true b 0
  if b0 == 0x3C && b1 == 0 && b2 == 0x3F && b3 == 0 then return ← fromUtf16 false b 0
  if !(bytesAt b 0 "<?xml" && isSpace (at? b 5)) then return (b, 0)
  let some close := find b 0 "?>" | throw (.syntax 0 "unterminated XML declaration")
  let after := close + 2
  match declValue (slice b 5 close) "encoding" with
  | none => return (b, after)
  | some label =>
    match WhatwgEncoding.lookup label with
    | none => throw (.encoding label)
    | some "UTF-8" | some "UTF-16LE" | some "UTF-16BE" => return (b, after)
    | some "x-user-defined" => return (b.extract 0 after ++ WhatwgEncoding.decodeUserDefined b after, after)
    | some name =>
      match WhatwgEncoding.singleByteIndex? name with
      | none => throw (.encoding name)
      | some idx =>
        match WhatwgEncoding.decodeSingle (WhatwgEncoding.scalarsOf idx) b after with
        | .ok body => return (b.extract 0 after ++ body, after)
        | .error i => throw (.syntax i s!"a byte {name} does not map")

/-- A name at `i`: its text and where it ends. -/
public def readName (bud : Budget) (b : ByteArray) (i : Nat) : Except Refusal (String × Nat) := do
  unless nameStart (at? b i) do throw (.syntax i "a name was expected")
  let j := scanWhile b nameByte i
  if j - i > bud.name then throw (.budget "name length")
  return (slice b i j, j)

@[expose] public def hexVal (c : Nat) : Option Nat :=
  if 48 ≤ c && c ≤ 57 then some (c - 48)
  else if 97 ≤ c && c ≤ 102 then some (c - 87)
  else if 65 ≤ c && c ≤ 70 then some (c - 55)
  else none

/-- A character or entity reference at `i`, with its end; only the predefined entities are read (§4.6). -/
public def readReference (b : ByteArray) (i : Nat) : Except Refusal (Char × Nat) := do
  if at? b (i + 1) == 35 then
    let hex := at? b (i + 2) == 120
    let d0 := if hex then i + 3 else i + 2
    let j := scanWhile b (fun c => if hex then (hexVal c).isSome else 48 ≤ c && c ≤ 57) d0
    if j == d0 || at? b j != 59 then throw (.syntax i "a malformed character reference")
    if j - d0 > 8 then throw (.syntax i "a character reference out of range")
    let v := Id.run do
      let mut v := 0
      for k in [d0:j] do
        v := v * (if hex then 16 else 10) + ((hexVal (at? b k)).getD 0)
      return v
    unless xmlChar v do throw (.syntax i "a character reference to a character XML does not admit")
    return (Char.ofNat v, j + 1)
  else
    let (name, j) ← readName Budget.standard b (i + 1)
    if at? b j != 59 then throw (.syntax i "an entity reference without ';'")
    let c ← match name with
      | "lt" => pure '<'
      | "gt" => pure '>'
      | "amp" => pure '&'
      | "quot" => pure '"'
      | "apos" => pure '\''
      | other => throw (.entity other)
    return (c, j + 1)

/-- An attribute value at `i` with references replaced and white space normalized (§3.3.3), and its end. -/
public def readValue (bud : Budget) (b : ByteArray) (i : Nat) : Except Refusal (String × Nat) := do
  let q := at? b i
  unless q == 34 || q == 39 do throw (.syntax i "an attribute value must be quoted")
  let mut out := ""
  let mut j := i + 1
  for _ in [0:b.size + 1] do
    let c := at? b j
    if c == q then break
    if c == 256 then throw (.syntax i "an unterminated attribute value")
    if c == 60 then throw (.syntax j "'<' in an attribute value")
    if c == 38 then
      let (ch, k) ← readReference b j
      out := out.push ch
      j := k
    else if c == 13 then
      out := out.push ' '
      j := if at? b (j + 1) == 10 then j + 2 else j + 1
    else if c == 9 || c == 10 then
      out := out.push ' '
      j := j + 1
    else
      let k := scanWhile b (fun d => d != q && d != 256 && d != 60 && d != 38 && !isSpace d) j
      let k := if k == j then j + 1 else k
      out := out ++ slice b j k
      j := k
    if out.utf8ByteSize > bud.text then throw (.budget "attribute length")
  if at? b j != q then throw (.syntax i "an unterminated attribute value")
  return (out, j + 1)

/-- Bytes as text with each CR LF or lone CR read as one line feed (§2.11). -/
public def normalizeEol (raw : ByteArray) : String :=
    if (raw.data.contains 13) then
      let out := Id.run do
        let mut out := ByteArray.emptyWithCapacity raw.size
        let mut k := 0
        for _ in [0:raw.size + 1] do
          if k ≥ raw.size then break
          let c := at? raw k
          if c == 13 then
            out := out.push 10
            k := if at? raw (k + 1) == 10 then k + 2 else k + 1
          else
            out := out.push (at? raw k).toUInt8
            k := k + 1
        return out
      (String.fromUTF8? out).getD ""
    else (String.fromUTF8? raw).getD ""

/-- Character data from `i` to the next markup or reference, end-of-line normalized (§2.11). -/
public def readChars (b : ByteArray) (i : Nat) : Except Refusal (String × Nat) := do
  let j := scanWhile b (fun c => c != 60 && c != 38 && c != 256) i
  let raw := b.extract i j
  if (find raw 0 "]]>").isSome then throw (.syntax i "']]>' in character data")
  return (normalizeEol raw, j)

/-- The end of a comment at `i`; `--` may stand only in its closing `-->` (§2.5). -/
public def skipComment (b : ByteArray) (i : Nat) : Except Refusal Nat := do
  let some j := find b (i + 4) "--" | throw (.syntax i "an unterminated comment")
  if at? b (j + 2) != 62 then throw (.syntax j "'--' inside a comment")
  return j + 3

/-- A start tag at `i`: its name, its attributes, whether it closes itself, and its end. -/
public def readStartTag (bud : Budget) (b : ByteArray) (i : Nat) :
    Except Refusal (String × Array (String × String) × Bool × Nat) := do
  let (name, j0) ← readName bud b (i + 1)
  let mut attrs : Array (String × String) := #[]
  -- A set, so a tag of many attributes reads in linear time.
  let mut seen : Std.HashSet String := {}
  let mut j := j0
  for _ in [0:b.size + 1] do
    let k := skipSpace b j
    let c := at? b k
    if c == 62 then return (name, attrs, false, k + 1)
    if c == 47 then
      if at? b (k + 1) == 62 then return (name, attrs, true, k + 2)
      throw (.syntax k "'/' not followed by '>' in a tag")
    if k == j then throw (.syntax k "attributes must be separated by white space")
    let (an, k1) ← readName bud b k
    let k2 := skipSpace b k1
    if at? b k2 != 61 then throw (.syntax k2 "an attribute without '='")
    let (v, k3) ← readValue bud b (skipSpace b (k2 + 1))
    if seen.contains an then throw (.syntax k s!"the attribute '{an}' is named twice")
    seen := seen.insert an
    attrs := attrs.push (an, v)
    j := k3
  throw (.syntax i "an unterminated tag")

private def skipLiteral (b : ByteArray) (i : Nat) : Except Refusal Nat := do
  let q := at? b i
  unless q == 34 || q == 39 do throw (.syntax i "a quoted literal was expected")
  let j := scanWhile b (fun c => c != q && c != 256) (i + 1)
  if at? b j != q then throw (.syntax i "an unterminated literal")
  return j + 1

/-- The end of a document type declaration at `i`; a declaration in an internal subset is refused (§2.8). -/
public def skipDoctype (bud : Budget) (b : ByteArray) (i : Nat) : Except Refusal Nat := do
  let j0 := i + 9
  unless isSpace (at? b j0) do throw (.syntax j0 "white space after <!DOCTYPE was expected")
  let (_, j1) ← readName bud b (skipSpace b j0)
  let mut j := skipSpace b j1
  if bytesAt b j "SYSTEM" then
    j ← skipLiteral b (skipSpace b (j + 6))
  else if bytesAt b j "PUBLIC" then
    let k ← skipLiteral b (skipSpace b (j + 6))
    j ← skipLiteral b (skipSpace b k)
  j := skipSpace b j
  if at? b j == 91 then
    j := j + 1
    for _ in [0:b.size + 1] do
      j := skipSpace b j
      let c := at? b j
      if c == 93 then break
      if c == 37 then throw (.declaration "a parameter-entity reference")
      if bytesAt b j "<!--" then
        j ← skipComment b j
      else if bytesAt b j "<!" then
        let (kind, _) ← readName bud b (j + 2)
        throw (.declaration s!"an {kind} declaration")
      else if bytesAt b j "<?" then
        let (target, _) ← readName bud b (j + 2)
        throw (.instruction target)
      else throw (.syntax j "an unreadable internal subset")
    if at? b j != 93 then throw (.syntax i "an unterminated internal subset")
    j := skipSpace b (j + 1)
  if at? b j != 62 then throw (.syntax j "an unterminated document type declaration")
  return j + 1

/-- An element still open: its name, attributes, finished children, and the
character data read since the last child. -/
public structure Frame where
  name : String
  attrs : Array (String × String)
  kids : Array Node
  text : String
  deriving Inhabited

@[expose] public def Frame.flush (f : Frame) : Frame :=
  if f.text.isEmpty then f else { f with kids := f.kids.push (.text f.text), text := "" }

@[expose] public def Frame.close (f : Frame) : Node :=
  let f := f.flush
  .elem f.name f.attrs f.kids

public structure State where
  pos : Nat
  stack : Array Frame
  root : Option Node
  nodes : Nat
  doctype : Bool
  deriving Inhabited

/-- A finished node handed to the open element, or made the root. -/
@[expose] public def State.give (s : State) (n : Node) : State :=
  match s.stack.back? with
  | some f => { s with stack := s.stack.pop.push { f.flush with kids := f.flush.kids.push n } }
  | none => { s with root := some n }

/-- Character data handed to the open element. -/
@[expose] public def State.chars (s : State) (t : String) : State :=
  match s.stack.back? with
  | some f => { s with stack := s.stack.pop.push { f with text := f.text ++ t } }
  | none => s

/-- What one step did: read on from a new state, or stop with the document
or a refusal. -/
public abbrev Step := ForInStep (Except Refusal State)

/-- One more node, under the node budget. -/
@[expose] public def State.tick (bud : Budget) (s : State) : Except Refusal State :=
  if s.nodes + 1 > bud.nodes then throw (.budget "node count") else pure { s with nodes := s.nodes + 1 }

@[expose] public def State.at (s : State) (p : Nat) : State := { s with pos := p }

@[expose] public def State.popped (s : State) : State := { s with stack := s.stack.pop }

/-- An end tag read: the open element `f` closed onto its parent, or made
the root, the reader at `p`. -/
@[expose] public def State.closeAt (s : State) (f : Frame) (p : Nat) : State := (s.popped.give f.close).at p

/-- A start tag read: the element `f` opened, the reader at `p`. -/
@[expose] public def State.openAt (s : State) (f : Frame) (p : Nat) : State :=
  { s with stack := s.stack.push f, pos := p }

/-- An end tag at `s.pos` (on `</`). -/
@[expose] public def endTag (bud : Budget) (b : ByteArray) (s : State) : Except Refusal State :=
  match readName bud b (s.pos + 2) with
  | .error e => .error e
  | .ok (name, j) =>
    let k := skipSpace b j
    if at? b k != 62 then .error (.syntax k "an unterminated end tag")
    else match s.stack.back? with
      | none => .error (.syntax s.pos s!"an end tag '{name}' with no element open")
      | some f =>
        if f.name != name then .error (.syntax s.pos s!"the end tag '{name}' closes '{f.name}'")
        else .ok (s.closeAt f (k + 1))

/-- A `<!` construct at `s.pos`: a comment, a CDATA section, or a document type declaration. -/
@[expose] public def markup (bud : Budget) (b : ByteArray) (s : State) : Except Refusal State :=
  let i := s.pos
  if bytesAt b i "<!--" then (skipComment b i).map s.at
  else if bytesAt b i "<![CDATA[" then
    if s.stack.isEmpty then .error (.syntax i "a CDATA section outside the root element")
    else match find b (i + 9) "]]>" with
      | none => .error (.syntax i "an unterminated CDATA section")
      | some j =>
        let t := normalizeEol (b.extract (i + 9) j)
        if (s.stack.back?.map (·.text.utf8ByteSize + t.utf8ByteSize)).getD 0 > bud.text then
          .error (.budget "text length")
        else ((s.chars t).tick bud).map (·.at (j + 3))
  else if bytesAt b i "<!DOCTYPE" then
    if !s.stack.isEmpty || s.root.isSome || s.doctype then
      .error (.syntax i "a document type declaration out of place")
    else (skipDoctype bud b i).map fun p => { s with pos := p, doctype := true }
  else .error (.syntax i "an unreadable '<!' construct")

/-- A start tag at `s.pos`: an element within the depth budget, empty or opened. -/
@[expose] public def startTag (bud : Budget) (b : ByteArray) (s : State) : Except Refusal State :=
  if s.stack.isEmpty && s.root.isSome then .error (.syntax s.pos "content after the root element")
  else match s.tick bud with
    | .error e => .error e
    | .ok s' =>
      match readStartTag bud b s.pos with
      | .error e => .error e
      | .ok (name, attrs, empty, j) =>
        if s'.stack.size + 1 > bud.depth then .error (.budget "element depth")
        else if empty then .ok ((s'.give (.elem name attrs #[])).at j)
        else .ok (s'.openAt { name, attrs, kids := #[], text := "" } j)

/-- A reference at `s.pos`, within the text budget. -/
@[expose] public def reference (bud : Budget) (b : ByteArray) (s : State) : Except Refusal State :=
  if s.stack.isEmpty then .error (.syntax s.pos "a reference outside the root element")
  else match readReference b s.pos with
    | .error e => .error e
    | .ok (ch, j) =>
      if (s.stack.back?.map (·.text.utf8ByteSize + ch.utf8Size)).getD 0 > bud.text then
        .error (.budget "text length")
      else ((s.chars (String.singleton ch)).tick bud).map (·.at j)

/-- Character data at `s.pos`: inside the root, one more node; outside
it, white space alone. -/
@[expose] public def charData (bud : Budget) (b : ByteArray) (s : State) : Except Refusal State :=
  match readChars b s.pos with
  | .error e => .error e
  | .ok (t, j) =>
    if s.stack.isEmpty then
      if !(t.all fun ch => ch == ' ' || ch == '\t' || ch == '\n') then
        .error (.syntax s.pos "text outside the root element")
      else .ok ((s.chars t).at j)
    else if (s.stack.back?.map (·.text.utf8ByteSize + t.utf8ByteSize)).getD 0 > bud.text then
      .error (.budget "text length")
    else ((s.chars t).tick bud).map (·.at j)

/-- One token from `s.pos`; every step that continues moves forward. -/
@[expose] public def step (bud : Budget) (b : ByteArray) (s : State) : Except Refusal State :=
  let c := at? b s.pos
  if c == 60 then
    let d := at? b (s.pos + 1)
    if d == 47 then endTag bud b s
    else if d == 33 then markup bud b s
    else if d == 63 then
      match readName bud b (s.pos + 2) with
      | .error e => .error e
      | .ok (target, _) => .error (.instruction target)
    else startTag bud b s
  else if c == 38 then reference bud b s
  else charData bud b s

/-- Read every token from `start`, at most one per byte. -/
@[expose] public def run (bud : Budget) (b : ByteArray) (start : Nat) : Except Refusal State :=
  let init : Except Refusal State :=
    .ok { pos := start, stack := #[], root := none, nodes := 0, doctype := false }
  (forIn [0:b.size + 1] init fun _ acc => pure (match acc with
    | .error e => ForInStep.done (.error e)
    | .ok s =>
      if s.pos ≥ b.size then ForInStep.done (.ok s)
      else match step bud b s with
        | .error e => ForInStep.done (.error e)
        | .ok s' =>
          if s'.pos ≤ s.pos then ForInStep.done (.error (.syntax s.pos "no progress"))
          else ForInStep.yield (.ok s')) : Id (Except Refusal State)).run

/-- Bytes as a document under the budget, or the reason they are none. -/
@[expose] public def parseWith (bud : Budget) (input : ByteArray) : Except Refusal Node :=
  if input.size > bud.bytes then .error (.budget "file size") else
  match decode input with
  | .error e => .error e
  | .ok (b, start) =>
    if !b.validateUTF8 then .error (.syntax 0 "the file is not UTF-8") else
    match badCharAt b with
    | some i => .error (.syntax i "a character XML does not admit")
    | none =>
      match run bud b start with
      | .error e => .error e
      | .ok s =>
        if s.pos < b.size then .error (.syntax s.pos "the reader stopped early")
        else if !s.stack.isEmpty then .error (.syntax b.size "an element is not closed")
        else match s.root with
          | some n => .ok n
          | none => .error (.syntax b.size "no root element")

@[expose] public def parse (input : ByteArray) : Except Refusal Node := parseWith Budget.standard input

/-- A character as a decimal character reference (§4.1). -/
@[expose] public def charRef (c : Char) : String := "&#" ++ toString c.toNat ++ ";"

/-- A character a canonical spelling writes as itself: printable ASCII but
the four markup reads, `"`, `&`, `<` and `>`. -/
@[expose] public def literal (c : Char) : Bool :=
  32 ≤ c.toNat && c.toNat ≤ 126 && c != '"' && c != '&' && c != '<' && c != '>'

/-- Text or an attribute value canonically spelled: `literal` characters as themselves, every
other one as a reference. -/
@[expose] public def escapeChars (s : String) : String :=
  s.foldl (fun acc c => if literal c then acc.push c else acc ++ charRef c) ""

mutual

-- conserves: none — a spelling.
public def renderOne (out : String) : Node → String
  | .elem name attrs kids =>
    let out := attrs.foldl (fun o (k, v) => o ++ " " ++ k ++ "=\"" ++ escapeChars v ++ "\"")
      (out ++ "<" ++ name)
    if kids.isEmpty then out ++ "/>"
    else renderList (out ++ ">") kids.toList ++ "</" ++ name ++ ">"
  | .text s =>
    let e := escapeChars s
    out ++ e

public def renderList (out : String) : List Node → String
  | [] => out
  | n :: rest => renderList (renderOne out n) rest

end

/-- A tree written as canonical UTF-8 XML, with no declaration and no comment. -/
public def render (n : Node) : ByteArray := (renderOne "" n).toUTF8

/-- An attribute in its namespace. -/
public structure Attr where
  ns : String
  name : String
  value : String
  deriving Repr, Inhabited, BEq

/-- A node with every name resolved against the namespace declarations in scope (Namespaces in
XML 1.0 §5–§6). -/
public inductive Item where
  | elem (ns : String) (name : String) (attrs : Array Attr) (kids : Array Item)
  | text (s : String)
  deriving Repr, Inhabited, BEq

@[expose] public def xmlNs : String := "http://www.w3.org/XML/1998/namespace"

/-- A name's prefix and local part; a second colon or an empty part is no
qualified name. -/
public def splitName (s : String) : Option (Option String × String) :=
  match s.splitOn ":" with
  | [l] => if l.isEmpty then none else some (none, l)
  | [p, l] => if p.isEmpty || l.isEmpty then none else some (some p, l)
  | _ => none

/-- The namespace a prefix is bound to in `scope`, innermost first. -/
public def lookup (scope : Array (String × String)) (p : String) : Option String :=
  if p == "xml" then some xmlNs else (scope.findRev? (·.1 == p)).map (·.2)

/-- The scope an element opens: its declarations over the enclosing ones; a prefix may not be undeclared (§5). -/
public def declare (scope : Array (String × String)) (attrs : Array (String × String)) :
    Except String (Array (String × String)) := do
  let mut scope := scope
  for (k, v) in attrs do
    if k == "xmlns" then scope := scope.push ("", v)
    else if k.startsWith "xmlns:" then
      let p := (k.drop 6).toString
      if v.isEmpty then throw s!"the prefix '{p}' is undeclared"
      if p == "xmlns" || (p == "xml" && v != xmlNs) || p.isEmpty || p.contains ':' then
        throw s!"the prefix '{p}' cannot be bound"
      scope := scope.push (p, v)
  return scope

mutual

-- conserves: none — a renaming of a tree's names.
/-- One node with its names resolved, or the first name no declaration in
scope binds. -/
public def resolveOne (scope : Array (String × String)) : Node → Except String Item
  | .text s => .ok (.text s)
  | .elem name attrs kids => do
    let scope ← declare scope attrs
    let some (p, l) := splitName name | throw s!"'{name}' is no qualified name"
    let ns ← match p with
      | none => pure ((lookup scope "").getD "")
      | some p =>
        if p == "xmlns" then throw s!"the element '{name}' uses the prefix 'xmlns'"
        match lookup scope p with
        | some u => pure u
        | none => throw s!"the prefix '{p}' of '{name}' is not declared"
    let mut out : Array Attr := #[]
    let mut seen : Std.HashSet (String × String) := {}
    for (k, v) in attrs do
      if k == "xmlns" || k.startsWith "xmlns:" then continue
      let some (ap, al) := splitName k | throw s!"'{k}' is no qualified name"
      let ans ← match ap with
        | none => pure ""
        | some ap =>
          match lookup scope ap with
          | some u => pure u
          | none => throw s!"the prefix '{ap}' of '{k}' is not declared"
      if seen.contains (ans, al) then
        throw s!"the attribute '{k}' is named twice in its namespace"
      seen := seen.insert (ans, al)
      out := out.push { ns := ans, name := al, value := v }
    let kids ← resolveList scope #[] kids.toList
    return .elem ns l out kids

public def resolveList (scope : Array (String × String)) (acc : Array Item) :
    List Node → Except String (Array Item)
  | [] => .ok acc
  | n :: rest => do resolveList scope (acc.push (← resolveOne scope n)) rest

end

/-- A tree with its names resolved; the `xmlns` attributes stay out. -/
public def resolve (n : Node) : Except String Item := resolveOne #[] n

/-- An attribute's value by namespace and local name. -/
@[expose] public def Attr.get? (attrs : Array Attr) (ns name : String) : Option String :=
  (attrs.find? fun a => a.ns == ns && a.name == name).map (·.value)

mutual

-- conserves: none — the XPath string-value of a node.
/-- A node's text, all its descendants', in document order. -/
public def Item.textOne (acc : String) : Item → String
  | .text s => acc ++ s
  | .elem _ _ _ kids => Item.textList acc kids.toList

public def Item.textList (acc : String) : List Item → String
  | [] => acc
  | n :: rest => Item.textList (Item.textOne acc n) rest

end

/-- The prefix a namespace is written with: SVG's the default, `xml` its
reserved one, XLink `xlink`, any other `n` and its place. -/
public def prefixOf (others : Array String) (ns : String) : Option String :=
  if ns == "http://www.w3.org/2000/svg" then none
  else if ns == xmlNs then some "xml"
  else if ns == "http://www.w3.org/1999/xlink" then some "xlink"
  else some ("n" ++ toString ((others.findIdx? (· == ns)).getD others.size))

mutual

-- conserves: none — a census of a tree's namespaces.
/-- Every namespace a node names, other than SVG's, XML's and XLink's, in
first-use order. -/
public def nsOne (acc : Array String) : Item → Array String
  | .text _ => acc
  | .elem ns _ attrs kids =>
    let note (a : Array String) (n : String) : Array String :=
      if n.isEmpty || n == "http://www.w3.org/2000/svg" || n == xmlNs ||
          n == "http://www.w3.org/1999/xlink" || a.contains n then a else a.push n
    nsList (attrs.foldl (fun a at_ => note a at_.ns) (note acc ns)) kids.toList

public def nsList (acc : Array String) : List Item → Array String
  | [] => acc
  | n :: rest => nsList (nsOne acc n) rest

end

mutual

-- conserves: none — a respelling of a resolved tree's names.
/-- A resolved node as a syntactic one, each name under the prefix its namespace is written with. -/
public def toNodeOne (others : Array String) : Item → Node
  | .text s => .text s
  | .elem ns name attrs kids =>
    let ename := match prefixOf others ns with
      | some p => if ns.isEmpty then name else p ++ ":" ++ name
      | none => name
    let undeclare : Array (String × String) := if ns.isEmpty then #[("xmlns", "")] else #[]
    let as := attrs.map fun a =>
      if a.ns.isEmpty then (a.name, a.value)
      else match prefixOf others a.ns with
        | some p => (p ++ ":" ++ a.name, a.value)
        | none => (a.name, a.value)
    .elem ename (undeclare ++ as) (toNodeList others #[] kids.toList)

public def toNodeList (others : Array String) (acc : Array Node) : List Item → Array Node
  | [] => acc
  | n :: rest => toNodeList others (acc.push (toNodeOne others n)) rest

end

/-- A resolved tree written as canonical XML, its namespaces declared on the root. -/
public def renderItem (t : Item) : ByteArray :=
  let others := nsOne #[] t
  let decls : Array (String × String) :=
    #[("xmlns", "http://www.w3.org/2000/svg"), ("xmlns:xlink", "http://www.w3.org/1999/xlink")] ++
      others.mapIdx fun k ns => ("xmlns:n" ++ toString k, ns)
  match toNodeOne others t with
  | .elem name attrs kids => render (.elem name (decls ++ attrs.filter (·.1 != "xmlns")) kids)
  | .text s => render (.text s)

end LeanTex.Core.Xml
