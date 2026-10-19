module

public import LeanTex.Core.SurfaceKind
public import Std.Data.HashSet
import LeanTex.Core.Hex

/-! Documentation comments' markup lowered into markdown by each dialect's documented rules (the
Rustdoc Book, the JDK's Documentation Comment Specification, Doxygen's manual), each scalar keeping
its source place and each construct a reader does not read named. -/
namespace LeanTex.Core.DocMarkup

/-- A scalar of a comment's text and the source line and column it stands at. -/
public structure PChar where
  c : Char
  line : Nat
  col : Nat
  deriving Repr, BEq, Inhabited

public abbrev PText := Array PChar

/-- What a reader does not read. -/
public inductive Lost where
  /-- A cross-reference to a program element, which no target on the page stands for. -/
  | unlinked (ref : String)
  /-- A tag or command the reader does not read. -/
  | unread (what : String)
  deriving Repr, BEq, Inhabited

/-- A loss and where its construct stands. -/
public structure Loss where
  lost : Lost
  line : Nat
  col : Nat
  deriving Repr, BEq, Inhabited

/-- What lowering has written: the markdown, and the losses. -/
public structure Out where
  text : PText := #[]
  losses : Array Loss := #[]
  deriving Inhabited

namespace Out

@[inline] def put (o : Out) (c : Char) (at_ : PChar) : Out := { o with text := o.text.push { at_ with c } }

def str (o : Out) (s : String) (at_ : PChar) : Out := s.foldl (fun o c => o.put c at_) o

def lose (o : Out) (l : Lost) (at_ : PChar) : Out :=
  { o with losses := o.losses.push ⟨l, at_.line, at_.col⟩ }

def last? (o : Out) (k : Nat) : Option Char :=
  if k < o.text.size then (o.text[o.text.size - 1 - k]?).map (·.c) else none

/-- Whether nothing is written, or the text ends a line. -/
def atLineStart (o : Out) : Bool := o.text.isEmpty || o.last? 0 == some '\n'

/-- A paragraph break: the line ended and one blank line, unless the text already ends so. -/
def para (o : Out) (at_ : PChar) : Out :=
  if o.text.isEmpty then o
  else if o.last? 0 == some '\n' && o.last? 1 == some '\n' then o
  else if o.last? 0 == some '\n' then o.put '\n' at_
  else (o.put '\n' at_).put '\n' at_

/-- The text with its trailing spaces dropped. -/
def trimEnd (o : Out) : Out := Id.run do
  let mut t := o.text
  for _ in [0:t.size] do
    if (t.back?.map (·.c == ' ')).getD false then t := t.pop else break
  return { o with text := t }

/-- The line ended, unless it is. -/
def endLine (o : Out) (at_ : PChar) : Out := if o.atLineStart then o else o.put '\n' at_

end Out

/-- The characters of a placed text. -/
public def strOf (t : PText) : String := String.ofList (t.toList.map (·.c))

private def charAt (t : PText) (i : Nat) : Char := (t[i]?.map (·.c)).getD '\x00'

private def isSpace (c : Char) : Bool := c == ' ' || c == '\t'

private def isBlank (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n'

/-- A placed text split at its line feeds. -/
private def splitLines (t : PText) : Array PText := Id.run do
  let mut out : Array PText := #[]
  let mut cur : PText := #[]
  for p in t do
    if p.c == '\n' then
      out := out.push (cur.push p)
      cur := #[]
    else cur := cur.push p
  return out.push cur

/-- A text's scalars past its leading spaces and tabs. -/
private def dropIndent (t : PText) : PText := t.extract ((t.findIdx? (!isSpace ·.c)).getD t.size) t.size

/-- Whether `w` stands at `i`. -/
private def litAt (t : PText) (i : Nat) (w : String) : Bool :=
  w.toList.zipIdx.all fun (c, k) => charAt t (i + k) == c

/-- The longest run of backticks a string holds. -/
private def backtickRun (s : String) : Nat := Id.run do
  let mut best := 0
  let mut cur := 0
  for c in s.toList do
    if c == '`' then
      cur := cur + 1
      best := max best cur
    else cur := 0
  return best

/-- A code span holding `s` as written, its fence one backtick longer than any run it holds. -/
private def codeSpan (o : Out) (s : String) (at_ : PChar) : Out :=
  let s := (s.map fun c => if c == '\n' || c == '\r' then ' ' else c).trimAscii.toString
  if s.isEmpty then o else
  let fence := String.ofList (List.replicate (backtickRun s + 1) '`')
  let pad := s.front == '`' || s.back == '`'
  o.str (fence ++ (if pad then " " ++ s ++ " " else s) ++ fence) at_

/-- A fenced code block of `body` in `lang`, its fence longer than any it holds. -/
private def fenced (o : Out) (lang : String) (body : String) (at_ : PChar) : Out :=
  let fence := String.ofList (List.replicate (max 3 (backtickRun body + 1)) '`')
  let ls := (body.splitOn "\n").dropWhile (·.trimAscii.isEmpty)
  let ls := (ls.reverse.dropWhile (·.trimAscii.isEmpty)).reverse
  let margin := ls.foldl (fun m l => if l.trimAscii.isEmpty then m else
    min m (l.toList.takeWhile (· == ' ')).length) 1000
  let body := "\n".intercalate (ls.map fun l => (l.drop (min margin l.length)).toString)
  (o.para at_).str (fence ++ lang ++ "\n" ++ body ++ "\n" ++ fence ++ "\n\n") at_

/-- Markdown's punctuation, which a literal scalar is escaped from. -/
private def mdSpecial (c : Char) : Bool := "\\`*_[]<>#+-!|~=".toList.contains c

/-- A scalar as literal text, markdown's punctuation escaped, and a `.` or `)` after digits opening
a line, which would open an ordered list. -/
private def literal (o : Out) (p : PChar) : Out :=
  let digitsOpen := Id.run do
    let mut k := 0
    for _ in [0:o.text.size] do
      if (o.last? k).any Char.isDigit then k := k + 1 else break
    if k == 0 then return false
    -- The line before the digits: white space and list or quote markers alone open a block there.
    let mut before : List Char := []
    for _ in [0:o.text.size] do
      match o.last? k with
      | some '\n' | none => break
      | some c =>
        before := c :: before
        k := k + 1
    let words := (String.ofList before).splitOn " " |>.filter (!·.isEmpty)
    return words.all fun w =>
      let ds := (w.dropEnd 1).toString
      ["-", "*", "+", ">"].contains w ||
        (!ds.isEmpty && ds.all Char.isDigit && (w.endsWith "." || w.endsWith ")"))
  if mdSpecial p.c || ((p.c == '.' || p.c == ')') && digitsOpen) then (o.put '\\' p).put p.c p
  else o.put p.c p

/-- Text set literally, one space for each run of white space. -/
private def literalLine (o : Out) (t : PText) : Out :=
  t.foldl (init := o) fun o p =>
    if isBlank p.c then (if o.last? 0 == some ' ' then o else o.put ' ' p) else literal o p

/-! ## HTML -/

/-- An HTML tag where a `<` stands: its name, lowercased, whether it closes, its attributes' text,
and the index past its `>`. -/
private structure Tag where
  name : String
  closing : Bool
  attrs : String
  stop : Nat

/-- The tag at `i`, `none` where the `<` opens none. -/
private def tagAt? (t : PText) (i : Nat) : Option Tag := Id.run do
  if charAt t i != '<' then return none
  if litAt t i "<!--" then
    for k in [i + 4:t.size] do
      if litAt t k "-->" then return some ⟨"!--", false, "", k + 3⟩
    return none
  let closing := charAt t (i + 1) == '/'
  let start := if closing then i + 2 else i + 1
  let mut j := start
  let mut name := ""
  for _ in [start:t.size] do
    let c := charAt t j
    if c.isAlpha || (c.isDigit && j > start) then
      name := name.push c.toLower
      j := j + 1
    else break
  if name.isEmpty then return none
  let next := charAt t j
  if !(next == '>' || next == '/' || isBlank next) then return none
  let mut attrs := ""
  let mut quote : Option Char := none
  for _ in [j:t.size] do
    let c := charAt t j
    match quote with
    | some q =>
      if c == q then quote := none
      attrs := attrs.push c
    | none =>
      if c == '>' then return some ⟨name, closing, attrs.trimAscii.toString, j + 1⟩
      if c == '<' then return none
      if c == '"' || c == '\'' then quote := some c
      attrs := attrs.push c
    j := j + 1
  return none

/-- An attribute's value, quoted or bare. -/
private def attrValue? (attrs key : String) : Option String := Id.run do
  let cs := attrs.toList.toArray
  let low := attrs.toLower.toList.toArray
  let k := key.toList.toArray
  for i in [0:cs.size] do
    let before := i == 0 || (cs[i - 1]?.map isBlank).getD false
    if before && (List.range k.size).all (fun d => low[i + d]? == k[d]?) then
      let mut j := i + k.size
      for _ in [j:cs.size] do
        if cs[j]? == some ' ' then j := j + 1 else break
      if cs[j]? != some '=' then continue
      j := j + 1
      for _ in [j:cs.size] do
        if cs[j]? == some ' ' then j := j + 1 else break
      let rest := (cs.extract (j + 1) cs.size).toList
      match cs[j]? with
      | some '"' => return some (String.ofList (rest.takeWhile (· != '"')))
      | some '\'' => return some (String.ofList (rest.takeWhile (· != '\'')))
      | _ => return some (String.ofList ((cs.extract j cs.size).toList.takeWhile (!isBlank ·)))
  return none

/-- Where the tag closing an element named `name` that opened before `i` stands, and past it,
nested ones of its name counted. -/
private def closeOf? (t : PText) (i : Nat) (name : String) : Option (Nat × Nat) := Id.run do
  let mut depth := 0
  let mut j := i
  for _ in [i:t.size] do
    if j ≥ t.size then break
    match tagAt? t j with
    | some tag =>
      if tag.name == name then
        if tag.closing then
          if depth == 0 then return some (j, tag.stop)
          depth := depth - 1
        else depth := depth + 1
      j := tag.stop
    | none => j := j + 1
  return none

/-- A named or numeric character reference's scalar. -/
private def entity? (name : String) : Option Char :=
  match name with
  | "lt" => some '<'
  | "gt" => some '>'
  | "amp" => some '&'
  | "quot" => some '"'
  | "apos" => some '\''
  | "nbsp" => some ' '
  | _ =>
    if name.startsWith "#x" || name.startsWith "#X" then
      (Hex.value? (name.drop 2).toString.toList).bind fun n =>
        if n < 0x110000 && n > 0 then some (Char.ofNat n) else none
    else if name.startsWith "#" then
      ((name.drop 1).toString.toNat?).bind fun n => if n < 0x110000 && n > 0 then some (Char.ofNat n) else none
    else none

/-- The reference at `i`: its scalar and the index past its `;`. -/
private def entityAt? (t : PText) (i : Nat) : Option (Char × Nat) := Id.run do
  if charAt t i != '&' then return none
  let mut name := ""
  for k in [i + 1:min t.size (i + 12)] do
    let c := charAt t k
    if c == ';' then return (entity? name).map (·, k + 1)
    if !(c.isAlphanum || c == '#') then return none
    name := name.push c
  return none

/-! ## Inline tags -/

/-- A Javadoc inline tag `{@name body}` at `i`: its name, its body past the white space after the
name, and the index past its `}`, braces in the body balanced. -/
private def inlineTagAt? (t : PText) (i : Nat) : Option (String × PText × Nat) := Id.run do
  if charAt t i != '{' || charAt t (i + 1) != '@' then return none
  let mut j := i + 2
  let mut name := ""
  for _ in [j:t.size] do
    let c := charAt t j
    if c.isAlpha then
      name := name.push c
      j := j + 1
    else break
  if name.isEmpty then return none
  for _ in [j:t.size] do
    if isBlank (charAt t j) then j := j + 1 else break
  let bodyStart := j
  let mut depth := 0
  for _ in [j:t.size] do
    match charAt t j with
    | '{' => depth := depth + 1
    | '}' =>
      if depth == 0 then return some (name, t.extract bodyStart j, j + 1)
      depth := depth - 1
    | _ => pure ()
    j := j + 1
  return none

/-- A reference's first word, parentheses balanced, and what follows it past its white space. -/
private def splitRef (t : PText) : PText × PText := Id.run do
  let mut depth : Nat := 0
  for p in t, k in [0:t.size] do
    if p.c == '(' then depth := depth + 1
    else if p.c == ')' then depth := depth - 1
    else if depth == 0 && isBlank p.c then
      return (t.extract 0 k, (t.extract (k + 1) t.size).extract
        (((t.extract (k + 1) t.size).findIdx? (!isBlank ·.c)).getD 0) t.size)
  return (t, #[])

/-- A reference as the standard doclet shows it: a member's `#` as `.`, one of the class at hand as
its name alone. -/
private def refShown (ref : String) : String :=
  let r := if ref.startsWith "#" then (ref.drop 1).toString else ref
  r.replace "#" "."

/-- What a text sets as code: an inline tag's code, a link's text, the rest's scalars with
references decoded and tags dropped. -/
private def codeText (t : PText) : String := Id.run do
  let mut out := ""
  let mut i := 0
  for _ in [0:t.size + 1] do
    if i ≥ t.size then break
    match inlineTagAt? t i with
    | some (name, body, next) =>
      let (ref, label) := splitRef body
      out := out ++ (if name == "link" || name == "linkplain" then
          (if label.isEmpty then refShown (strOf ref) else (strOf label))
        else (strOf body))
      i := next
    | none =>
      match tagAt? t i, entityAt? t i with
      | some tag, _ => i := tag.stop
      | none, some (c, next) =>
        out := out.push c
        i := next
      | none, none =>
        out := out.push (charAt t i)
        i := i + 1
  return out

/-! ## The walk -/

/-- A reader's dialect: Javadoc's HTML text, Javadoc's markdown text, Doxygen's markdown with
commands, rustdoc's markdown. -/
public inductive Dialect where
  | javadoc
  | javadocMarkdown
  | doxygen
  | rustdoc
  deriving BEq, DecidableEq, Repr

private def Dialect.markdown : Dialect → Bool
  | .javadoc => false
  | .javadocMarkdown | .doxygen | .rustdoc => true

/-- A Doxygen section: its label, and whether its entries stand in one list. -/
private structure Section where
  label : String
  listed : Bool
  deriving BEq

/-- The walk's state: the open HTML lists, innermost first, and their open items; whether a heading
or a term is open; whether a quote is; the Doxygen section the text is in; and whether the whole
text sets on one line, as a tag's entry does. -/
private structure Walk where
  lists : List (Bool × Nat) := []
  items : Nat := 0
  line : Bool := false
  quoted : Bool := false
  section? : Option Section := none
  oneLine : Bool := false

/-- Whether a line feed reads as a space: inside an item, a heading, a term or a listed section. -/
private def Walk.joined (w : Walk) : Bool :=
  w.items > 0 || w.line || w.oneLine || (w.section?.any (·.listed))

/-- The walk past a blank line, which ends every open item, heading, term and section. -/
private def Walk.broken (w : Walk) : Walk := { w with items := 0, line := false, section? := none }

/-- What the walk over one text reads with: its dialect, the listing language a code block's code
sets in, and the citation keys the page cites by. -/
private structure Ctx where
  dialect : Dialect
  lang : String
  known : Std.HashSet String

/-- The HTML elements whose content stands apart from what is around it. -/
private def blockElement (name : String) : Bool :=
  ["table", "tr", "thead", "tbody", "tfoot", "caption", "div", "center", "section", "article",
   "figure", "figcaption", "nav", "header", "footer", "aside", "main", "address"].contains name

/-- One HTML tag the walk meets at `i`: what it writes, and where the walk goes on. -/
private def tagStep (cx : Ctx) (t : PText) (i : Nat) (tag : Tag) (w : Walk) (o : Out) :
    Out × Walk × Nat :=
  let at_ := (t[i]?).getD default
  let open_ := !tag.closing
  match tag.name with
  | "!--" => (o, w, tag.stop)
  | "b" | "strong" => (o.str "**" at_, w, tag.stop)
  | "i" | "em" | "cite" | "var" | "dfn" => (o.str "*" at_, w, tag.stop)
  | "s" | "strike" | "del" => (o.str "~~" at_, w, tag.stop)
  | "code" | "tt" | "kbd" | "samp" =>
    if !open_ then (o, w, tag.stop) else
    match closeOf? t tag.stop tag.name with
    | some (a, b) => (codeSpan o (codeText (t.extract tag.stop a)) at_, w, b)
    | none => (o, w, tag.stop)
  | "pre" =>
    if !open_ then (o, w, tag.stop) else
    match closeOf? t tag.stop "pre" with
    | some (a, b) => (fenced o cx.lang (codeText (t.extract tag.stop a)) at_, w, b)
    | none => (o, w, tag.stop)
  | "a" =>
    if !open_ then (o, w, tag.stop) else
    match attrValue? tag.attrs "href", closeOf? t tag.stop "a" with
    | some href, some (a, b) =>
      let text := codeText (t.extract tag.stop a)
      let o := text.foldl (fun o c => literal o { at_ with c }) (o.put '[' at_)
      (o.str ("](" ++ href.replace " " "%20" ++ ")") at_, w, b)
    | none, some (a, b) =>
      (if a == tag.stop then o.lose (.unread "<a name>") at_ else o, w, if a == tag.stop then b else tag.stop)
    | _, _ => (o, w, tag.stop)
  | "p" | "dd" | "dl" => (o.para at_, w, tag.stop)
  | "br" => (o.str "\\\n" at_, w, tag.stop)
  | "ul" | "menu" | "ol" =>
    if open_ then
      -- A list inside an item nests under it, its lines starting at the item's content.
      let o := if w.items > 0 then o.endLine at_ else o.para at_
      (o, { w with lists := (tag.name == "ol", 0) :: w.lists }, tag.stop)
    else
      let lists := w.lists.drop 1
      (if lists.isEmpty then o.para at_ else o.endLine at_, { w with lists, items := min w.items lists.length },
        tag.stop)
  | "li" =>
    if !open_ then (o, { w with items := w.items - 1 }, tag.stop) else
    let width (l : Bool × Nat) : Nat := if l.1 then (toString (l.2 + 1)).length + 2 else 2
    let indent := String.ofList (List.replicate ((w.lists.drop 1).foldl (· + width ·) 0) ' ')
    let (marker, lists) := match w.lists with
      | (true, n) :: rest => (s!"{n + 1}. ", (true, n + 1) :: rest)
      | (false, n) :: rest => ("- ", (false, n + 1) :: rest)
      | [] => ("- ", [])
    ((o.endLine at_).str (indent ++ marker) at_,
      { w with lists, items := min (w.items + 1) (max 1 w.lists.length) }, tag.stop)
  | "h1" | "h2" | "h3" | "h4" | "h5" | "h6" =>
    let n := ((tag.name.drop 1).toString.toNat?).getD 1
    if open_ then
      ((o.para at_).str (String.ofList (List.replicate n '#') ++ " ") at_, { w with line := true },
        tag.stop)
    else (o.para at_, { w with line := false }, tag.stop)
  | "hr" => ((o.para at_).str "---\n\n" at_, w, tag.stop)
  | "blockquote" =>
    if open_ then ((o.para at_).str "> " at_, { w with quoted := true }, tag.stop)
    else (o.para at_, { w with quoted := false }, tag.stop)
  | "dt" =>
    if open_ then ((o.para at_).str "**" at_, { w with line := true }, tag.stop)
    else ((o.str "**" at_).para at_, { w with line := false }, tag.stop)
  | "td" | "th" | "sub" | "sup" =>
    let o := if open_ then o.lose (.unread ("<" ++ tag.name ++ ">")) at_ else o
    (if o.last? 0 == some ' ' || o.atLineStart then o else o.put ' ' at_, w, tag.stop)
  | name =>
    let o := if tag.closing then o else o.lose (.unread ("<" ++ name ++ ">")) at_
    (if blockElement name then o.para at_ else o, w, tag.stop)

/-- A Javadoc inline tag the walk meets: what it writes. -/
private def inlineTag (cx : Ctx) (name : String) (body : PText) (at_ : PChar) (o : Out) : Out :=
  let (ref, label) := splitRef body
  match name with
  | "code" | "systemProperty" => codeSpan o (strOf body) at_
  | "literal" => literalLine o body
  | "link" =>
    let o := o.lose (.unlinked (strOf ref)) at_
    codeSpan o (if label.isEmpty then refShown (strOf ref) else (strOf label)) at_
  | "linkplain" =>
    let o := o.lose (.unlinked (strOf ref)) at_
    literalLine o (if label.isEmpty then (refShown (strOf ref)).toList.toArray.map ({ at_ with c := · })
      else label)
  | "value" =>
    if ref.isEmpty then o.lose (.unread "{@value}") at_
    else codeSpan (o.lose (.unlinked (strOf ref)) at_) (refShown (strOf ref)) at_
  | "index" => literalLine o (if (strOf ref).startsWith "\"" then body.filter (·.c != '"') else ref)
  | "summary" => literalLine o body
  | "return" => literalLine (o.str "Returns " at_) body
  | "snippet" =>
    match (strOf body).splitOn ":" with
    | attrs :: rest@(_ :: _) =>
      let lang := ((attrs.splitOn " ").findSome? fun a =>
        if a.startsWith "lang=" then some ((a.drop 5).toString.replace "\"" "") else none).getD cx.lang
      fenced o lang (":".intercalate rest) at_
    | _ => o.lose (.unread "{@snippet}") at_
  | "inheritDoc" | "docRoot" => o.lose (.unread ("{@" ++ name ++ "}")) at_
  | _ =>
    let o := o.lose (.unread ("{@" ++ name ++ "}")) at_
    literalLine (o.str "{@" at_ |>.str name at_ |>.str " " at_) body |>.str "}" at_

/-! ## Doxygen -/

/-- Doxygen's paragraph sections: each command's label, and whether its entries stand in a list. -/
private def doxSection? (cmd : String) : Option Section :=
  let s (l : String) (b : Bool := false) : Option Section := some ⟨l, b⟩
  match cmd with
  | "param" => s "Parameters" true
  | "tparam" => s "Template Parameters" true
  | "retval" => s "Return values" true
  | "throw" | "throws" | "exception" => s "Exceptions" true
  | "return" | "returns" | "result" => s "Returns"
  | "see" | "sa" => s "See also"
  | "note" => s "Note"
  | "warning" => s "Warning"
  | "attention" => s "Attention"
  | "remark" | "remarks" => s "Remarks"
  | "todo" => s "Todo"
  | "bug" => s "Bug"
  | "pre" => s "Precondition"
  | "post" => s "Postcondition"
  | "invariant" => s "Invariant"
  | "since" => s "Since"
  | "version" => s "Version"
  | "author" | "authors" => s "Author"
  | "date" => s "Date"
  | "copyright" => s "Copyright"
  | "deprecated" => s "Deprecated"
  | "test" => s "Test"
  | _ => none

/-- The Doxygen commands that mark what a comment documents, or group it, which a page that sets the
comment where it stands has no use for: each with whether its argument runs to the line's end. -/
private def doxStructural : List (String × Bool) :=
  [("class", true), ("struct", true), ("union", true), ("enum", true), ("fn", true), ("var", true),
   ("def", true), ("typedef", true), ("namespace", true), ("package", true), ("interface", true),
   ("protocol", true), ("property", true), ("headerfile", true), ("defgroup", true),
   ("ingroup", true), ("addtogroup", true), ("weakgroup", true), ("name", true),
   ("relates", true), ("related", true), ("relatesalso", true), ("memberof", true),
   ("overload", true), ("concept", true), ("idlexcept", true), ("dir", true),
   ("endinternal", false), ("endcond", false),
   ("private", false), ("public", false), ("protected", false), ("static", false),
   ("privatesection", false), ("publicsection", false), ("protectedsection", false),
   ("showinitializer", false), ("hideinitializer", false), ("nosubgrouping", false),
   ("callgraph", false), ("callergraph", false), ("hidecallgraph", false),
   ("hidecallergraph", false), ("showrefby", false), ("hiderefby", false), ("showrefs", false),
   ("hiderefs", false), ("showenumvalues", false), ("hideenumvalues", false), ("pure", false),
   ("extends", true), ("implements", true), ("anchor", true), ("copydoc", true),
   ("copybrief", true), ("copydetails", true), ("include", true), ("includelineno", true),
   ("example", true), ("dontinclude", true), ("line", true), ("skip", true), ("skipline", true),
   ("until", true), ("image", true), ("dotfile", true), ("mscfile", true), ("diafile", true)]

/-- Doxygen's escaped scalars, `\x` for the `x` the text means. -/
private def doxEscapes : List String :=
  ["\\", "@", "&", "$", "#", "<", ">", "%", "\"", ".", "|", "{", "}", "=", "!", "?"]

/-- A Doxygen command at `i`: `\` or `@`, standing where no word scalar precedes it, then its
name. -/
private def doxCommandAt? (t : PText) (i : Nat) : Option (String × Nat) := Id.run do
  let c := charAt t i
  if !(c == '\\' || c == '@') then return none
  if i > 0 && (charAt t (i - 1)).isAlphanum then return none
  let mut j := i + 1
  let mut name := ""
  for _ in [j:t.size] do
    let d := charAt t j
    if d.isAlpha || (d.isDigit && !name.isEmpty) || (d == '_' && !name.isEmpty) then
      name := name.push d
      j := j + 1
    else break
  if name.isEmpty then return none
  return some (name, j)

/-- The word after `i`, past white space on its line, trailing punctuation left out, and the index
past it. -/
private def wordAfter (t : PText) (i : Nat) : PText × Nat := Id.run do
  let mut j := i
  for _ in [i:t.size] do
    if isSpace (charAt t j) then j := j + 1 else break
  let start := j
  for _ in [j:t.size] do
    if isBlank (charAt t j) || charAt t j == '\x00' then break
    j := j + 1
  let opens := ((t.extract start j).filter (·.c == '(')).size
  let mut closes := ((t.extract start j).filter (·.c == ')')).size
  let mut stop := j
  for _ in [start:j] do
    let c := charAt t (stop - 1)
    if stop > start && (".,;:!?".toList.contains c || (c == ')' && closes > opens)) then
      if c == ')' then closes := closes - 1
      stop := stop - 1
    else break
  return (t.extract start stop, stop)

/-- The index of the first `c` at or after `i`, before a blank line. -/
private def findOnPara? (t : PText) (i : Nat) (c : Char) : Option Nat := Id.run do
  for k in [i:t.size] do
    let d := charAt t k
    if d == c then return some k
    if d == '\n' && charAt t (k + 1) == '\n' then return none
  return none

/-- The index past the line holding `i`, its line feed kept. -/
private def lineEndAt (t : PText) (i : Nat) : Nat := Id.run do
  for k in [i:t.size] do
    if charAt t k == '\n' then return k
  return t.size

/-- Where a raw block opened at `i` closes: the index of `stop` after it, and past it. -/
private def blockClose? (t : PText) (i : Nat) (stops : List String) : Option (Nat × Nat) := Id.run do
  for k in [i:t.size] do
    for s in stops do
      if litAt t k s && !(charAt t (k + s.length)).isAlpha then return some (k, k + s.length)
  return none

/-- A code block's info string's language, `{.ext}` or `ext` an extension naming a language; the
listing language where none is named. -/
private def doxLang (cx : Ctx) (info : String) : String :=
  let info := ((info.trimAscii.toString.dropWhile (· == '{')).dropEndWhile (· == '}')).toString
  let ext := (info.dropWhile (· == '.')).toString.trimAscii.toString
  if ext.isEmpty then cx.lang
  else match Ir.Surface.ofInput? ("x." ++ ext) with
    | some (.code l) => l.listing
    | _ => ext

/-- A Doxygen command the walk meets at `i`, named `cmd`, its name ending at `j`: what it writes,
and where the walk goes on. -/
private def doxStep (cx : Ctx) (t : PText) (i j : Nat) (cmd : String) (w : Walk) (o : Out) :
    Out × Walk × Nat :=
  let at_ := (t[i]?).getD default
  let shown := String.singleton (charAt t i) ++ cmd
  match doxSection? cmd with
  | some sec =>
    let (dir, j) := if charAt t j == '[' then
        let k := (List.range 12).find? (fun d => charAt t (j + d) == ']')
        match k with
        | some d => (some (String.ofList ((t.extract (j + 1) (j + d)).toList.map (·.c))), j + d + 1)
        | none => (none, j)
      else (none, j)
    let continues := w.section? == some sec && sec.listed
    let o := if continues then o.endLine at_ else (o.para at_).str ("**" ++ sec.label ++ ":**") at_
    if sec.listed then
      let (name, j) := wordAfter t j
      let o := (if continues then o else o.para at_).str "- " at_
      let o := codeSpan o (strOf name) at_
      let o := match dir with
        | some d => o.str (" (" ++ d ++ ")") at_
        | none => o
      (o.str " –" at_, { w with section? := some sec }, j)
    else (o, { w with section? := some sec }, j)
  | none =>
  match cmd with
  | "brief" | "short" | "details" | "file" | "mainpage" =>
    let past (k : Nat) : Nat := Id.run do
      for q in [k:t.size] do
        if !isSpace (charAt t q) then return q
      return t.size
    if cmd == "file" then
      let e := lineEndAt t j
      (o, w, if (dropIndent (t.extract j e)).all (fun p => !isBlank p.c) then e else past j)
    else if cmd == "mainpage" then
      let e := lineEndAt t j
      (((o.para at_).str "# " at_) |> fun o => literalLine o (dropIndent (t.extract j e)), w, e)
    else (o, w, past j)
  | "c" | "p" =>
    let (word, j) := wordAfter t j
    (codeSpan o (strOf word) at_, w, j)
  | "b" =>
    let (word, j) := wordAfter t j
    ((o.str "**" at_ |> fun o => literalLine o word).str "**" at_, w, j)
  | "e" | "em" | "a" =>
    let (word, j) := wordAfter t j
    ((o.str "*" at_ |> fun o => literalLine o word).str "*" at_, w, j)
  | "n" => (o.str "\\\n" at_, w, j)
  | "li" | "arg" =>
    let k := Id.run do
      for q in [j:t.size] do
        if !isSpace (charAt t q) then return q
      return t.size
    ((o.endLine at_).str "- " at_, w, k)
  | "par" =>
    let e := lineEndAt t j
    let title := dropIndent (t.extract j e)
    let o := o.para at_
    (if title.isEmpty then o else ((o.str "**" at_ |> fun o => literalLine o title).str "**" at_).para at_,
      w, e)
  | "section" | "subsection" | "subsubsection" | "paragraph" | "page" =>
    let (_, j) := wordAfter t j
    let e := lineEndAt t j
    let n := match cmd with
      | "section" | "page" => 2
      | "subsection" => 3
      | "subsubsection" => 4
      | _ => 5
    (((o.para at_).str (String.ofList (List.replicate n '#') ++ " ") at_ |>
      fun o => literalLine o (dropIndent (t.extract j e))).para at_, w, e)
  | "ref" | "link" =>
    let (name, j) := wordAfter t j
    let o := o.lose (.unlinked (strOf name)) at_
    if cmd == "link" then
      match blockClose? t j ["\\endlink", "@endlink"] with
      | some (a, b) => (literalLine o (dropIndent (t.extract j a)), w, b)
      | none => (codeSpan o (strOf name) at_, w, j)
    else
      let k := (List.range 4).find? (fun d => !isSpace (charAt t (j + d))) |>.getD 0
      if charAt t (j + k) == '"' then
        match findOnPara? t (j + k + 1) '"' with
        | some q => (literalLine o (t.extract (j + k + 1) q), w, q + 1)
        | none => (codeSpan o (strOf name) at_, w, j)
      else (codeSpan o (strOf name) at_, w, j)
  | "cite" =>
    let (key, j) := wordAfter t j
    (o.str ("[" ++ strOf key ++ "]") at_, w, j)
  | "code" =>
    let (info, j) := if charAt t j == '{' then
        match (List.range 16).find? (fun d => charAt t (j + d) == '}') with
        | some d => (String.ofList ((t.extract j (j + d + 1)).toList.map (·.c)), j + d + 1)
        | none => ("", j)
      else ("", j)
    match blockClose? t j ["\\endcode", "@endcode"] with
    | some (a, b) => (fenced o (doxLang cx info) (strOf (t.extract j a)) at_, w, b)
    | none => (fenced o (doxLang cx info) (strOf (t.extract j t.size)) at_, w, t.size)
  | "verbatim" =>
    match blockClose? t j ["\\endverbatim", "@endverbatim"] with
    | some (a, b) => (fenced o "text" (strOf (t.extract j a)) at_, w, b)
    | none => (fenced o "text" (strOf (t.extract j t.size)) at_, w, t.size)
  | "f" => (o, w, j)
  | "internal" | "cond" =>
    -- Doxygen leaves internal documentation and conditional sections out unless configured in.
    let stops := if cmd == "internal" then ["\\endinternal", "@endinternal"] else ["\\endcond", "@endcond"]
    let o := o.lose (.unread shown) at_
    match blockClose? t j stops with
    | some (_, b) => (o, w, b)
    | none => (o, w, t.size)
  | "htmlonly" | "latexonly" | "xmlonly" | "manonly" | "rtfonly" | "docbookonly" | "dot" | "msc"
  | "startuml" =>
    let ends := match cmd with
      | "dot" => ["enddot"]
      | "msc" => ["endmsc"]
      | "startuml" => ["enduml"]
      | c => ["end" ++ c]
    let stops := ends.flatMap fun e => ["\\" ++ e, "@" ++ e]
    let o := o.lose (.unread shown) at_
    match blockClose? t j stops with
    | some (_, b) => (o, w, b)
    | none => (o, w, t.size)
  | _ =>
    match doxStructural.lookup cmd with
    | some toEnd => (o.lose (.unread shown) at_, w, if toEnd then lineEndAt t j else j)
    | none =>
      let o := o.lose (.unread shown) at_
      ((literal o at_).str cmd at_, w, j)

/-- A Doxygen formula at `i`, `\f$ … \f$`, `\f[ … \f]` or `\f{env}{ … \f}`: set as code, its reading
named, and the index past it. -/
private def doxFormula? (t : PText) (i : Nat) : Option (String × Bool × Nat) :=
  let c := charAt t i
  if !((c == '\\' || c == '@') && charAt t (i + 1) == 'f') then none else
  match charAt t (i + 2) with
  | '$' => (blockClose? t (i + 3) ["\\f$", "@f$"]).map fun (a, b) => ((strOf (t.extract (i + 3) a)), false, b)
  | '[' => (blockClose? t (i + 3) ["\\f]", "@f]"]).map fun (a, b) => ((strOf (t.extract (i + 3) a)), true, b)
  | '{' => (blockClose? t (i + 3) ["\\f}", "@f}"]).map fun (a, b) => ((strOf (t.extract (i + 3) a)), true, b)
  | _ => none

/-! ## Markdown's code -/

/-- A fence opening a line at `i`, up to three spaces in: its scalar, its length, and the index past
it. -/
private def fenceAt? (t : PText) (i : Nat) : Option (Char × Nat × Nat) := Id.run do
  let mut j := i
  for _ in [0:3] do
    if charAt t j == ' ' then j := j + 1
  let c := charAt t j
  if !(c == '`' || c == '~') then return none
  let mut n := 0
  for _ in [j:t.size] do
    if charAt t (j + n) == c then n := n + 1 else break
  return if n ≥ 3 then some (c, n, j + n) else none

/-- rustdoc's code block attributes, which name no language: a block naming none is Rust. -/
private def rustAttrs : List String :=
  ["rust", "ignore", "should_panic", "no_run", "compile_fail", "edition2015", "edition2018",
   "edition2021", "edition2024", "test_harness", "standalone_crate", "allow_fail", ""]

/-- A rustdoc code block's info string as its language. -/
private def rustLang (info : String) : String :=
  let words := (info.split fun c => c == ',' || c == ' ' || c == '\t').toList.map (·.toString.trimAscii.toString)
  let words := words.filter fun w => !w.startsWith "{" && !w.startsWith "ignore-"
  match words.find? (!rustAttrs.contains ·) with
  | some l => l
  | none => "rust"

/-- A rustdoc Rust block's line as it shows: a line opening on `# ` or alone `#` hidden, `##`
opening one setting `#`. -/
private def rustShown (line : String) : Option String :=
  let body := line.trimAsciiStart.toString
  if body == "#" || body.startsWith "# " then none
  else if body.startsWith "##" then
    some (String.ofList (line.toList.take (line.length - body.length)) ++ (body.drop 1).toString)
  else some line

/-- A fenced code block opening at `i`, copied as the dialect sets it, and the index past it. -/
private def fencedBlock (cx : Ctx) (t : PText) (i : Nat) (c : Char) (n : Nat) (afterFence : Nat)
    (o : Out) : Out × Nat := Id.run do
  let at_ := (t[i]?).getD default
  let infoEnd := lineEndAt t afterFence
  let info := (strOf (t.extract afterFence infoEnd)).trimAscii.toString
  let mut k := infoEnd + 1
  let mut body : Array PText := #[]
  let mut close := t.size
  for _ in [0:t.size] do
    if k > t.size then break
    let e := lineEndAt t k
    match fenceAt? t k with
    | some (c', n', after) =>
      if c' == c && n' ≥ n && (t.extract after e).all (isSpace ·.c) then
        close := e
        break
    | none => pure ()
    body := body.push (t.extract k e)
    k := e + 1
  let lang := match cx.dialect with
    | .rustdoc => rustLang info
    | .doxygen => doxLang cx info
    | .javadoc | .javadocMarkdown => if info.isEmpty then cx.lang else info
  let shown := if cx.dialect == .rustdoc && lang == "rust" then
      body.filterMap fun l => rustShown (strOf l)
    else body.map strOf
  let fence := String.ofList (List.replicate n c)
  let o := (o.endLine at_).str (fence ++ lang ++ "\n") at_
  let o := shown.foldl (fun o l => o.str (l ++ "\n") at_) o
  return (o.str fence at_, min t.size close)

/-- A code span at `i`: the index past it, `none` where its backticks never close. -/
private def codeSpanEnd? (t : PText) (i : Nat) : Option Nat := Id.run do
  let mut n := 0
  for _ in [i:t.size] do
    if charAt t (i + n) == '`' then n := n + 1 else break
  let mut k := i + n
  for _ in [k:t.size] do
    if k ≥ t.size then break
    if charAt t k == '\n' && (t.extract (k + 1) (lineEndAt t (k + 1))).all (isBlank ·.c) then return none
    if charAt t k == '`' then
      let mut m := 0
      for _ in [k:t.size] do
        if charAt t (k + m) == '`' then m := m + 1 else break
      if m == n then return some (k + m)
      k := k + m
    else k := k + 1
  return none

/-- Whether a link's destination is a Rust path rustdoc resolves to an item, not a URL. -/
private def rustPath (dest : String) : Bool :=
  let d := (dest.dropEndWhile fun c => c == '(' || c == ')' || c == '!').toString
  !d.isEmpty && !d.contains '/' && !d.contains '.' && !d.startsWith "#" &&
    (d.front.isAlpha || d.front == '_') &&
    d.all fun c => c.isAlphanum || c == '_' || c == ':' || c == '<' || c == '>' || c == '@'

/-- A bracket's text at `i`, its brackets balanced, and the index past its `]`. -/
private def bracketAt? (t : PText) (i : Nat) : Option (PText × Nat) := Id.run do
  if charAt t i != '[' then return none
  let mut depth := 0
  for k in [i + 1:t.size] do
    match charAt t k with
    | '[' => depth := depth + 1
    | ']' =>
      if depth == 0 then return some (t.extract (i + 1) k, k + 1)
      depth := depth - 1
    | '\n' => if charAt t (k + 1) == '\n' then return none
    | _ => pure ()
  return none

/-- Whether a Javadoc reference names a program element: a qualified name, a member after `#`, its
parameters in parentheses, and no URL. -/
private def javaRef (r : String) : Bool :=
  !r.isEmpty && !r.contains '/' && !r.endsWith ".html" && (r.front.isAlpha || r.front == '#') &&
    r.all fun c => c.isAlphanum || "_.#(),[]<>$ ".toList.contains c

/-- Whether a link's destination names a program element in the dialect, not a URL. -/
private def elementPath (d : Dialect) (dest : String) : Bool :=
  if d == .rustdoc then rustPath dest else javaRef dest

/-- Whether a bracket's text reads as a program element's name rather than prose: code, a path, or
a member. -/
private def codeLike (d : Dialect) (label : String) : Bool :=
  let bare := label.replace "`" ""
  elementPath d bare && (label.contains '`' || bare.contains "::" || bare.contains '#' ||
    (d == .javadocMarkdown && bare.contains '.' && !bare.contains ' ') ||
    (d == .rustdoc && (bare.front.isUpper || bare.endsWith "()" || bare.endsWith "!")))

/-- An intra-doc link at `i`, rustdoc's or a Javadoc markdown comment's: `[text](path)` whose
destination names an element, `[text][ref]`, `[ref][]` or `[ref]` whose reference does, none a
citation key or a definition gives a URL; its text, the reference, and the index past it. -/
private def intraDoc? (cx : Ctx) (defs items : Std.HashSet String) (t : PText) (i : Nat) :
    Option (PText × String × Nat) := do
  if i > 0 && ((charAt t (i - 1)).isAlphanum || charAt t (i - 1) == ']' || charAt t (i - 1) == '!') then
    none
  let (inner, next) ← bracketAt? t i
  let label := strOf inner
  if cx.known.contains label then none
  if charAt t next == '(' then
    let close ← findOnPara? t next ')'
    let dest := (strOf (t.extract (next + 1) close)).trimAscii.toString
    if cx.dialect == .rustdoc && elementPath cx.dialect dest then some (inner, dest, close + 1) else none
  else if charAt t next == '[' then
    let (ref, after) ← bracketAt? t next
    let key := if ref.isEmpty then label else strOf ref
    if defs.contains key.toLower || cx.known.contains key then none
    else if codeLike cx.dialect key || items.contains key.toLower then
      some (inner, key.replace "`" "", after)
    else none
  else
    if defs.contains label.toLower then none
    else if codeLike cx.dialect label || items.contains label.toLower then
      some (inner, label.replace "`" "", next)
    else none

/-- The reference definitions a markdown text gives a URL, by label lowercased; a definition whose
destination is a Rust path names an item, and is dropped. -/
private def linkDefs (d : Dialect) (t : PText) :
    Std.HashSet String × Std.HashSet Nat × Std.HashSet String := Id.run do
  let mut urls : Std.HashSet String := {}
  let mut items : Std.HashSet Nat := {}
  let mut itemLabels : Std.HashSet String := {}
  let mut i := 0
  for l in splitLines t do
    let body := dropIndent l
    if let some (inner, next) := bracketAt? body 0 then
      if charAt body next == ':' then
        let dest := (strOf (body.extract (next + 1) body.size)).trimAscii.toString
        if elementPath d dest then
          items := items.insert i
          itemLabels := itemLabels.insert (strOf inner).toLower
        else urls := urls.insert (strOf inner).toLower
    i := i + l.size
  return (urls, items, itemLabels)

/-- A line's indentation, a tab to the next column of four. -/
private def indentOf (t : PText) (i : Nat) : Nat := Id.run do
  let mut w := 0
  for k in [i:t.size] do
    match charAt t k with
    | ' ' => w := w + 1
    | '\t' => w := w + 4 - w % 4
    | _ => return w
  return w

/-- Whether the line at `i` holds only white space. -/
private def blankLine (t : PText) (i : Nat) : Bool := (t.extract i (lineEndAt t i)).all (isBlank ·.c)

/-- Whether the line at `i` opens a list item. -/
private def itemLine (t : PText) (i : Nat) : Bool :=
  let b := (dropIndent (t.extract i (lineEndAt t i))).toList.map (·.c)
  let digits := (b.takeWhile Char.isDigit).length
  b.take 2 == ['-', ' '] || b.take 2 == ['*', ' '] || b.take 2 == ['+', ' '] ||
    (digits > 0 && ((b.drop digits).take 2 == ['.', ' '] || (b.drop digits).take 2 == [')', ' ']))

/-- An indented code block opening at the line at `i`: the index past its last line that holds
text. -/
private def indentedEnd (t : PText) (i : Nat) : Nat := Id.run do
  let mut k := i
  let mut stop := lineEndAt t i
  for _ in [0:t.size] do
    if k ≥ t.size then break
    if blankLine t k then k := lineEndAt t k + 1
    else if indentOf t k ≥ 4 then
      stop := lineEndAt t k
      k := stop + 1
    else break
  return stop

/-- An indented code block's lines as the dialect sets them: rustdoc's a fenced Rust block, its
hidden lines dropped, another's as written. -/
private def indentedBlock (cx : Ctx) (t : PText) (i stop : Nat) (o : Out) : Out :=
  let at_ := (t[i]?).getD default
  if cx.dialect != .rustdoc then (t.extract i stop).foldl (fun o q => o.put q.c q) o else
  -- A line past the block's four columns of indentation, a tab to the next column of four.
  let cut (l : List Char) : List Char := Id.run do
    let mut w := 0
    let mut k := 0
    for c in l do
      if w ≥ 4 then break
      if c == ' ' then
        w := w + 1
        k := k + 1
      else if c == '\t' then
        w := w + 4 - w % 4
        k := k + 1
      else break
    let rest := l.drop k
    return List.append (List.replicate (w - min w 4) ' ') rest
  let lines := ((strOf (t.extract i stop)).splitOn "\n").map fun l => String.ofList (cut l.toList)
  let shown := lines.filterMap rustShown
  fenced o "rust" ("\n".intercalate shown) at_

/-! ## Walking a text -/

/-- The text walked into markdown under the dialect. -/
private def walk (cx : Ctx) (t : PText) (o : Out) (w : Walk := {}) : Out := Id.run do
  let (defs, itemDefs, itemLabels) := if cx.dialect == .rustdoc || cx.dialect == .javadocMarkdown then
      linkDefs cx.dialect t else ({}, {}, {})
  let mut o := o
  let mut w := w
  let mut i := 0
  -- Whether the line before is blank, and whether a list item's content runs on.
  let mut afterBlank := true
  let mut inList := false
  for _ in [0:t.size + 1] do
    if i ≥ t.size then break
    let p := (t[i]?).getD default
    let lineStart := i == 0 || charAt t (i - 1) == '\n'
    if cx.dialect.markdown && lineStart then
      let blank := blankLine t i
      if !blank then
        if itemLine t i then inList := true
        else if indentOf t i == 0 then inList := false
      if !blank && afterBlank && !inList && indentOf t i ≥ 4 then
        let stop := indentedEnd t i
        o := indentedBlock cx t i stop o
        i := stop
        afterBlank := false
        continue
      afterBlank := blank
    if lineStart && itemDefs.contains i then
      let line := dropIndent (t.extract i (lineEndAt t i))
      let dest := ((strOf line).splitOn "]:").drop 1 |> ":".intercalate |>.trimAscii.toString
      o := o.lose (.unlinked dest) p
      i := lineEndAt t i + 1
      continue
    if cx.dialect.markdown && lineStart then
      if let some (c, n, after) := fenceAt? t i then
        let (o', next) := fencedBlock cx t i c n after o
        o := o'
        i := next
        continue
    if cx.dialect.markdown && p.c == '`' then
      match codeSpanEnd? t i with
      | some e =>
        o := (t.extract i e).foldl (fun o q => o.put q.c q) o
        i := e
        continue
      | none => pure ()
    if cx.dialect == .doxygen then
      if let some (body, display, next) := doxFormula? t i then
        o := (if display then fenced (o.lose (.unread "\\f") p) "text" body p
          else codeSpan (o.lose (.unread "\\f") p) body p)
        i := next
        continue
      if p.c == '\\' || p.c == '@' then
        let esc := doxEscapes.find? fun e => litAt t (i + 1) e
        if (p.c == '\\' && (litAt t (i + 1) "::" || litAt t (i + 1) "---" || litAt t (i + 1) "--")) then
          let n := if litAt t (i + 1) "---" then 3 else 2
          o := (t.extract (i + 1) (i + 1 + n)).foldl (fun o q => o.put q.c q) o
          i := i + 1 + n
          continue
        if let some e := esc then
          o := literal o { p with c := e.front }
          i := i + 2
          continue
        if let some (cmd, j) := doxCommandAt? t i then
          let (o', w', next) := doxStep cx t i j cmd w o
          o := o'
          w := w'
          i := next
          continue
    if cx.dialect == .javadoc || cx.dialect == .javadocMarkdown then
      if let some (name, body, next) := inlineTagAt? t i then
        o := inlineTag cx name body p o
        i := next
        continue
    if cx.dialect == .javadoc && p.c == '[' then
      -- A bracket holding a key the page cites by is the citation doc-gen4's reading takes.
      if let some (inner, next) := bracketAt? t i then
        if cx.known.contains (strOf inner) then
          o := (t.extract i next).foldl (fun o q => o.put q.c q) o
          i := next
          continue
    if (cx.dialect == .rustdoc || cx.dialect == .javadocMarkdown) && p.c == '[' then
      if let some (inner, path, next) := intraDoc? cx defs itemLabels t i then
        o := o.lose (.unlinked path) p
        o := if cx.dialect == .javadocMarkdown && !(strOf inner).contains '`' then codeSpan o (strOf inner) p
          else inner.foldl (fun o q => o.put q.c q) o
        i := next
        continue
    if p.c == '<' then
      if let some tag := tagAt? t i then
        let (o', w', next) := tagStep cx t i tag w o
        o := o'
        w := w'
        i := next
        continue
    if p.c == '&' then
      if let some (_, next) := entityAt? t i then
        o := (t.extract i next).foldl (fun o q => o.put q.c q) o
        i := next
        continue
    if p.c == '\n' then
      let blankNext := Id.run do
        let mut k := i + 1
        for _ in [k:t.size] do
          if isSpace (charAt t k) then k := k + 1 else break
        return charAt t k == '\n' || k ≥ t.size
      if cx.dialect.markdown && blankNext then w := w.broken
      if w.joined && !(cx.dialect.markdown && blankNext) then
        o := if o.last? 0 == some ' ' then o else o.put ' ' p
      else if w.quoted then o := o.str "\n> " p
      else if cx.dialect == .javadoc then
        o := if o.last? 0 == some ' ' || o.atLineStart then o else o.put ' ' p
      else o := o.put '\n' p
      i := i + 1
      if cx.dialect == .javadoc || w.joined then
        for _ in [i:t.size] do
          if isSpace (charAt t i) then i := i + 1 else break
      continue
    o := if cx.dialect == .javadoc then
        (if isSpace p.c then (if o.last? 0 == some ' ' || o.atLineStart then o else o.put ' ' p)
          else literal o p)
      else o.put p.c p
    i := i + 1
  return o

/-! ## Javadoc's block tags -/

/-- A block tag: its name, its argument where its label lists one, its body and where it stands. -/
private structure BlockTag where
  name : String
  arg : PText
  body : PText
  at_ : PChar

/-- The standard doclet's sections for its block tags, in its order: the label, and whether the
tag names an argument its entry opens on. -/
private def javadocSections : List (String × String × Bool) :=
  [("deprecated", "Deprecated", false), ("typeparam", "Type Parameters", true),
   ("param", "Parameters", true), ("return", "Returns", false), ("throws", "Throws", true),
   ("exception", "Throws", true), ("apiNote", "API Note", false),
   ("implSpec", "Implementation Requirements", false), ("implNote", "Implementation Note", false),
   ("since", "Since", false), ("version", "Version", false), ("author", "Author", false),
   ("see", "See Also", false), ("uses", "Uses", true), ("provides", "Provides", true)]

/-- A line opening, past its spaces, with `@` and a letter: a block tag's. -/
private def tagLine? (l : PText) : Option (String × PText × PChar) := Id.run do
  let b := dropIndent l
  if charAt b 0 != '@' || !(charAt b 1).isAlpha then return none
  let mut k := 1
  let mut name := ""
  for _ in [1:b.size] do
    let c := charAt b k
    if c.isAlphanum then
      name := name.push c
      k := k + 1
    else break
  return some (name, b.extract k b.size, (b[0]?).getD default)

/-- A Javadoc comment's main description and its block tags. -/
private def javadocParts (t : PText) (fences : Bool) : PText × Array BlockTag := Id.run do
  let mut main : PText := #[]
  let mut tags : Array BlockTag := #[]
  let mut open? : Option BlockTag := none
  let mut body : PText := #[]
  let mut inPre := false
  let mut fence : Option (Char × Nat) := none
  let mut indented := false
  let mut prevBlank := true
  for l in splitLines t do
    let s := (strOf l).toLower
    let opens := (s.splitOn "<pre").length - 1
    let closes := (s.splitOn "</pre").length - 1
    let blank := l.all (isBlank ·.c)
    if fences && !blank then
      if !indented && prevBlank && indentOf l 0 ≥ 4 then indented := true
      else if indented && indentOf l 0 < 4 then indented := false
    prevBlank := blank
    match (if inPre || fence.isSome || indented then none else tagLine? l) with
    | some (name, rest, at_) =>
      if let some tag := open? then tags := tags.push { tag with body }
      open? := some ⟨name, #[], #[], at_⟩
      body := rest
    | none => if open?.isSome then body := body ++ l else main := main ++ l
    inPre := (inPre || opens > closes) && !(closes > opens)
    if fences then
      match fence, fenceAt? l 0 with
      | none, some (c, n, _) => fence := some (c, n)
      | some (c, n), some (c', n', after) =>
        if c' == c && n' ≥ n && (l.extract after l.size).all (isBlank ·.c) then fence := none
      | _, none => pure ()
  if let some tag := open? then tags := tags.push { tag with body }
  let entries := tags.map fun tag =>
    if (javadocSections.find? (·.1 == tag.name)).any (·.2.2) then
      let b := tag.body.extract ((tag.body.findIdx? (!isBlank ·.c)).getD 0) tag.body.size
      let (arg, rest) := splitRef b
      { tag with arg, body := rest }
    else tag
  return (main, entries)

/-- A Javadoc comment lowered: its deprecation, its main description, then its block tags' sections
in the standard doclet's order; a tag the doclet does not list named. -/
private def javadoc (cx : Ctx) (t : PText) : Out := Id.run do
  let (main, tags) := javadocParts t (cx.dialect == .javadocMarkdown)
  let at0 := (t[0]?).getD default
  let mut o : Out := {}
  let deprecated := tags.filter (·.name == "deprecated")
  for d in deprecated do
    o := walk cx d.body ((o.para d.at_).str "**Deprecated.** " d.at_)
  o := walk cx main (o.para at0)
  let mut seen : List String := []
  for (name, label, listed) in javadocSections do
    if name == "deprecated" || seen.contains label then continue
    let mine := tags.filter fun tag =>
      tag.name == name || ((javadocSections.find? (·.1 == tag.name)).map (·.2.1)) == some label
    let mine := if name == "param" then mine.filter (charAt ·.arg 0 != '<')
      else if name == "typeparam" then
        tags.filter fun tag => tag.name == "param" && charAt tag.arg 0 == '<'
      else mine
    if mine.isEmpty then continue
    seen := label :: seen
    let first := (mine[0]?.map (·.at_)).getD at0
    o := (o.para first).str ("**" ++ label ++ ":**") first
    if listed then
      o := o.para first
      for tag in mine do
        let arg := ((strOf tag.arg).dropWhile (· == '<')).dropEndWhile (· == '>') |>.toString
        o := codeSpan ((o.endLine tag.at_).str "- " tag.at_) arg tag.at_
        o := walk cx tag.body (o.str " – " tag.at_) { oneLine := true }
    else
      for tag in mine, k in [0:mine.size] do
        let o' := if k == 0 then o.str " " tag.at_ else o.trimEnd.str ", " tag.at_
        o := walkRef cx name tag.body o' tag.at_
  for tag in tags do
    unless (javadocSections.any (·.1 == tag.name)) do
      o := o.lose (.unread ("@" ++ tag.name)) tag.at_
      if tag.name != "hidden" && tag.name != "serial" && tag.name != "serialData" &&
          tag.name != "serialField" then
        o := walk cx tag.body (((o.para tag.at_).str ("**@" ++ tag.name ++ "**") tag.at_).str " " tag.at_)
  return o
where
  /-- A `@see`'s reference set as code and named, its string or link as written; another tag's
  body walked. -/
  walkRef (cx : Ctx) (name : String) (body : PText) (o : Out) (at_ : PChar) : Out :=
    let b := body.extract ((body.findIdx? (!isBlank ·.c)).getD 0) body.size
    if name == "see" && !(charAt b 0 == '"' || charAt b 0 == '<') && !b.isEmpty then
      let (ref, label) := splitRef b
      let o := o.lose (.unlinked (strOf ref)) at_
      if label.isEmpty then codeSpan o (refShown (strOf ref)) at_ else literalLine o label
    else walk cx body o { oneLine := true }

/-! ## The readers -/

/-- A markup's dialect, where it has a reader of its own. -/
public def dialectOf : Ir.DocMarkup → Option Dialect
  | .javadoc => some .javadoc
  | .javadocMarkdown => some .javadocMarkdown
  | .doxygen => some .doxygen
  | .rustdoc => some .rustdoc
  | .markdown | .docstring => none

/-- A comment's text lowered into markdown under its dialect, code blocks set in `lang` where they
name none, citing by `known`. -/
public def lower (d : Dialect) (lang : String) (known : Std.HashSet String) (t : PText) : Out :=
  let cx : Ctx := { dialect := d, lang, known }
  let o := match d with
    | .javadoc | .javadocMarkdown => javadoc cx t
    | .doxygen | .rustdoc => walk cx t {}
  let once : Array Loss := o.losses.foldl (init := #[]) fun acc l =>
    if acc.any (·.lost == l.lost) then acc else acc.push l
  let text := if d == .javadoc then trimLines o.text else o.text
  { text, losses := once }
where
  /-- Each line's trailing spaces dropped, which markdown would read as a hard break. -/
  trimLines (t : PText) : PText := Id.run do
    let mut out : PText := Array.mkEmpty t.size
    let mut held : PText := #[]
    for p in t do
      if p.c == ' ' then held := held.push p
      else if p.c == '\n' then
        out := out.push p
        held := #[]
      else
        out := out ++ held |>.push p
        held := #[]
    return out

/-- Whether a Doxygen comment's text holds `\file`, which makes it the file's description. -/
public def describesFile (text : List Char) : Bool :=
  let t : PText := text.toArray.map fun c => ⟨c, 0, 0⟩
  (List.range t.size).any fun i =>
    match doxCommandAt? t i with
    | some ("file", j) => !(charAt t j).isAlpha
    | _ => false

end LeanTex.Core.DocMarkup
