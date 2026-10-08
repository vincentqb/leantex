module

/-!
A bounded native listing lexer. It classifies source; it neither parses nor
executes the language. Lean 4 and Python are the supported lexical subsets, following
the Lean reference's lexical structure and Python's lexical analysis reference.
Unrecognized names stay ordinary text. In particular, Python formatted
string contents are one string token, not a second parser for interpolation.

Classes are Pygments token types (`Kind`), the vocabulary the installed
provider answers in too, so one style table paints both. A Lean proof hole
is `Generic.Error`, as Pygments' Lean 4 lexer classifies the two hole
tactics (pygments/lexers/lean.py).

The scanner copies every source scalar once, using lookahead only at token
boundaries. Tokens retain their exact text, including whitespace. Newlines split
the result into lines without changing the lexical state: a nested Lean block
comment or Python triple-quoted string can span any number of lines.
-/
namespace LeanTex.Core.ListingHighlight

public inductive Language where
  | lean | python
  deriving Repr, BEq, DecidableEq, Inhabited

public def language? (name : String) : Option Language :=
  match name.toLower with
  | "lean" | "lean4" => some .lean
  | "python" | "python3" | "py" => some .python
  | _ => none

/-- A Pygments token type (https://pygments.org/docs/tokens/): its dotted
path below the root `Token` (`Keyword.Type`), `""` for the root itself. -/
public structure Kind where
  path : String
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace Kind

public def text : Kind := ⟨"Text"⟩
public def keyword : Kind := ⟨"Keyword"⟩
public def string : Kind := ⟨"Literal.String"⟩
public def number : Kind := ⟨"Literal.Number"⟩
public def comment : Kind := ⟨"Comment"⟩
public def nameBuiltin : Kind := ⟨"Name.Builtin"⟩
public def nameFunction : Kind := ⟨"Name.Function"⟩
public def operator : Kind := ⟨"Operator"⟩
public def genericError : Kind := ⟨"Generic.Error"⟩

/-- The types from the top level down to `k` itself, the root excluded: the
order Pygments' LaTeX formatter applies their styles in
(pygments/formatters/latex.py, `format_unencoded`). -/
public def chain (k : Kind) : List Kind :=
  if k.path.isEmpty then [] else
  let parts := k.path.splitOn "."
  (List.range parts.length).map fun i => ⟨".".intercalate (parts.take (i + 1))⟩

/-- A provider's class name as a type: `Token` or a dotted descendant, each
part an ASCII capital and then letters, digits or `_`, as Pygments creates
subtypes (pygments/token.py, `_TokenType.__getattr__`). Anything else is
ordinary text, so no class name becomes paint it does not name. -/
public def ofPygments (name : String) : Kind :=
  let parts := name.splitOn "."
  let part (p : String) : Bool := match p.toList with
    | c :: cs => 'A' ≤ c && c ≤ 'Z' && cs.all fun d => d.isAlphanum || d == '_'
    | [] => false
  if parts.head? == some "Token" && parts.length ≤ 8 && name.length ≤ 128 &&
      parts.tail.all part then ⟨".".intercalate parts.tail⟩
  else text

end Kind

public structure Token where
  kind : Kind := .text
  text : String
  deriving Repr, BEq, DecidableEq, Inhabited

@[expose] public def lineText (tokens : Array Token) : String :=
  tokens.foldl (fun s t => s ++ t.text) ""

private def charAt (chars : Array Char) (i : Nat) : Char := chars[i]?.getD '\x00'

private def slice (chars : Array Char) (start stop : Nat) : String :=
  String.ofList (chars.extract start stop).toList

private def scanWhile (chars : Array Char) (start : Nat) (p : Char → Bool) : Nat :=
  Id.run do
    let mut stop := start
    for h : i in [start:chars.size] do
      if !p chars[i] then break
      stop := i + 1
    return stop

private def identStart (c : Char) : Bool :=
  c.isAlpha || c == '_' ||
    (c.toNat ≥ 128 && !c.isWhitespace &&
      !("∀∃→←↔⇒⇔:=+-*/<>≤≥≠∧∨¬∈∉∪∩⟨⟩«»".contains c))

private def identRest (lang : Language) (c : Char) : Bool :=
  identStart c || c.isDigit || (lang == .lean && c == '\'')

private def keywords : Language → List String
  | .lean =>
    ["abbrev", "axiom", "by", "class", "def", "deriving", "do", "else",
     "end", "example", "export", "extends", "for", "fun", "have", "if",
     "import", "in", "inductive", "instance", "let", "macro", "match",
     "mutual", "namespace", "noncomputable", "opaque", "open", "partial",
     "private", "protected", "return", "section", "set_option", "structure",
     "syntax", "termination_by", "then", "theorem", "universe", "variable",
     "where", "with", "simp", "simpa", "exact", "apply", "intro",
     "intros", "rw", "rfl", "constructor", "cases", "induction", "decide"]
  | .python =>
    ["False", "None", "True", "and", "as", "assert", "async", "await",
     "break", "class", "continue", "def", "del", "elif", "else", "except",
     "finally", "for", "from", "global", "if", "import", "in", "is",
     "lambda", "nonlocal", "not", "or", "pass", "raise", "return", "try",
     "while", "with", "yield"]

private def builtins : Language → List String
  | .lean =>
    ["Type", "Prop", "Sort", "Nat", "Int", "Float", "Bool", "String",
     "Char", "List", "Array", "Option", "Except", "IO", "Unit", "true", "false"]
  | .python =>
    ["abs", "all", "any", "bool", "bytes", "dict", "enumerate", "filter",
     "float", "int", "isinstance", "len", "list", "map", "max", "min",
     "object", "open", "print", "range", "repr", "reversed", "set",
     "sorted", "str", "sum", "super", "tuple", "type", "zip"]

private def declaresName (lang : Language) (s : String) : Bool :=
  match lang with
  | .lean => ["def", "abbrev", "theorem", "axiom", "opaque", "structure",
      "class", "inductive"].contains s
  | .python => s == "def" || s == "class"

/-- Find a closing quote, accounting for backslash escapes and triple quotes.
A single-quoted Python string stops before an unescaped newline; an unfinished
triple string or Lean string keeps its remaining source as a string token. -/
private def stringEnd (chars : Array Char) (start : Nat) (quote : Char)
    (triple multiline : Bool) : Nat := Id.run do
  let width := if triple then 3 else 1
  let mut escaped := false
  for h : i in [start + width:chars.size] do
    let c := chars[i]
    if escaped then escaped := false
    else if c == '\\' then escaped := true
    else if !multiline && c == '\n' then return i
    else if c == quote &&
        (!triple || (charAt chars (i + 1) == quote && charAt chars (i + 2) == quote)) then
      return i + width
  return chars.size

private def blockCommentEnd (chars : Array Char) (start : Nat) : Nat := Id.run do
  let mut depth := 1
  let mut skip := start + 2
  for i in [start + 2:chars.size] do
    if i < skip then continue
    if charAt chars i == '/' && charAt chars (i + 1) == '-' then
      depth := depth + 1
      skip := i + 2
    else if charAt chars i == '-' && charAt chars (i + 1) == '/' then
      depth := depth - 1
      if depth == 0 then return i + 2
      skip := i + 2
  return chars.size

private def numberEnd (lang : Language) (chars : Array Char) (start : Nat) : Nat := Id.run do
  let digit (c : Char) := c.isDigit || c == '_'
  if charAt chars start == '0' then
    let base := (charAt chars (start + 1)).toLower
    if base == 'x' || base == 'o' || base == 'b' then
      let allowed (c : Char) := c == '_' || (if base == 'x' then c.isHexDigit
        else if base == 'o' then '0' ≤ c && c ≤ '7' else c == '0' || c == '1')
      return scanWhile chars (start + 2) allowed
  let mut stop := scanWhile chars start digit
  if charAt chars stop == '.' && (charAt chars (stop + 1)).isDigit then
    stop := scanWhile chars (stop + 1) digit
  if (charAt chars stop).toLower == 'e' then
    let after := stop + 1
    let after := if charAt chars after == '+' || charAt chars after == '-' then after + 1 else after
    if (charAt chars after).isDigit then stop := scanWhile chars after digit
  if lang == .python && (charAt chars stop).toLower == 'j' then stop := stop + 1
  return stop

/-- One token boundary. The returned end is exclusive. Lookahead never changes
the source; the outer traversal copies each visited scalar exactly once. -/
private def tokenAt (lang : Language) (chars : Array Char) (i : Nat)
    (expectName : Bool) : Kind × Nat × Bool := Id.run do
  let c := charAt chars i
  let next := charAt chars (i + 1)
  if (lang == .python && c == '#') || (lang == .lean && c == '-' && next == '-') then
    return (Kind.comment, scanWhile chars i (· != '\n'), false)
  if lang == .lean && c == '/' && next == '-' then
    return (Kind.comment, blockCommentEnd chars i, false)
  if c == '"' || (lang == .python && c == '\'') then
    let triple := lang == .python && next == c && charAt chars (i + 2) == c
    return (.string, stringEnd chars i c triple (triple || lang == .lean), false)
  -- A Lean character literal needs its closing quote. Apostrophes inside names
  -- are consumed by identRest, so `value'` is never a string.
  if lang == .lean && c == '\'' then
    let stop := stringEnd chars i c false false
    if stop ≤ i + 4 && stop ≤ chars.size && charAt chars (stop - 1) == '\'' then
      return (.string, stop, false)
  if lang == .lean && c == '«' then
    let stop := scanWhile chars (i + 1) (· != '»')
    return (Kind.text, min chars.size (stop + 1), false)
  if c.isDigit || (c == '.' && next.isDigit) then
    return (.number, numberEnd lang chars i, false)
  if identStart c || (lang == .lean && c == '#' && identStart next) then
    let stop := scanWhile chars (i + 1) (identRest lang)
    let word := slice chars i stop
    if lang == .python &&
        ["r", "u", "b", "f", "br", "rb", "fr", "rf"].contains word.toLower &&
        (charAt chars stop == '"' || charAt chars stop == '\'') then
      let q := charAt chars stop
      let triple := charAt chars (stop + 1) == q && charAt chars (stop + 2) == q
      return (.string, stringEnd chars stop q triple triple, false)
    let kind := if lang == .lean && (word == "sorry" || word == "admit") then Kind.genericError
      else if (keywords lang).contains word || (lang == .lean && c == '#') then .keyword
      else if expectName then .nameFunction
      else if (builtins lang).contains word then .nameBuiltin else .text
    return (kind, stop, declaresName lang word)
  if "=:+-*/<>!%&|^~∀∃→←↔⇒⇔≤≥≠∧∨¬∈∉∪∩".contains c then
    return (.operator, i + 1, false)
  return (Kind.text, i + 1, expectName && c.isWhitespace)

/-- Classify normalized listing lines. Newlines remain line boundaries and
adjacent scalars of the same class coalesce, including spaces within comments
and strings. The shared IR reader separately certifies text preservation even
for manually constructed or stale metadata. -/
public def tokenize (lang : Language) (lines : Array String) : Array (Array Token) := Id.run do
  if lines.isEmpty then return #[]
  let chars := (String.intercalate "\n" lines.toList).toList.toArray
  let mut result : Array (Array Token) := #[]
  let mut line : Array Token := #[]
  let mut text := ""
  let mut kind := Kind.text
  let mut stop := 0
  let mut expectName := false
  for h : i in [:chars.size] do
    let c := chars[i]
    let (nextKind, nextStop, nextExpect) :=
      if i < stop then (kind, stop, expectName) else tokenAt lang chars i expectName
    if nextKind != kind || c == '\n' then
      unless text.isEmpty do line := line.push { kind, text }
      text := ""
    kind := nextKind
    stop := nextStop
    expectName := nextExpect
    if c == '\n' then
      result := result.push line
      line := #[]
    else text := text.push c
  unless text.isEmpty do line := line.push { kind, text }
  return result.push line

end LeanTex.Core.ListingHighlight
