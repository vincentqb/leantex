module

public import LeanTex.Core.Highlight

/-! Listing classification for the elaborator: a native lexer's token stream as one token array
per source line, classes being Pygments token types. -/
namespace LeanTex.Core.ListingHighlight

/-- A language with a native lexer. -/
public abbrev Language := Highlight.Lexer

public def language? (name : String) : Option Language := Highlight.Lexer.ofName? name

/-- A Pygments token type: its dotted path below the root `Token`, `""` for the root itself. -/
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

/-- The types from the top level down to `k`, the root excluded, the order Pygments' LaTeX
formatter applies their styles in. -/
public def chain (k : Kind) : List Kind :=
  if k.path.isEmpty then [] else
  let parts := k.path.splitOn "."
  (List.range parts.length).map fun i => ⟨".".intercalate (parts.take (i + 1))⟩

/-- A provider's class name as a type (pygments/token.py); anything else is ordinary text. -/
public def ofPygments (name : String) : Kind :=
  let parts := name.splitOn "."
  let part (p : String) : Bool := match p.toList with
    | c :: cs => 'A' ≤ c && c ≤ 'Z' && cs.all fun d => d.isAlphanum || d == '_'
    | [] => false
  if parts.head? == some "Token" && parts.length ≤ 8 && name.length ≤ 128 &&
      parts.tail.all part then ⟨".".intercalate parts.tail⟩
  else text

/-- Pygments' short names for its standard types (pygments/token.py,
`STANDARD_TYPES`), each beside the type's path below `Token`. -/
private def standardClasses : List (String × String) :=
  [("", ""), ("Text", ""), ("Text.Whitespace", "w"), ("Escape", "esc"), ("Error", "err"),
   ("Other", "x"),
   ("Keyword", "k"), ("Keyword.Constant", "kc"), ("Keyword.Declaration", "kd"),
   ("Keyword.Namespace", "kn"), ("Keyword.Pseudo", "kp"), ("Keyword.Reserved", "kr"),
   ("Keyword.Type", "kt"),
   ("Name", "n"), ("Name.Attribute", "na"), ("Name.Builtin", "nb"),
   ("Name.Builtin.Pseudo", "bp"), ("Name.Class", "nc"), ("Name.Constant", "no"),
   ("Name.Decorator", "nd"), ("Name.Entity", "ni"), ("Name.Exception", "ne"),
   ("Name.Function", "nf"), ("Name.Function.Magic", "fm"), ("Name.Property", "py"),
   ("Name.Label", "nl"), ("Name.Namespace", "nn"), ("Name.Other", "nx"), ("Name.Tag", "nt"),
   ("Name.Variable", "nv"), ("Name.Variable.Class", "vc"), ("Name.Variable.Global", "vg"),
   ("Name.Variable.Instance", "vi"), ("Name.Variable.Magic", "vm"),
   ("Literal", "l"), ("Literal.Date", "ld"),
   ("Literal.String", "s"), ("Literal.String.Affix", "sa"), ("Literal.String.Backtick", "sb"),
   ("Literal.String.Char", "sc"), ("Literal.String.Delimiter", "dl"),
   ("Literal.String.Doc", "sd"), ("Literal.String.Double", "s2"),
   ("Literal.String.Escape", "se"), ("Literal.String.Heredoc", "sh"),
   ("Literal.String.Interpol", "si"), ("Literal.String.Other", "sx"),
   ("Literal.String.Regex", "sr"), ("Literal.String.Single", "s1"),
   ("Literal.String.Symbol", "ss"),
   ("Literal.Number", "m"), ("Literal.Number.Bin", "mb"), ("Literal.Number.Float", "mf"),
   ("Literal.Number.Hex", "mh"), ("Literal.Number.Integer", "mi"),
   ("Literal.Number.Integer.Long", "il"), ("Literal.Number.Oct", "mo"),
   ("Operator", "o"), ("Operator.Word", "ow"), ("Punctuation", "p"),
   ("Punctuation.Marker", "pm"),
   ("Comment", "c"), ("Comment.Hashbang", "ch"), ("Comment.Multiline", "cm"),
   ("Comment.Preproc", "cp"), ("Comment.PreprocFile", "cpf"), ("Comment.Single", "c1"),
   ("Comment.Special", "cs"),
   ("Generic", "g"), ("Generic.Deleted", "gd"), ("Generic.Emph", "ge"), ("Generic.Error", "gr"),
   ("Generic.Heading", "gh"), ("Generic.Inserted", "gi"), ("Generic.Output", "go"),
   ("Generic.Prompt", "gp"), ("Generic.Strong", "gs"), ("Generic.Subheading", "gu"),
   ("Generic.EmphStrong", "ges"), ("Generic.Traceback", "gt")]

/-- A type's Pygments class as its HTML formatter names it (`_get_ttype_class`); `""` for plain
text. -/
public def cssClass (k : Kind) : String :=
  let parts := if k.path.isEmpty then [] else k.path.splitOn "."
  let rec up : Nat → List String → String × List String
    | 0, rest => ("", rest)
    | m + 1, rest =>
      match standardClasses.lookup (".".intercalate (parts.take (m + 1))) with
      | some c => (c, rest)
      | none => up m ((parts.getD m "") :: rest)
  let (c, rest) := up parts.length []
  c ++ String.join (rest.map ("-" ++ ·))

end Kind

public structure Token where
  kind : Kind := .text
  text : String
  deriving Repr, BEq, DecidableEq, Inhabited

@[expose] public def lineText (tokens : Array Token) : String :=
  tokens.foldl (fun s t => s ++ t.text) ""

/-- One line's runs: each scalar takes the type `kinds` holds at its
position, and adjacent scalars of one type share a token. -/
private def runsGo (kinds : Array String) : Nat → List Char → String → String →
    Array Token → Array Token
  | _, [], kind, cur, acc => if cur.isEmpty then acc else acc.push { kind := ⟨kind⟩, text := cur }
  | i, c :: cs, kind, cur, acc =>
    let k := kinds.getD i Highlight.Ty.text
    if cur.isEmpty || k == kind then runsGo kinds (i + 1) cs k (cur.push c) acc
    else runsGo kinds (i + 1) cs k (String.singleton c) (acc.push { kind := ⟨kind⟩, text := cur })

private theorem lineText_push (acc : Array Token) (t : Token) :
    lineText (acc.push t) = lineText acc ++ t.text := by
  simp [lineText]

private theorem runsGo_lineText (kinds : Array String) (cs : List Char) :
    ∀ (i : Nat) (kind cur : String) (acc : Array Token),
      lineText (runsGo kinds i cs kind cur acc) = lineText acc ++ cur ++ String.ofList cs := by
  induction cs with
  | nil =>
    intro i kind cur acc
    simp only [runsGo]
    split
    · rename_i h
      simp [String.isEmpty_iff.mp h]
    · simp [lineText_push]
  | cons c cs ih =>
    intro i kind cur acc
    simp only [runsGo]
    split
    · rw [ih, String.ofList_cons, String.push_eq_append]
      simp only [String.append_assoc]
    · rw [ih, lineText_push, String.ofList_cons]
      simp only [String.append_assoc]

private def runs (kinds : Array String) (base : Nat) (line : String) : Array Token :=
  runsGo kinds base line.toList "" "" #[]

private theorem runs_lineText (kinds : Array String) (base : Nat) (line : String) :
    lineText (runs kinds base line) = line := by
  rw [runs, runsGo_lineText]
  simp [lineText]

/-- Where each line starts in the lexed text, a newline after each. -/
private def lineBases (lines : Array String) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty lines.size
  let mut at_ := 0
  for line in lines do
    out := out.push at_
    at_ := at_ + line.length + 1
  return out

/-- Classify normalized listing lines, lexed joined with one trailing newline. -/
public def tokenize (lang : Language) (lines : Array String) : Array (Array Token) :=
  let src := Highlight.Src.ofString (String.intercalate "\n" lines.toList ++ "\n")
  let kinds := Highlight.kindsOf src.size (Highlight.lex lang src)
  let bases := lineBases lines
  lines.mapIdx fun k line => runs kinds (bases[k]?.getD 0) line

public theorem tokenize_source_exact (lang : Language) (lines : Array String) :
    (tokenize lang lines).map lineText = lines := by
  apply Array.ext
  · simp [tokenize]
  · intro i _ _
    simp [tokenize, runs_lineText]

end LeanTex.Core.ListingHighlight
