module

public import LeanTex.Core.Highlight

/-!
Listing classification for the elaborator: a native lexer's token stream
(`Highlight`, Pygments' own lexers mirrored rule for rule) as one token
array per source line. Classes are Pygments token types (`Kind`), the
vocabulary the installed provider answers in too, so one style table paints
both, and a language with no native lexer reaches the provider instead.

A line's tokens are its scalars, each typed by the stream at its position
and adjacent scalars of one type in one token: `tokenize_source_exact`
holds every line's text whatever the stream says.
-/
namespace LeanTex.Core.ListingHighlight

/-- A language with a native lexer. -/
public abbrev Language := Highlight.Lexer

public def language? (name : String) : Option Language := Highlight.Lexer.ofName? name

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

/-- Classify normalized listing lines: the lexer reads them joined, with
the one trailing newline the provider adds too, so a rule that ends at a
newline also types the last line. -/
public def tokenize (lang : Language) (lines : Array String) : Array (Array Token) :=
  let src := Highlight.Src.ofString (String.intercalate "\n" lines.toList ++ "\n")
  let kinds := Highlight.kindsOf src.size (Highlight.lex lang src)
  let bases := lineBases lines
  lines.mapIdx fun k line => runs kinds (bases[k]?.getD 0) line

/-- Classification keeps every line's text exactly, for any lexer and any
lines: the token stream decides types, never text. -/
public theorem tokenize_source_exact (lang : Language) (lines : Array String) :
    (tokenize lang lines).map lineText = lines := by
  apply Array.ext
  · simp [tokenize]
  · intro i _ _
    simp [tokenize, runs_lineText]

end LeanTex.Core.ListingHighlight
