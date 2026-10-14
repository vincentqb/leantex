module

public import LeanTex.Core.Highlight.Scan
import LeanTex.Core.Highlight.Lean4
import LeanTex.Core.Highlight.Python
import LeanTex.Core.Highlight.Bash
import LeanTex.Core.Highlight.Console
import LeanTex.Core.PygmentsLexData

/-! The native listing lexers: Pygments' own for the languages documents write, mirrored rule for
rule from one release (`PygmentsLexData.pygmentsVersion`) under the departures
testdata/highlight/pygments-departures.json declares, with no Python on the render path. -/
namespace LeanTex.Core.Highlight

public inductive Lexer where
  | lean4 | python | bash | console | text
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

public def Lexer.all : List Lexer := [.lean4, .python, .bash, .console, .text]

/-- `lean` names Lean 4 here, where Pygments registers it for its retired Lean 3 lexer. -/
public def leanIsLean4 : String := "lean"

/-- The spellings that select a lexer: Pygments' registry aliases. -/
public def Lexer.aliases : Lexer → Array String
  | .lean4 => PygmentsLexData.lean4Aliases.push leanIsLean4
  | .python => PygmentsLexData.pythonAliases
  | .bash => PygmentsLexData.bashAliases
  | .console => PygmentsLexData.consoleAliases
  | .text => PygmentsLexData.textAliases

/-- The lexer a listing's language selects, case-insensitively, as the
provider's registry lookup is. -/
public def Lexer.ofName? (name : String) : Option Lexer :=
  let n := name.trimAscii.toString.toLower
  Lexer.all.find? (·.aliases.contains n)

/-- The Pygments lexer a native one mirrors, and the alias selecting it there. -/
public def Lexer.pygmentsAlias : Lexer → String
  | .lean4 => "lean4"
  | .python => "python"
  | .bash => "bash"
  | .console => "console"
  | .text => "text"

/-- The SHA-256 of the rule structure these lexers implement (`PygmentsLexData.rulesDigest`). -/
public def mirrorsRules : String :=
  "bf918c5d14c06fe7162c0141720eade1289ee69df4d403683880b739028bb4a8"

/-- The raw token stream the mirrored Pygments lexer writes for the whole
text, before any filter. -/
public def lex : Lexer → Src → Array Raw
  | .lean4, s => Lean4.lex s
  | .text, s => if s.size == 0 then #[] else #[⟨0, s.size, Ty.text⟩]
  | .python, s => Python.lex s
  | .bash, s => Bash.lex s
  | .console, s => Console.lex s

/-- Every scalar's token type: the raw token covering it, `Text` where none does. -/
public def kindsOf (n : Nat) (raws : Array Raw) : Array String := Id.run do
  let mut ks := Array.replicate n Ty.text
  for r in raws do
    for i in [r.start:min r.stop n] do
      ks := ks.setIfInBounds i r.kind
  return ks

end LeanTex.Core.Highlight
