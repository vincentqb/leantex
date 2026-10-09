module

public import LeanTex.Core.Highlight.Scan
import LeanTex.Core.Highlight.Lean4
import LeanTex.Core.Highlight.Python
import LeanTex.Core.Highlight.Bash
import LeanTex.Core.Highlight.Console
import LeanTex.Core.PygmentsLexData

/-!
The native listing lexers: Pygments' own, for the languages documents in
use write, mirrored rule for rule from one release
(`PygmentsLexData.pygmentsVersion`), so a listing's token types are the
ones that release's lexers write, with no process and no Python on the
render path. A language with no lexer here still reaches the provider.

The mirror is held to Pygments three ways: the rule structure it implements
(`mirrorsRules`, against the generated digest), recorded token streams in
the suite, and `scripts/highlight-diff.lean`, which runs both over invented,
fuzzed and local documents' listings.
-/
namespace LeanTex.Core.Highlight

public inductive Lexer where
  | lean4 | python | bash | console | text
  deriving Repr, BEq, DecidableEq, Inhabited, Hashable

public def Lexer.all : List Lexer := [.lean4, .python, .bash, .console, .text]

/-- `lean` names Lean 4 here. Pygments registers it for its Lean 3 lexer,
but Lean 3 is retired, and current documents' `lean` fences hold Lean 4,
which is how the Lean 4 manual and Mathlib's documentation spell them. -/
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

/-- The Pygments lexer a native one mirrors, and the alias that selects it
there: what the differential oracle asks the provider for. -/
public def Lexer.pygmentsAlias : Lexer → String
  | .lean4 => "lean4"
  | .python => "python"
  | .bash => "bash"
  | .console => "console"
  | .text => "text"

/-- The SHA-256 of the rule structure these lexers implement. The suite
holds it equal to `PygmentsLexData.rulesDigest`; a regeneration from a
Pygments whose rules moved breaks that until the mirror follows. -/
public def mirrorsRules : String :=
  "b84faed2c9d54c80a464be2a057f2bf7700eb9c4e64fa56e1f800bd032ca3256"

/-- The raw token stream the mirrored Pygments lexer writes for the whole
text, before any filter. -/
public def lex : Lexer → Src → Array Raw
  | .lean4, s => Lean4.lex s
  | .text, s => if s.size == 0 then #[] else #[⟨0, s.size, Ty.text⟩]
  | .python, s => Python.lex s
  | .bash, s => Bash.lex s
  | .console, s => Console.lex s

/-- Every scalar's token type: the raw token covering it, `Text` where none
does. A stream that skipped or overlapped scalars would still keep every
scalar; the lexers' coverage is the oracle's to judge. -/
public def kindsOf (n : Nat) (raws : Array Raw) : Array String := Id.run do
  let mut ks := Array.replicate n Ty.text
  for r in raws do
    for i in [r.start:min r.stop n] do
      ks := ks.setIfInBounds i r.kind
  return ks

end LeanTex.Core.Highlight
