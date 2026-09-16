import LeanTex.Core.Lex

namespace LeanTex.Core.Parse

open LeanTex.Core LeanTex.Core.Lex

inductive Raw where
  | word (s : String) (pos : Pos)
  | space
  | par (pos : Pos)
  | ctrl (name : String) (pos : Pos)
  | sym (c : Char) (pos : Pos)
  | group (body : Array Raw) (pos : Pos)
  | math (display : Bool) (body : Array Raw) (pos : Pos)
  | env (name : String) (body : Array Raw) (pos : Pos)
  | verb (s : String) (pos : Pos)
  deriving Repr, BEq, Inhabited

inductive Stop where
  | eof
  | brace
  | math
  | displayMath
  | env (name : String)
  deriving Repr, BEq

structure St where
  toks : Array Token
  file : String
  diags : Array Diag := #[]

abbrev PM := StateM St

private def diag (code msg : String) (pos : Pos) (help : Option String := none) : PM Unit :=
  modify fun st => { st with diags := st.diags.push {
    severity := .error
    code := code
    message := msg
    span := some ⟨st.file, pos⟩
    help := help
  } }

private def tokAt (i : Nat) : PM (Option Token) := do
  return (← get).toks[i]?

private def stopName : Stop → String
  | .eof => "end of input"
  | .brace => "'}'"
  | .math => "closing '$'"
  | .displayMath => "'\\]'"
  | .env n => s!"'\\end\{{n}}'"

private def parseEnvName (i : Nat) (pos : Pos) : PM (String × Nat) := do
  let some ⟨.lbrace, _⟩ ← tokAt i
    | diag "E0205" "expected '{name}' here" pos; return ("", i)
  let some ⟨.word n, _⟩ ← tokAt (i + 1)
    | diag "E0205" "expected an environment name" pos; return ("", i + 1)
  let some ⟨.rbrace, _⟩ ← tokAt (i + 2)
    | diag "E0205" "expected '}' after the environment name" pos; return (n, i + 2)
  return (n, i + 3)

/-- Parse a sequence until `stop`; returns the items and the index after the
closing delimiter. Recovery: strays are reported and skipped, unclosed
delimiters close at end of input. -/
private partial def seq (i : Nat) (stop : Stop) (openPos : Pos) :
    PM (Array Raw × Nat) := do
  let mut acc : Array Raw := #[]
  let mut i := i
  repeat
    match ← tokAt i with
    | none =>
      if stop != .eof then
        diag "E0201" s!"unclosed: expected {stopName stop}" openPos
      return (acc, i)
    | some ⟨tok, pos⟩ =>
      match tok with
      | .rbrace =>
        if stop == .brace then
          return (acc, i + 1)
        diag "E0202" "unexpected '}'" pos
        i := i + 1
      | .math =>
        if stop == .math then
          return (acc, i + 1)
        let (body, j) ← seq (i + 1) .math pos
        acc := acc.push (.math false body pos)
        i := j
      | .lbrace =>
        let (body, j) ← seq (i + 1) .brace pos
        acc := acc.push (.group body pos)
        i := j
      | .ctrl "[" =>
        let (body, j) ← seq (i + 1) .displayMath pos
        acc := acc.push (.math true body pos)
        i := j
      | .ctrl "]" =>
        if stop == .displayMath then
          return (acc, i + 1)
        diag "E0202" "unexpected '\\]'" pos
        i := i + 1
      | .ctrl "begin" =>
        let (name, j) ← parseEnvName (i + 1) pos
        let (body, k) ← seq j (.env name) pos
        acc := acc.push (.env name body pos)
        i := k
      | .ctrl "end" =>
        let (name, j) ← parseEnvName (i + 1) pos
        match stop with
        | .env expected =>
          if name != expected then
            diag "E0205" s!"'\\end\{{name}}' closes '\\begin\{{expected}}'" pos
          return (acc, j)
        | _ =>
          diag "E0205" s!"'\\end\{{name}}' without matching '\\begin\{{name}}'" pos
          i := j
      | .ctrl name =>
        acc := acc.push (.ctrl name pos)
        i := i + 1
      | .word s =>
        acc := acc.push (.word s pos)
        i := i + 1
      | .space =>
        acc := acc.push .space
        i := i + 1
      | .par =>
        acc := acc.push (.par pos)
        i := i + 1
      | .sym c =>
        acc := acc.push (.sym c pos)
        i := i + 1
      | .verb s =>
        acc := acc.push (.verb s pos)
        i := i + 1
  return (acc, i)

def parse (file : String) (toks : Array Token) : Array Raw × Array Diag :=
  let (res, st) := (seq 0 .eof {}).run { toks := toks, file := file }
  (res.1, st.diags)

end LeanTex.Core.Parse
