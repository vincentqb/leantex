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

/-- What closes an open frame. -/
inductive Stop where
  | brace
  | math
  | parenMath
  | displayMath
  | env (name : String)
  deriving Repr, BEq, Inhabited

def Stop.name : Stop → String
  | .brace => "'}'"
  | .math => "closing '$'"
  | .parenMath => "'\\)'"
  | .displayMath => "'\\]'"
  | .env n => s!"'\\end\{{n}}'"

/-- An open delimiter, holding the items collected before it. -/
private structure Frame where
  stop : Stop
  openPos : Pos
  outer : Array Raw

/-- Wrap a closed frame's body into the node its delimiter denotes. -/
private def Frame.close (f : Frame) (body : Array Raw) : Array Raw :=
  match f.stop with
  | .brace => f.outer.push (.group body f.openPos)
  | .math => f.outer.push (.math false body f.openPos)
  | .parenMath => f.outer.push (.math false body f.openPos)
  | .displayMath => f.outer.push (.math true body f.openPos)
  | .env n => f.outer.push (.env n body f.openPos)

private def err (file : String) (code : DiagCode) (msg : String) (pos : Pos) : Diag :=
  Diag.of code msg (some ⟨file, pos⟩)

/-- `{name}` after `\begin` or `\end`; returns the name and the next index. -/
private def envName (toks : Array Token) (file : String) (i : Nat) (pos : Pos) :
    String × Nat × Array Diag :=
  match toks[i]?, toks[i + 1]?, toks[i + 2]? with
  | some ⟨.lbrace, _⟩, some ⟨.word n, _⟩, some ⟨.rbrace, _⟩ => (n, i + 3, #[])
  | some ⟨.lbrace, _⟩, some ⟨.word n, _⟩, _ =>
    (n, i + 2, #[err file .E0205 "expected '}' after the environment name" pos])
  | some ⟨.lbrace, _⟩, _, _ =>
    ("", i + 1, #[err file .E0205 "expected an environment name" pos])
  | _, _, _ => ("", i, #[err file .E0205 "expected '{name}' here" pos])

/-- Parse tokens into a `Raw` forest with one pass and an explicit frame
stack: no recursion, so totality is immediate. Recovery is unchanged —
strays are reported and skipped, unclosed delimiters close at end of input. -/
def parse (file : String) (toks : Array Token) : Array Raw × Array Diag := Id.run do
  let mut frames : Array Frame := #[]
  let mut acc : Array Raw := #[]
  let mut diags : Array Diag := #[]
  let mut i := 0
  -- Every branch advances `i` by at least one, so this bound is never the
  -- reason the loop stops; the `i < toks.size` guard is.
  for _ in [0:toks.size + 1] do
    if h : i < toks.size then
      let ⟨tok, pos⟩ := toks[i]
      i := i + 1
      match tok with
      | .lbrace =>
        frames := frames.push ⟨.brace, pos, acc⟩
        acc := #[]
      | .rbrace =>
        match frames.back? with
        | some f =>
          if f.stop == .brace then
            frames := frames.pop
            acc := f.close acc
          else
            diags := diags.push (err file .E0202 "unexpected '}'" pos)
        | none =>
          diags := diags.push (err file .E0202 "unexpected '}'" pos)
      | .math =>
        match frames.back? with
        | some f =>
          if f.stop == .math then
            frames := frames.pop
            acc := f.close acc
          else
            frames := frames.push ⟨.math, pos, acc⟩
            acc := #[]
        | none =>
          frames := frames.push ⟨.math, pos, acc⟩
          acc := #[]
      | .ctrl "(" =>
        frames := frames.push ⟨.parenMath, pos, acc⟩
        acc := #[]
      | .ctrl ")" =>
        match frames.back? with
        | some f =>
          if f.stop == .parenMath then
            frames := frames.pop
            acc := f.close acc
          else
            diags := diags.push (err file .E0202 "unexpected '\\)'" pos)
        | none =>
          diags := diags.push (err file .E0202 "unexpected '\\)'" pos)
      | .ctrl "[" =>
        frames := frames.push ⟨.displayMath, pos, acc⟩
        acc := #[]
      | .ctrl "]" =>
        match frames.back? with
        | some f =>
          if f.stop == .displayMath then
            frames := frames.pop
            acc := f.close acc
          else
            diags := diags.push (err file .E0202 "unexpected '\\]'" pos)
        | none =>
          diags := diags.push (err file .E0202 "unexpected '\\]'" pos)
      | .ctrl "begin" =>
        let (name, j, ds) := envName toks file i pos
        diags := diags ++ ds
        i := j
        frames := frames.push ⟨.env name, pos, acc⟩
        acc := #[]
      | .ctrl "end" =>
        let (name, j, ds) := envName toks file i pos
        diags := diags ++ ds
        i := j
        match frames.back? with
        | some f =>
          match f.stop with
          | .env expected =>
            if name != expected then
              diags := diags.push
                (err file .E0205 s!"'\\end\{{name}}' closes '\\begin\{{expected}}'" pos)
            frames := frames.pop
            acc := f.close acc
          | _ =>
            diags := diags.push (err file .E0205
              s!"'\\end\{{name}}' without matching '\\begin\{{name}}'" pos)
        | none =>
          diags := diags.push (err file .E0205
            s!"'\\end\{{name}}' without matching '\\begin\{{name}}'" pos)
      | .ctrl name => acc := acc.push (.ctrl name pos)
      | .word s => acc := acc.push (.word s pos)
      | .space => acc := acc.push .space
      | .par => acc := acc.push (.par pos)
      | .sym c => acc := acc.push (.sym c pos)
      | .verb s => acc := acc.push (.verb s pos)
  -- End of input: close what is still open, innermost first.
  for _ in [0:frames.size] do
    match frames.back? with
    | some f =>
      diags := diags.push
        (err file .E0201 s!"unclosed: expected {f.stop.name}" f.openPos)
      frames := frames.pop
      acc := f.close acc
    | none => pure ()
  return (acc, diags)


/-! `Raw` back to source text. Declaration blocks and lengths are parsed from
this string, so it must round-trip what the lexer accepted. -/

/-- The synthetic environment the driver wraps an `\input` file's content in,
so every stage downstream knows which file a position belongs to. The name
starts with `@`, which no control word can lex, so no document can forge one. -/
def inputEnv (file : String) : String := "@input:" ++ file

def inputEnvFile? (name : String) : Option String :=
  if name.startsWith "@input:" then some ((name.drop "@input:".length).toString)
  else none

/-- The index past the leading run of `.space` raws at `i`: the one spaces
scan over sibling raws, shared by every consumer of `Raw` — a caller never
hand-rolls its own. -/
def skipSpaces (raws : Array Raw) (i : Nat) : Nat :=
  if h : i < raws.size then
    if raws[i] matches .space then skipSpaces raws (i + 1) else i
  else i
termination_by raws.size - i

theorem skipSpaces_ge (raws : Array Raw) (i : Nat) : i ≤ skipSpaces raws i := by
  fun_induction skipSpaces raws i <;> omega

mutual

def rawSrc (raws : Array Raw) : String :=
  (rawSrcList raws.toList).trimAscii.toString

def rawSrcList (rs : List Raw) : String :=
  match rs with
  | [] => ""
  | r :: rest => rawSrcOne r ++ rawSrcList rest

def rawSrcOne (r : Raw) : String :=
  match r with
  | .word s _ => s
  | .space => " "
  | .par _ => " "
  | .sym c _ => String.ofList [c]
  | .ctrl n _ => "\\" ++ n ++ " "
  | .group body _ => "{" ++ rawSrc body ++ "}"
  | .math d body _ =>
    let inner := rawSrc body
    if d then s!"\\[{inner}\\]" else s!"${inner}$"
  | .env n body _ => s!"\\begin\{{n}}" ++ rawSrc body ++ s!"\\end\{{n}}"
  | .verb s _ => s!"\\begin\{verbatim}{s}\\end\{verbatim}"

end

end LeanTex.Core.Parse
