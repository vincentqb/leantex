import LeanTex.Core.Diag

namespace LeanTex.Core.Lex

open LeanTex.Core

inductive Tok where
  | word (s : String)
  | space
  | par
  | ctrl (name : String)
  | lbrace
  | rbrace
  | math
  | sym (c : Char)
  | verb (s : String)
  deriving Repr, BEq

structure Token where
  tok : Tok
  pos : Pos
  deriving Repr, BEq

/-- Text symbols. The table lives in the lexer because it also decides the
space-swallowing rule above: these names take no argument, so the space after
them is content. The elaborator reads the same table for replacement text. -/
def textSymbols : List (String × String) :=
  [("middot", "·"), ("bullet", "•"), ("endash", "–"),
   ("emdash", "—"), ("ldots", "…"), ("dots", "…"),
   ("times", "×"), ("copyright", "©"), ("degree", "°"),
   ("nbsp", " "), ("thinspace", " ")]

/-- The special characters are fixed forever: no catcode reprogramming. -/
def special (c : Char) : Bool :=
  c == '\\' || c == '{' || c == '}' || c == '$' || c == '%' ||
  c == '[' || c == ']' || c == '&' || c == '#' || c == '^' || c == '_' || c == '~'

def isWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def scanWhile (cs : Array Char) (start : Nat) (p : Char → Bool) : Nat := Id.run do
  let mut j := start
  for _ in [start:cs.size] do
    if h : j < cs.size then
      if p cs[j] then j := j + 1 else break
    else break
  return j

private def posOver (cs : Array Char) (a b : Nat) (p : Pos) : Pos := Id.run do
  let mut pos := p
  for j in [a:b] do
    if h : j < cs.size then
      pos := pos.next (cs[j] == '\n')
  return pos

private def newlines (cs : Array Char) (a b : Nat) : Nat := Id.run do
  let mut n := 0
  for j in [a:b] do
    if h : j < cs.size then
      if cs[j] == '\n' then n := n + 1
  return n

private def matchAt (cs : Array Char) (i : Nat) (ps : Array Char) : Bool := Id.run do
  if i + ps.size > cs.size then
    return false
  for k in [0:ps.size] do
    if cs[i + k]! != ps[k]! then
      return false
  return true

private def findSub (cs : Array Char) (start : Nat) (pat : Array Char) : Option Nat := Id.run do
  for k in [start:cs.size] do
    if matchAt cs k pat then
      return some k
  return none

/-- The string over `[a, b)`, pushed a character at a time: going through
`extract` and a `List` allocated a cons cell per character of every token. -/
private def strFrom (cs : Array Char) (a b : Nat) : String := Id.run do
  let mut s := ""
  for j in [a:b] do
    if h : j < cs.size then
      s := s.push cs[j]
  return s

private def verbatimOpen : Array Char := "{verbatim}".toList.toArray
private def verbatimClose : Array Char := "\\end{verbatim}".toList.toArray

def lex (file : String) (input : String) : Array Token × Array Diag := Id.run do
  -- Folded straight into an array: `toList.toArray` builds and drops a cons
  -- cell per character of the document.
  let cs : Array Char := input.foldl (fun a c => a.push c) (Array.mkEmpty input.utf8ByteSize)
  let mut toks : Array Token := #[]
  let mut diags : Array Diag := #[]
  let mut i := 0
  let mut pos : Pos := {}
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      let here := pos
      if isWs c then
        let j := scanWhile cs i isWs
        let tok := if newlines cs i j ≥ 2 then Tok.par else Tok.space
        toks := toks.push ⟨tok, here⟩
        pos := posOver cs i j pos
        i := j
      else if c == '%' then
        let j := scanWhile cs i (· != '\n')
        let j := min (j + 1) cs.size
        pos := posOver cs i j pos
        i := j
      else if c == '\\' then
        if h' : i + 1 < cs.size then
          let c1 := cs[i + 1]
          if c1.isAlpha then
            let j := scanWhile cs (i + 1) Char.isAlpha
            let name := strFrom cs (i + 1) j
            if name == "begin" && matchAt cs j verbatimOpen then
              -- verbatim is lexically blind: capture raw content in one token
              let start := j + verbatimOpen.size
              match findSub cs start verbatimClose with
              | some k =>
                let stop := k + verbatimClose.size
                toks := toks.push ⟨.verb (strFrom cs start k), here⟩
                pos := posOver cs i stop pos
                i := stop
              | none =>
                diags := diags.push {
                  severity := .error
                  code := "E0102"
                  message := "unclosed verbatim: expected '\\end{verbatim}'"
                  span := some ⟨file, here⟩
                }
                toks := toks.push ⟨.verb (strFrom cs start cs.size), here⟩
                pos := posOver cs i cs.size pos
                i := cs.size
            else
              toks := toks.push ⟨.ctrl name, here⟩
              pos := posOver cs i j pos
              i := j
              -- A control word swallows the whitespace after it, so
              -- `\textbf {x}` introduces no space. Symbols take no argument,
              -- so eating the space would turn `a \middot b` into "a ·b".
              unless (textSymbols.lookup name).isSome do
                let k := scanWhile cs i isWs
                if k > i && newlines cs i k < 2 then
                  pos := posOver cs i k pos
                  i := k
          else
            toks := toks.push ⟨.ctrl (String.ofList [c1]), here⟩
            pos := posOver cs i (i + 2) pos
            i := i + 2
        else
          diags := diags.push {
            severity := .error
            code := "E0101"
            message := "lone backslash at end of input"
            span := some ⟨file, here⟩
          }
          i := i + 1
      else if c == '{' then
        toks := toks.push ⟨.lbrace, here⟩
        pos := pos.next false
        i := i + 1
      else if c == '}' then
        toks := toks.push ⟨.rbrace, here⟩
        pos := pos.next false
        i := i + 1
      else if c == '$' then
        toks := toks.push ⟨.math, here⟩
        pos := pos.next false
        i := i + 1
      else if special c then
        toks := toks.push ⟨.sym c, here⟩
        pos := pos.next false
        i := i + 1
      else
        let j := scanWhile cs i (fun c => !special c && !isWs c)
        toks := toks.push ⟨.word (strFrom cs i j), here⟩
        pos := posOver cs i j pos
        i := j
  return (toks, diags)

end LeanTex.Core.Lex
