import LeanTex.Core.Diag
import LeanTex.Core.Nfc

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
  | verb (env : String) (s : String)
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

/-- `@` is a control-name character, always. TeX makes this a mode
(`\makeatletter` sets `@` to catcode 11, `\makeatother` back to 12 —
source2e `ltdefns.dtx`; catcodes, TeXbook ch. 7), because internal names
like `\p@` must be writable in package code and unwritable in documents.
This engine has no catcode reprogramming, so the mode collapses to its
permissive half: `\vqb@bp` is one name wherever it stands. The alternative
— honouring the mode — would re-lex `\vqb@bp` outside `\makeatletter` as
`\vqb` then `@bp`, which is exactly the mis-lex the mode exists to cause,
and no known document wants: a document using `@`-names writes
`\makeatletter` first, and one that never uses them never notices. -/
def nameChar (c : Char) : Bool :=
  c.isAlpha || c == '@'

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

/-- What a whitespace run holding `n` end-of-lines means, by TeX's reading
state when it begins (TeXbook ch. 8): mid-line (`M`), one end-of-line is
a space and a blank line a paragraph; at the start of a line (`N`, where
a comment leaves the reader once it has discarded its own end-of-line),
indentation is skipped and one end-of-line is already a paragraph. -/
def wsTok (lineStart : Bool) (n : Nat) : Option Tok :=
  if lineStart then (if n ≥ 1 then some .par else none)
  else (if n ≥ 2 then some .par else some .space)

/-- A blank line is a paragraph break in either state: the comment that
put the reader at line start hid its own end-of-line, not the blank line
after it — the run it leaves reads as the run the text would have seen,
one end-of-line longer. -/
theorem blank_line_par_agree (n : Nat) (h : 1 ≤ n) :
    wsTok true n = wsTok false (n + 1) := by
  have h' : n + 1 ≥ 2 := by omega
  simp [wsTok, h, h']

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

/-- The lexically blind environments: their bodies are code, captured raw
in one token — `{verbatim}`, and the listing environments that differ from
it only by their declared apparatus (listings' `{lstlisting}`, minted's
`{minted}`), whose option head the elaborator reads from the captured
string. Each entry: the environment name, its `\begin` suffix, its whole
closer. -/
private def verbEnvs : List (String × Array Char × Array Char) :=
  ["verbatim", "lstlisting", "minted"].map fun n =>
    (n, s!"\{{n}}".toList.toArray, s!"\\end\{{n}}".toList.toArray)

def lex (file : String) (input : String) : Array Token × Array Diag := Id.run do
  -- Folded straight into an array: `toList.toArray` builds and drops a cons
  -- cell per character of the document. Normalized to NFC here, once, so
  -- every downstream consumer — hyphenation, slugs, font cmap lookups,
  -- both backends — sees one canonical spelling (UAX #15; Nfc.lean says
  -- why input is the right place).
  let cs : Array Char := Nfc.normalizeChars
    (input.foldl (fun a c => a.push c) (Array.mkEmpty input.utf8ByteSize))
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
        if let some tok := wsTok false (newlines cs i j) then
          toks := toks.push ⟨tok, here⟩
        pos := posOver cs i j pos
        i := j
      else if c == '%' then
        let j := scanWhile cs i (· != '\n')
        let j := min (j + 1) cs.size
        let k := scanWhile cs j isWs
        if let some tok := wsTok true (newlines cs j k) then
          toks := toks.push ⟨tok, posOver cs i j pos⟩
        pos := posOver cs i k pos
        i := k
      else if c == '\\' then
        if h' : i + 1 < cs.size then
          let c1 := cs[i + 1]
          if nameChar c1 then
            let j := scanWhile cs (i + 1) nameChar
            let name := strFrom cs (i + 1) j
            if name == "begin" &&
                verbEnvs.any (fun e => matchAt cs j e.2.1) then
              -- verbatim (and the listing environments) are lexically
              -- blind: capture raw content in one token
              let (env, opener, closer) :=
                (verbEnvs.find? (fun e => matchAt cs j e.2.1)).getD
                  ("verbatim", #[], #[])
              let start := j + opener.size
              match findSub cs start closer with
              | some k =>
                let stop := k + closer.size
                toks := toks.push ⟨.verb env (strFrom cs start k), here⟩
                pos := posOver cs i stop pos
                i := stop
              | none =>
                diags := diags.push (Diag.of .E0102
                  s!"unclosed \{{env}}: expected '\\end\{{env}}'" (some ⟨file, here⟩))
                toks := toks.push ⟨.verb env (strFrom cs start cs.size), here⟩
                pos := posOver cs i cs.size pos
                i := cs.size
            else if name == "verb" then
              -- `\verb<d>…<d>`: the text up to the delimiter's next copy on
              -- the same line is code, read raw (latex.ltx's `\verb`, whose
              -- `\@ifstar` skips spaces before the delimiter); `\verb*`
              -- shows each space as the visible space, U+2423.
              let star := cs[j]? == some '*'
              let k := scanWhile cs (if star then j + 1 else j) (fun c => c == ' ' || c == '\t')
              let d := (cs[k]?).getD '\n'
              let e := if d == '\n' || d == '\r' then k
                else scanWhile cs (k + 1) (fun c => c != d && c != '\n' && c != '\r')
              let closed := d != '\n' && d != '\r' && cs[e]? == some d
              let body := if d == '\n' || d == '\r' then "" else strFrom cs (k + 1) e
              let shown := if star then body.map (fun c => if c == ' ' then '␣' else c) else body
              unless closed do
                diags := diags.push (Diag.of .E0102
                  "unclosed \\verb: its delimiter's second copy must end the code on the same line"
                  (some ⟨file, here⟩))
              toks := toks.push ⟨.verb "verb" shown, here⟩
              let stop := if closed then e + 1 else e
              pos := posOver cs i stop pos
              i := stop
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
          else if c1 == '\n' || c1 == '\r' then
            -- `\` ending a line is `\^^M`, the control space (plain.tex and
            -- latex.ltx: `\def\^^M{\ }`); the next line starts at its first
            -- non-blank, and a blank one ends the paragraph.
            toks := toks.push ⟨.ctrl " ", here⟩
            let e := if c1 == '\r' && cs[i + 2]? == some '\n' then i + 3 else i + 2
            let k := scanWhile cs e isWs
            if let some tok := wsTok true (newlines cs e k) then
              toks := toks.push ⟨tok, posOver cs i e pos⟩
            pos := posOver cs i k pos
            i := k
          else
            toks := toks.push ⟨.ctrl (String.ofList [c1]), here⟩
            pos := posOver cs i (i + 2) pos
            i := i + 2
        else
          diags := diags.push (Diag.of .E0101
            "lone backslash at end of input" (some ⟨file, here⟩))
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
