module

public import LeanTex.Core.Diag
import LeanTex.Core.Nfc

namespace LeanTex.Core.Lex

open LeanTex.Core

public inductive Tok where
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

public structure Token where
  tok : Tok
  pos : Pos
  deriving Repr, BEq

/-- Text symbols. The table lives in the lexer because it also decides the
space-swallowing rule above: these names take no argument, so the space after
them is content. The elaborator reads the same table for replacement text. -/
@[expose] public def textSymbols : List (String × String) :=
  [("middot", "·"), ("bullet", "•"), ("endash", "–"),
   ("emdash", "—"), ("ldots", "…"), ("dots", "…"),
   ("times", "×"), ("copyright", "©"), ("degree", "°"),
   ("nbsp", " "), ("thinspace", " ")]

/-- `@` is a control-name character, always. TeX makes this a mode
(`\makeatletter` sets `@` to catcode 11, `\makeatother` back to 12 —
source2e `ltdefns.dtx`; catcodes, TeXbook ch. 7), because internal names
like `\p@` must be writable in package code and unwritable in documents.
This engine has no catcode reprogramming, so the mode collapses to its
permissive half: `\demo@wd` is one name wherever it stands. The alternative
— honouring the mode — would re-lex `\demo@wd` outside `\makeatletter` as
`\demo` then `@wd`, which is exactly the mis-lex the mode exists to cause,
and no known document wants: a document using `@`-names writes
`\makeatletter` first, and one that never uses them never notices. -/
@[expose] public def nameChar (c : Char) : Bool :=
  c.isAlpha || c == '@'

/-- The special characters are fixed forever: no catcode reprogramming. -/
@[expose] public def special (c : Char) : Bool :=
  c == '\\' || c == '{' || c == '}' || c == '$' || c == '%' ||
  c == '[' || c == ']' || c == '&' || c == '#' || c == '^' || c == '_' || c == '~'

@[expose] public def isWs (c : Char) : Bool :=
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

/-- TeXbook ch. 8: mid-line whitespace supplies one space, followed by a
paragraph token for each blank line. At line start, indentation is skipped
and every end-of-line is a paragraph. Keeping the whole token run matters
inside definitions, where `\ifx` distinguishes spaces and repeated `\par`. -/
public def wsTokens (lineStart : Bool) (n : Nat) : List Tok :=
  if lineStart then List.replicate n .par
  else .space :: List.replicate (n - 1) .par

/-- A comment removes its own end-of-line, including the space mid-line
text would have supplied, but preserves every subsequent paragraph token. -/
public theorem blank_line_par_agree (n : Nat) :
    (wsTokens false (n + 1)).tail = wsTokens true n := by
  simp [wsTokens]

/-- The mid-line whitespace run, given whether a group brace sits immediately
before the run (`prevLbrace`) or immediately after it (`nextRbrace`), and the
run's newline count `n`. A single line end against a group brace is dropped —
exactly as LaTeX's `{%` drops the line end after an opening brace — so the run
emits nothing; every other run is byte-for-byte `wsTokens false n`, leaving
same-line spacing and blank-line paragraph behaviour untouched. The brace
carries no glyph, so any adjacency the drop leaves is intentional under the
shorthand and earns no diagnostic: `{` at end of line and `{%` are identical
after lexing. -/
public def midlineWs (prevLbrace nextRbrace : Bool) (n : Nat) : List Tok :=
  if n = 1 ∧ (prevLbrace = true ∨ nextRbrace = true) then []
  else wsTokens false n

/-- A same-line run is always a space, whatever sits beside it. -/
public theorem midlineWs_same_line (p q : Bool) : midlineWs p q 0 = [.space] := by
  simp [midlineWs, wsTokens]

/-- A blank line keeps main's whole mid-line run, brace-adjacency
notwithstanding. -/
public theorem midlineWs_par (p q : Bool) (n : Nat) (h : n ≥ 2) :
    midlineWs p q n = wsTokens false n := by
  have : ¬ n = 1 := by omega
  simp [midlineWs, this]

/-- Suppression is exactly a single line end against a group brace: the
contract is narrow, not a global whitespace trim. (`wsTokens false n` is
always non-empty — it heads with a space — so an empty run can only be the
suppressed case.) -/
public theorem midlineWs_suppress_iff (p q : Bool) (n : Nat) :
    midlineWs p q n = [] ↔ (n = 1 ∧ (p = true ∨ q = true)) := by
  unfold midlineWs
  split
  · rename_i hc; exact iff_of_true rfl hc
  · rename_i hc
    refine iff_of_false ?_ hc
    simp [wsTokens]

/-- Away from braces the rule is byte-for-byte the old `wsTokens false`: the
change is confined to brace-adjacency. -/
public theorem midlineWs_conservative (p q : Bool) (n : Nat) (hp : p = false) (hq : q = false) :
    midlineWs p q n = wsTokens false n := by
  simp [midlineWs, hp, hq]

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

/-- A line end at `k`: where the line after it starts, a CRLF one unit. -/
private def lineEndAt (cs : Array Char) (k : Nat) : Option Nat :=
  match cs[k]? with
  | some '\n' => some (k + 1)
  | some '\r' => some (if cs[k + 1]? == some '\n' then k + 2 else k + 1)
  | _ => none

/-- Past the spaces at `k` and at most one line end among them, as TeX's
argument reader skips them, and — where `comments` — any comment, which
spends its own line end (TeX's `%`); `none` at a blank line, which ends a
paragraph there. -/
private def argGap (cs : Array Char) (k : Nat) (comments : Bool := true) : Option Nat := Id.run do
  let blank (c : Char) := c == ' ' || c == '\t'
  let mut a := scanWhile cs k blank
  let mut ends := 0
  for _ in [0:cs.size] do
    if comments && cs[a]? == some '%' then
      let eol := scanWhile cs a (fun c => c != '\n' && c != '\r')
      a := scanWhile cs ((lineEndAt cs eol).getD eol) blank
      -- The comment spent its line end; a line end now is a blank line.
      ends := 1
    else
      match lineEndAt cs a with
      | some b =>
        if ends > 0 then return none
        ends := ends + 1
        a := scanWhile cs b blank
      | none => break
  return some a

/-- The commands whose next token is the name they define or show, never a
call: `\renewcommand\mintinline[2]{…}` names minted's command, so its
arguments are the definition's, not code. -/
private def definers : List String :=
  ["newcommand", "renewcommand", "providecommand", "DeclareRobustCommand",
   "NewDocumentCommand", "RenewDocumentCommand", "ProvideDocumentCommand",
   "DeclareDocumentCommand", "NewCommandCopy", "RenewCommandCopy", "DeclareCommandCopy",
   "LetLtxMacro", "newrobustcmd", "renewrobustcmd", "providerobustcmd",
   "def", "gdef", "edef", "xdef", "let", "define", "show", "meaning", "string", "noexpand"]

/-- Whether the last token, past white space and a definer's star, is a
definer. -/
private def definesNext (toks : Array Token) : Bool := Id.run do
  let mut k := toks.size
  for _ in [0:toks.size] do
    if k == 0 then break
    k := k - 1
    match toks[k]? with
    | some { tok := .space, .. } | some { tok := .word "*", .. } => continue
    | some { tok := .ctrl n, .. } => return definers.contains n
    | _ => return false
  return false

/-- minted's one-line commands, `\mintinline` and `\mint`, read from just
past the command name as minted.sty (v3.7) reads them: `[options]`, braces
nesting inside, then `{language}`, then the code — a brace group whose
braces nest, or the text up to the next copy of the character that opens
it. Spaces stand between them as TeX's reader skips them (`argGap`); inside
the code a line end is one more character, which a blank line ends unclosed.
Returns where the call ends, whether its code closed, and the call as the
elaborator reads it: its options, language and delimited code, the spaces
between them dropped. `none` when no `{language}` follows, so the name stays
an ordinary control word (the subject of a definition, say). -/
private def mintedCall (cs : Array Char) (j : Nat) : Option (Nat × Bool × String) := Id.run do
  let some start := argGap cs j | return none
  let mut k := start
  let mut head := ""
  if cs[k]? == some '[' then
    let mut depth : Nat := 0
    let mut m := k + 1
    let mut shut := false
    for _ in [k + 1:cs.size] do
      match cs[m]? with
      | some ']' =>
        if depth == 0 then
          shut := true
          break
        m := m + 1
      | some '{' => depth := depth + 1; m := m + 1
      | some '}' => depth := depth - 1; m := m + 1
      | some _ => m := m + 1
      | none => break
    unless shut do return none
    head := strFrom cs k (m + 1)
    let some next := argGap cs (m + 1) | return none
    k := next
  unless cs[k]? == some '{' do return none
  let close := scanWhile cs (k + 1) (fun c => c != '}' && c != '\n' && c != '\r')
  unless cs[close]? == some '}' do return none
  head := head ++ strFrom cs k (close + 1)
  let some code := argGap cs (close + 1) (comments := false) | return some (close + 1, false, head)
  -- A closing brace opens no code: the call's code is not here, as in a
  -- definition that stops at the language (`\newcommand{\py}{\mintinline{python}}`).
  if cs[code]? == some '}' then return none
  -- A blank line ends the code: a line end, then only spaces, then another.
  let blankAt (m : Nat) : Bool :=
    match lineEndAt cs m with
    | some b => (lineEndAt cs (scanWhile cs b (fun c => c == ' ' || c == '\t'))).isSome
    | none => false
  let (stop, closed) : Nat × Bool := Id.run do
    match cs[code]? with
    | none => return (code, false)
    | some '{' =>
      let mut depth : Nat := 0
      let mut m := code + 1
      for _ in [code + 1:cs.size] do
        if blankAt m then return (m, false)
        match cs[m]? with
        | some '}' =>
          if depth == 0 then return (m + 1, true)
          depth := depth - 1
          m := m + 1
        | some '{' => depth := depth + 1; m := m + 1
        | some _ => m := m + 1
        | none => break
      return (cs.size, false)
    | some d =>
      let mut m := code + 1
      for _ in [code + 1:cs.size] do
        if blankAt m then return (m, false)
        match cs[m]? with
        | some c => if c == d then return (m + 1, true) else m := m + 1
        | none => break
      return (cs.size, false)
  return some (stop, closed, head ++ strFrom cs code stop)

/-- The written control token, before NFC changes any spelling. A control
word ends with its name; a control symbol includes its character, including
both characters of a CRLF line end. -/
private def writtenControl (source : Array Char) (i : Nat) : Option String := do
  guard (source[i]? == some '\\')
  let c ← source[i + 1]?
  let stop := if nameChar c then scanWhile source (i + 1) nameChar
    else if c == '\r' && source[i + 2]? == some '\n' then i + 3 else i + 2
  return strFrom source i stop

private structure SourceChunk where
  first : Nat
  stop : Nat
  offset : Nat
  normalized : Array Char
  unchanged : Bool
  pos : Pos

private structure SourceMap where
  chunks : Array SourceChunk := #[]
  size : Nat := 0
  stop : Nat := 0
  pos : Pos := {}

/-- Structural ASCII characters and whitespace separate NFC slices (UAX #15).
Keep their original scalar offsets and positions, including the end boundary.
The normalizer still owns token text; only the original array supplies evidence. -/
private def sourceMap (source : Array Char) : SourceMap := Id.run do
  let mut out : SourceMap := {}
  let mut i := 0
  for _ in [0:source.size] do
    if h : i < source.size then
      let j := if special source[i] || isWs source[i] then i + 1
        else scanWhile source i (fun c => !special c && !isWs c)
      let raw := source.extract i j
      let normalized := Nfc.normalizeChars raw
      out := { out with
        chunks := out.chunks.push ⟨i, j, out.size, normalized, raw == normalized, out.pos⟩
        size := out.size + normalized.size
        stop := j
        pos := posOver source i j out.pos }
      i := j
  return out

/-- Most token boundaries coincide with a chunk boundary. A control may consume
part of a word chunk; an internal cut is accepted only when normalizing its two
original slices gives exactly the two normalized slices. A reordered or expanded
scalar with no such cut provides no literal evidence for a synthetic fragment. -/
private def SourceMap.point (m : SourceMap) (source : Array Char) (i : Nat) :
    Option (Nat × Pos) := Id.run do
  if i == m.size then return some (m.stop, m.pos)
  let mut lo := 0
  let mut hi := m.chunks.size
  for _ in [0:m.chunks.size + 1] do
    if h : lo < hi ∧ hi ≤ m.chunks.size then
      let mid := (lo + hi) / 2
      let chunk := m.chunks[mid]'(by omega)
      if i < chunk.offset then hi := mid
      else if chunk.offset + chunk.normalized.size ≤ i then lo := mid + 1
      else
        let k := i - chunk.offset
        if k == 0 then return some (chunk.first, chunk.pos)
        if chunk.unchanged then
          return some (chunk.first + k, posOver source chunk.first (chunk.first + k) chunk.pos)
        let lead := chunk.normalized.extract 0 k
        let rest := chunk.normalized.extract k chunk.normalized.size
        for j in [chunk.first + 1:chunk.stop] do
          if Nfc.normalizeChars (source.extract chunk.first j) == lead &&
              Nfc.normalizeChars (source.extract j chunk.stop) == rest then
            return some (j, posOver source chunk.first j chunk.pos)
        return none
    else break
  return none

private def writtenRange (m : SourceMap) (source cs : Array Char) (i j : Nat) :
    Option String := do
  let (a, _) ← m.point source i
  let (b, _) ← m.point source j
  guard (a < b && b ≤ source.size &&
    Nfc.normalizeChars (source.extract a b) == cs.extract i j)
  return strFrom source a b

/-- Every admitted literal is a nonempty original source slice whose NFC is
the token's normalized slice; arbitrary or incomplete maps cannot invent it. -/
private theorem writtenRange_source_exact
    (m : SourceMap) (source cs : Array Char) (i j : Nat) (text : String)
    (h : writtenRange m source cs i j = some text) :
    ∃ a b, a < b ∧ b ≤ source.size ∧
      Nfc.normalizeChars (source.extract a b) = cs.extract i j ∧
      text = strFrom source a b := by
  cases ha : m.point source i with
  | none => simp [writtenRange, ha] at h
  | some a =>
    cases hb : m.point source j with
    | none => simp [writtenRange, ha, hb] at h
    | some b =>
      simp [writtenRange, ha, hb, guard] at h
      split at h
      next good =>
        simp at h
        exact ⟨a.1, b.1, good.1.1, good.1.2, good.2, h.symm⟩
      next bad => simp [failure] at h

/-- The lexically blind environments: their bodies are code, captured raw
in one token — `{verbatim}`, and the listing environments that differ from
it only by their declared apparatus (listings' `{lstlisting}`, minted's
`{minted}`), whose option head the elaborator reads from the captured
string. Each entry: the environment name, its `\begin` suffix, its whole
closer. -/
private def verbEnvs : List (String × Array Char × Array Char) :=
  ["verbatim", "lstlisting", "minted"].map fun n =>
    (n, s!"\{{n}}".toList.toArray, s!"\\end\{{n}}".toList.toArray)

public def lex (file : String) (input : String) : Array Token × Array Diag := Id.run do
  -- Folded straight into an array: `toList.toArray` builds and drops a cons
  -- cell per character of the document. Normalized to NFC here, once, so
  -- every downstream consumer — hyphenation, slugs, font cmap lookups,
  -- both backends — sees one canonical spelling (UAX #15; Nfc.lean says
  -- why input is the right place).
  let source := input.foldl (fun a c => a.push c) (Array.mkEmpty input.utf8ByteSize)
  let cs := Nfc.normalizeChars source
  let unchanged := source == cs
  let locations := if unchanged then {} else sourceMap source
  let sourcePos (i : Nat) (fallback : Pos) :=
    if unchanged then fallback else
      ((locations.point source i).map (·.2)).getD { fallback with sourceMapped := false }
  let written (i j : Nat) :=
    if unchanged then some (strFrom source i j) else writtenRange locations source cs i j
  let mut toks : Array Token := #[]
  let mut diags : Array Diag := #[]
  let mut i := 0
  let mut pos : Pos := {}
  let mut closeEol := false
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      let c := cs[i]
      let here := sourcePos i pos
      if isWs c then
        let j := scanWhile cs i isWs
        let n := newlines cs i j
        let prevLbrace := match toks.back? with
          | some t => t.tok == .lbrace
          | none => false
        let nextRbrace := cs[j]? == some '}'
        -- A single line end against a group brace is dropped, exactly as
        -- LaTeX's `{%` drops the line end after an opening brace. Group
        -- braces carry no glyph, so any adjacency this leaves is intentional
        -- under the shorthand and earns no diagnostic: the two syntaxes are
        -- indistinguishable at the lexer boundary.
        for tok in midlineWs prevLbrace nextRbrace n do
          toks := toks.push ⟨tok, here⟩
        -- The space TeX reads there stays on the brace, for a reader that
        -- runs TeX's lists as TeX does (`Pos.openEol`, `Pos.closeEol`).
        if n == 1 && (prevLbrace || nextRbrace) then
          if prevLbrace then
            toks := toks.modify (toks.size - 1) fun t => { t with pos := { t.pos with openEol := true } }
          else closeEol := true
        pos := posOver cs i j pos
        i := j
      else if c == '%' then
        let j := scanWhile cs i (· != '\n')
        let j := min (j + 1) cs.size
        let k := scanWhile cs j isWs
        for tok in wsTokens true (newlines cs j k) do
          toks := toks.push ⟨tok, sourcePos j (posOver cs i j pos)⟩
        pos := posOver cs i k pos
        i := k
      else if c == '\\' then
        let here := { here with command :=
          if unchanged then writtenControl source i
          else (locations.point source i).bind fun (offset, _) => writtenControl source offset }
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
            else if let some (stop, closed, call) :=
                (if (name == "mintinline" || name == "mint") && !definesNext toks then
                  mintedCall cs j else none) then
              -- minted's commands read their code raw, as `\verb` does.
              unless closed do
                diags := diags.push (Diag.of .E0102
                  s!"unclosed \\{name}: its code's closing delimiter must come before a blank line"
                  (some ⟨file, here⟩))
              toks := toks.push ⟨.verb name call, here⟩
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
                for tok in wsTokens true (newlines cs i k - 1) do
                  toks := toks.push ⟨tok, sourcePos i pos⟩
                pos := posOver cs i k pos
                i := k
          else if c1 == '\n' || c1 == '\r' then
            -- `\` ending a line is `\^^M`, the control space (plain.tex and
            -- latex.ltx: `\def\^^M{\ }`); the next line starts at its first
            -- non-blank, and a blank one ends the paragraph.
            toks := toks.push ⟨.ctrl " ", here⟩
            let e := if c1 == '\r' && cs[i + 2]? == some '\n' then i + 3 else i + 2
            let k := scanWhile cs e isWs
            for tok in wsTokens true (newlines cs e k) do
              toks := toks.push ⟨tok, sourcePos e (posOver cs i e pos)⟩
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
        toks := toks.push ⟨.rbrace, { here with closeEol }⟩
        closeEol := false
        pos := pos.next false
        i := i + 1
      else if c == '$' then
        -- Keep individual shifts: in `$x$$y$` the middle pair closes one
        -- inline formula and opens the next.
        let stop := if cs[i + 1]? == some '$' then i + 2 else i + 1
        let here := { here with command := written i stop }
        toks := toks.push ⟨.math, here⟩
        pos := pos.next false
        i := i + 1
      else if special c then
        toks := toks.push ⟨.sym c, { here with command := written i (i + 1) }⟩
        pos := pos.next false
        i := i + 1
      else
        let j := scanWhile cs i (fun c => !special c && !isWs c)
        toks := toks.push ⟨.word (strFrom cs i j), { here with command := written i j }⟩
        pos := posOver cs i j pos
        i := j
  return (toks, diags)

end LeanTex.Core.Lex
