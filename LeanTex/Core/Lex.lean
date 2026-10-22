module

public import LeanTex.Core.Diag
import LeanTex.Core.Nfc
import LeanTex.Core.Definer

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

/-- Text symbols, which take no argument, so the space after them is content. -/
@[expose] public def textSymbols : List (String × String) :=
  [("middot", "·"), ("bullet", "•"), ("endash", "–"),
   ("emdash", "—"), ("ldots", "…"), ("dots", "…"),
   ("times", "×"), ("copyright", "©"), ("degree", "°"),
   ("nbsp", " "), ("thinspace", " ")]

/-- Whether a character continues a control name; `@` always does. -/
@[expose] public def nameChar (c : Char) : Bool :=
  c.isAlpha || c == '@'

/-- The special characters, fixed: no catcode reprogramming. -/
@[expose] public def special (c : Char) : Bool :=
  c == '\\' || c == '{' || c == '}' || c == '$' || c == '%' ||
  c == '[' || c == ']' || c == '&' || c == '#' || c == '^' || c == '_' || c == '~'

@[expose] public def isWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def scanWhile (cs : Array Char) (j : Nat) (p : Char → Bool) : Nat :=
  if h : j < cs.size then
    if p cs[j] then scanWhile cs (j + 1) p else j
  else j
termination_by cs.size - j

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

/-- The tokens of a whitespace run with `n` line ends: one space mid-line, then
a paragraph per blank line. -/
public def wsTokens (lineStart : Bool) (n : Nat) : List Tok :=
  if lineStart then List.replicate n .par
  else .space :: List.replicate (n - 1) .par

public theorem blank_line_par_agree (n : Nat) :
    (wsTokens false (n + 1)).tail = wsTokens true n := by
  simp [wsTokens]

/-- The mid-line whitespace run: a single line end against a
group brace is dropped. -/
public def midlineWs (prevLbrace nextRbrace : Bool) (n : Nat) : List Tok :=
  if n = 1 ∧ (prevLbrace = true ∨ nextRbrace = true) then []
  else wsTokens false n

private def matchFrom (cs ps : Array Char) (i k : Nat) : Bool :=
  if h : k < ps.size then
    match cs[i + k]? with
    | some c => c == ps[k] && matchFrom cs ps i (k + 1)
    | none => false
  else true
termination_by ps.size - k

private def matchAt (cs : Array Char) (i : Nat) (ps : Array Char) : Bool :=
  i + ps.size ≤ cs.size && matchFrom cs ps i 0

private def findSub (cs : Array Char) (k : Nat) (pat : Array Char) : Option Nat :=
  if k < cs.size then
    if matchAt cs k pat then some k else findSub cs (k + 1) pat
  else none
termination_by cs.size - k

/-- The string over `[a, b)`. -/
private def strFrom (cs : Array Char) (a b : Nat) : String :=
  cs.foldl String.push "" a b

/-- A line end at `k`: where the next line starts, a CRLF one unit. -/
private def lineEndAt (cs : Array Char) (k : Nat) : Option Nat :=
  match cs[k]? with
  | some '\n' => some (k + 1)
  | some '\r' => some (if cs[k + 1]? == some '\n' then k + 2 else k + 1)
  | _ => none

/-- The index past the spaces at `k` and at most one line end, as TeX's argument
reader skips them; `none` at a blank line. -/
public def argGap (cs : Array Char) (k : Nat) (comments : Bool := true) : Option Nat := Id.run do
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

/-- The commands whose next token is the name they define or
show, never a call. -/
private def definers : List String :=
  Definer.namedNext ++ ["show", "meaning", "string", "noexpand"]

/-- Whether the last token, past white space and a definer's
star, is a definer. -/
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

/-- minted's `\mintinline` and `\mint`, read from just past the command name as
minted.sty reads them, or listings' `\lstinline`, which names no `{language}`, where `lang` is false. -/
private def mintedCall (cs : Array Char) (j : Nat) (lang : Bool := true) :
    Option (Nat × Bool × String) := Id.run do
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
  if lang then
    unless cs[k]? == some '{' do return none
    -- The language is one group, the groups it holds nested in it.
    let close : Nat := Id.run do
      let mut depth : Nat := 0
      let mut m := k + 1
      for _ in [k + 1:cs.size] do
        match cs[m]? with
        | some '}' =>
          if depth == 0 then return m
          depth := depth - 1
          m := m + 1
        | some '{' => depth := depth + 1; m := m + 1
        | some '\n' | some '\r' | none => return m
        | some _ => m := m + 1
      return m
    unless cs[close]? == some '}' do return none
    head := head ++ strFrom cs k (close + 1)
    k := close + 1
  let some code := argGap cs k (comments := false) | return some (k, false, head)
  -- A closing brace opens no code.
  if cs[code]? == some '}' then return none
  -- A blank line ends the code.
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

/-- The written control token, before NFC changes any spelling. -/
private def writtenControl (source : Array Char) (i : Nat) : Option String := do
  guard (source[i]? == some '\\')
  let c ← source[i + 1]?
  let stop := if nameChar c then scanWhile source (i + 1) nameChar
    else if c == '\r' && source[i + 2]? == some '\n' then i + 3 else i + 2
  return strFrom source i stop

/-- url.sty's commands, which read their argument verbatim. -/
@[expose] public def urlCommands : List String := ["url", "nolinkurl", "path"]

/-- A url.sty argument from its delimiter at `k` to the delimiter's next copy on the line; none
where a brace, a letter, a TeX special or what opens a TikZ path's operation stands there (`(`, `[`,
`;`, `<`, `:`, `+(`, `++`, `--`, `-|`, `|-`). -/
public def urlFrom (cs : Array Char) (k : Nat) : Option (Nat × Bool × String) := do
  let d ← cs[k]?
  guard (!d.isAlphanum && !d.isWhitespace && !"{}\\%$&#^_~([;<:".contains d)
  let next := cs[k + 1]?
  guard (d != '+' || !(next == some '(' || next == some '+'))
  guard (d != '-' || !(next == some '-' || next == some '|'))
  guard (d != '|' || next != some '-')
  let e := scanWhile cs (k + 1) (fun c => c != d && c != '\n' && c != '\r')
  let stop := if cs[e]? == some d then e + 1 else e
  return (stop, cs[e]? == some d, strFrom cs k stop)

/-- A url.sty command's delimited argument, read from just past the command name. -/
public def urlDelimited (cs : Array Char) (j : Nat) : Option (Nat × Bool × String) := do
  urlFrom cs (← argGap cs j (comments := false))

/-- `\verb`'s argument from just past its name: a star showing spaces, blanks skipped, then the text
to its delimiter's next copy on the line. -/
public def verbRead (cs : Array Char) (j : Nat) : Nat × Bool × String :=
  let star := cs[j]? == some '*'
  let k := scanWhile cs (if star then j + 1 else j) (fun c => c == ' ' || c == '\t')
  let d := (cs[k]?).getD '\n'
  let e := if d == '\n' || d == '\r' then k
    else scanWhile cs (k + 1) (fun c => c != d && c != '\n' && c != '\r')
  let closed := d != '\n' && d != '\r' && cs[e]? == some d
  let body := if d == '\n' || d == '\r' then "" else strFrom cs (k + 1) e
  let shown := if star then body.map (fun c => if c == ' ' then '␣' else c) else body
  (if closed then e + 1 else e, closed, shown)

/-- A lexically blind environment's body from `start` to its closer's first copy, or to the end. -/
public def envRead (cs : Array Char) (start : Nat) (closer : Array Char) : Nat × Bool × String :=
  match findSub cs start closer with
  | some k => (k + closer.size, true, strFrom cs start k)
  | none => (cs.size, false, strFrom cs start cs.size)

/-- A form whose argument the lexer reads raw: a blind environment's body up to its closer, `\verb`'s
text between two copies of its delimiter, and a url.sty argument with its delimiters. -/
public inductive Capture where
  | env (closer : Array Char)
  | verb
  | url

/-- A line end, which no one-line capture crosses. -/
@[expose] public def lineEnd (c : Char) : Bool := c == '\n' || c == '\r'

/-- The characters of `p` stand in `cs` from `m`. -/
@[expose] public def occursAt (cs p : Array Char) (m : Nat) : Prop :=
  ∀ t (h : t < p.size), cs[m + t]? = some p[t]

/-- Every character strictly between `a` and `b` is neither `d` nor a line end. -/
@[expose] public def plainBetween (cs : Array Char) (d : Char) (a b : Nat) : Prop :=
  ∀ m, a < m → m < b → ∃ c, cs[m]? = some c ∧ c ≠ d ∧ lineEnd c = false

/-- What a capture read from `j` owes: its text is the source characters it spans, `\verb*` showing
each space as `␣`, ending at its closer's first copy, or where none stands on its line or in the input. -/
@[expose] public def Capture.Exact : Capture → Array Char → Nat → Nat × Bool × String → Prop
  | .env closer, cs, start, (stop, closed, s) =>
    ∃ k, s.toList = (cs.extract start k).toList ∧
      (∀ m, start ≤ m → m < k → ¬ occursAt cs closer m) ∧
      (if closed then start ≤ k ∧ occursAt cs closer k ∧ stop = k + closer.size
        else k = cs.size ∧ stop = cs.size)
  | .verb, cs, j, (stop, closed, s) =>
    let star := cs[j]? == some '*'
    let k₀ := if star then j + 1 else j
    ∃ k, k₀ ≤ k ∧ (∀ m, k₀ ≤ m → m < k → cs[m]? = some ' ' ∨ cs[m]? = some '\t') ∧
      (∀ c, cs[k]? = some c → c ≠ ' ' ∧ c ≠ '\t') ∧
      match cs[k]? with
      | some d =>
        if lineEnd d then stop = k ∧ closed = false ∧ s = ""
        else ∃ e, k < e ∧ plainBetween cs d k e ∧
          s.toList = (cs.extract (k + 1) e).toList.map
            (fun c => if star && c == ' ' then '␣' else c) ∧
          (closed = true ↔ cs[e]? = some d) ∧
          (closed = false → ∀ c, cs[e]? = some c → lineEnd c = true) ∧
          stop = (if closed then e + 1 else e)
      | none => stop = k ∧ closed = false ∧ s = ""
  | .url, cs, k, (stop, closed, s) =>
    ∃ d e, cs[k]? = some d ∧ lineEnd d = false ∧ k < e ∧ plainBetween cs d k e ∧
      s.toList = (cs.extract k stop).toList ∧
      (closed = true ↔ cs[e]? = some d) ∧
      (closed = false → ∀ c, cs[e]? = some c → lineEnd c = true) ∧
      stop = (if closed then e + 1 else e)

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

/-- The original-source map of the NFC slices between structural ASCII
characters and whitespace. -/
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

/-- The original span of a normalized token boundary, admitted only where
normalizing its slices agrees. -/
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

/-- The lexically blind environments, whose bodies are captured raw in one token: the token's
environment, the name written, and the opener and closer the capture spans. -/
private def verbEnvs : Array (String × String × Array Char × Array Char) :=
  #["verbatim", "lstlisting", "minted"].map fun n =>
    (n, n, s!"\{{n}}".toList.toArray, s!"\\end\{{n}}".toList.toArray)

/-- fancyvrb's environment captured as minted's code block in the `text` lexer, whose keys are
fancyvrb's. -/
private def fancyEnv (n : String) : String × String × Array Char × Array Char :=
  ("minted", n, s!"\{{n}}".toList.toArray, s!"\\end\{{n}}".toList.toArray)

/-- The index of the `]` closing an option list, outside every brace group. -/
private def optionEnd : List Char → Nat → Nat → Option Nat
  | [], _, _ => none
  | ']' :: _, 0, n => some n
  | '{' :: rest, d, n => optionEnd rest (d + 1) (n + 1)
  | '}' :: rest, d, n => optionEnd rest (d - 1) (n + 1)
  | _ :: rest, d, n => optionEnd rest d (n + 1)

/-- A fancyvrb environment's body as minted's: the options its definition gives, then those written
after `\begin`, and the `text` lexer. -/
private def fancyBody (defined body : String) : String :=
  let (written, rest) := match body.toList with
    | '[' :: tl => match optionEnd tl 0 0 with
      | some n => (String.ofList (tl.take n), String.ofList (tl.drop (n + 1)))
      | none => ("", body)
    | _ => ("", body)
  let opts := ",".intercalate ([defined, written].filter (!·.isEmpty))
  (if opts.isEmpty then "" else "[" ++ opts ++ "]") ++ "{text}" ++ rest

/-- The index past spaces and `%` comments from `k`. -/
private def skipBlank (cs : Array Char) (k : Nat) : Nat := Id.run do
  let mut k := scanWhile cs k isWs
  for _ in [0:cs.size] do
    if cs[k]? != some '%' then break
    k := scanWhile cs (scanWhile cs k (· != '\n')) isWs
  return k

/-- The text of the brace group at `k` after blanks, and the index past it. -/
private def groupText (cs : Array Char) (k : Nat) : Option (String × Nat) := Id.run do
  let k := skipBlank cs k
  unless cs[k]? == some '{' do return none
  let mut depth := 0
  let mut j := k
  for _ in [k:cs.size] do
    match cs[j]? with
    | some '{' => depth := depth + 1
    | some '}' =>
      depth := depth - 1
      if depth == 0 then return some (strFrom cs (k + 1) j, j + 1)
    | some '\\' => j := j + 1
    | _ => pure ()
    j := j + 1
  return none

/-- The index past `\\verbatim` or `\\begin{verbatim}` at `k` (the `end` spellings when `close`), and
whether it was written as the environment, which a definition's text cannot hold under LaTeX. -/
private def verbHalf (cs : Array Char) (k : Nat) (close : Bool) : Option (Nat × Bool) :=
  let env := (if close then "\\end{verbatim}" else "\\begin{verbatim}").toList.toArray
  let cmd := (if close then "\\endverbatim" else "\\verbatim").toList.toArray
  if matchAt cs k env then some (k + env.size, true)
  else if matchAt cs k cmd && !(cs[k + cmd.size]?.any nameChar) then some (k + cmd.size, false)
  else none

/-- The name an environment definition from `j` defines, and the index past its group. -/
private def envDefName (cs : Array Char) (j : Nat) : Option (String × Nat) := do
  let k := skipBlank cs j
  guard (cs[k]? == some '{')
  let e := scanWhile cs (k + 1) fun c => c != '}' && c != '{' && c != '\\' && !isWs c
  guard (e > k + 1 && cs[e]? == some '}')
  return (strFrom cs (k + 1) e, e + 1)

/-- An environment a definition from `j` makes verbatim, its begin and end code `\\verbatim` and
`\\endverbatim` as the verbatim package reads them, or the environment's own spellings; its name,
whether the environment was spelled, and the index past the definition. -/
private def verbEnvDef (cs : Array Char) (j : Nat) : Option (String × Bool × Nat) := do
  let (name, e) ← envDefName cs j
  let b := skipBlank cs e
  guard (cs[b]? == some '{')
  let (b, spelled) ← verbHalf cs (skipBlank cs (b + 1)) false
  let b := skipBlank cs b
  guard (cs[b]? == some '}')
  let c := skipBlank cs (b + 1)
  guard (cs[c]? == some '{')
  let (c, spelledEnd) ← verbHalf cs (skipBlank cs (c + 1)) true
  let c := skipBlank cs c
  guard (cs[c]? == some '}')
  return (name, spelled || spelledEnd, c + 1)

public def lex (file : String) (input : String) : Array Token × Array Diag := Id.run do
  -- Normalized to NFC here, once, so every consumer sees one canonical spelling.
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
  -- How deep the scan stands in TikZ pictures, whose `\path` is TikZ's own.
  let mut tikz : Nat := 0
  -- The verbatim environments, the document's among them, and where a definition read ends.
  let mut verbs := verbEnvs.push (fancyEnv "Verbatim")
  -- Each fancyvrb environment's options from its `\DefineVerbatimEnvironment`.
  let mut fancy : Array (String × String) := #[("Verbatim", "")]
  let mut verbDefStop : Nat := 0
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
        -- A single line end against a group brace is dropped, as LaTeX's `{%` drops it.
        for tok in midlineWs prevLbrace nextRbrace n do
          toks := toks.push ⟨tok, here⟩
        -- The space TeX reads there stays on the brace.
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
            if (name == "begin" || name == "end") && matchAt cs j "{tikzpicture}".toList.toArray then
              tikz := if name == "begin" then tikz + 1 else tikz - 1
            if name == "DefineVerbatimEnvironment" then
              if let some (env, k) := groupText cs j then
                if let some (base, k) := groupText cs k then
                  if let some (opts, _) := groupText cs k then
                    if let some (_, given) := fancy.find? (·.1 == base.trimAscii.toString) then
                      let env := env.trimAscii.toString
                      verbs := (verbs.filter (·.2.1 != env)).push (fancyEnv env)
                      fancy := (fancy.filter (·.1 != env)).push
                        (env, ",".intercalate ([given, opts.trimAscii.toString].filter (!·.isEmpty)))
            if (name == "newenvironment" || name == "renewenvironment") then
              match verbEnvDef cs j, envDefName cs j with
              | some (env, spelled, stop), _ =>
                verbs := (verbs.filter (·.2.1 != env)).push
                  ("verbatim", env, s!"\{{env}}".toList.toArray, s!"\\end\{{env}}".toList.toArray)
                verbDefStop := stop
                if spelled then
                  diags := diags.push (Diag.of .W0411
                    s!"'\\begin\{verbatim}' in a definition's text does not compile under LaTeX; \
'\{{env}}' sets its body verbatim" (some ⟨file, here⟩)
                    (help := s!"\\newenvironment\{{env}}\{\\verbatim}\{\\endverbatim} with the \
verbatim package spells it"))
              | none, some (env, _) =>
                -- A definition of any other text ends the document's verbatim one.
                verbs := verbs.filter fun v => v.2.1 != env || verbEnvs.any (·.2.1 == env)
              | none, none => pure ()
            if i < verbDefStop && (name == "begin" || name == "end") &&
                matchAt cs j "{verbatim}".toList.toArray then
              -- A definition's verbatim halves, read as the verbatim package's commands.
              toks := toks.push ⟨.ctrl (if name == "begin" then "verbatim" else "endverbatim"), here⟩
              let stop := j + "{verbatim}".length
              pos := posOver cs i stop pos
              i := stop
            else if let some (env, written, opener, closer) :=
                (if name == "begin" then verbs.find? (fun e => matchAt cs j e.2.2.1) else none) then
              -- verbatim and the listing environments capture raw content in one token.
              let (stop, closed, body) := envRead cs (j + opener.size) closer
              if closed then
                let body := match (fancy.find? (·.1 == written)).map (·.2) with
                  | some given => if env == "minted" then fancyBody given body else body
                  | none => body
                toks := toks.push ⟨.verb env body, here⟩
              else
                diags := diags.push (Diag.of .E0102 (Diag.say .E0102 .environment written)
                  (some ⟨file, here⟩))
                toks := toks.push ⟨.verb env body, here⟩
              pos := posOver cs i stop pos
              i := stop
            else if name == "verb" then
              let (stop, closed, shown) := verbRead cs j
              unless closed do
                diags := diags.push (Diag.of .E0102 (Diag.say .E0102 .command "\\verb")
                  (some ⟨file, here⟩) (detail := some "no second delimiter on its line"))
              toks := toks.push ⟨.verb "verb" shown, here⟩
              pos := posOver cs i stop pos
              i := stop
            else if let some (stop, closed, call) :=
                (if (name == "mintinline" || name == "mint") && !definesNext toks then
                  mintedCall cs j
                else if name == "lstinline" && !definesNext toks then mintedCall cs j (lang := false)
                else if urlCommands.contains name && tikz == 0 && !definesNext toks then
                  urlDelimited cs j
                else none) then
              -- minted's, listings' and url.sty's inline commands read their argument raw, as
              -- `\verb` does.
              unless closed do
                diags := diags.push (Diag.of .E0102 (Diag.say .E0102 .command s!"\\{name}")
                  (some ⟨file, here⟩)
                  (detail := some (if urlCommands.contains name then
                    "no second delimiter on its line"
                  else "no closing delimiter before a blank line")))
              toks := toks.push ⟨.verb name call, here⟩
              pos := posOver cs i stop pos
              i := stop
            else
              toks := toks.push ⟨.ctrl name, here⟩
              pos := posOver cs i j pos
              i := j
              -- A control word swallows the whitespace after it; a text symbol does not.
              unless (textSymbols.lookup name).isSome do
                let k := scanWhile cs i isWs
                for tok in wsTokens true (newlines cs i k - 1) do
                  toks := toks.push ⟨tok, sourcePos i pos⟩
                pos := posOver cs i k pos
                i := k
          else if c1 == '\n' || c1 == '\r' then
            -- `\` ending a line is the control space.
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
          diags := diags.push (Diag.of .E0101 (Diag.say .E0101 .character "\\")
            (some ⟨file, here⟩) (detail := some "at the end of input"))
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
        -- In `$x$$y$` the middle pair closes one formula and opens the next.
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
