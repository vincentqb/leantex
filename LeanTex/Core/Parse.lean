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
  | verb (env : String) (s : String) (pos : Pos)
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

/-- An open delimiter, holding the items collected before it. `body` marks a
brace group that is one of an environment definer's two bodies. -/
private structure Frame where
  stop : Stop
  openPos : Pos
  outer : Array Raw
  body : Bool := false

/-- The definers whose two body groups are token lists: LaTeX's
`\newenvironment{name}{begin}{end}` defines `\name` and `\endname` as macros
(ltdefns.dtx), so an environment opened in the first and closed in the
second is balanced where the environment is used, never inside one body. -/
def envDefiners : List String :=
  ["newenvironment", "renewenvironment", "provideenvironment", "defineenv"]

/-- A definer body's half of a construct its other body completes — an
environment, or math opened with `$`, `\(` or `\[` — kept by name for the
definer to judge. The name holds a space, which no word token holds (`Lex`:
a word is a run of characters neither special nor white space), and a
document's environment name is one word (`envName`), so no document can
spell one. -/
def splitOpen (name : String) : String := "open " ++ name
def splitClose (name : String) : String := "close " ++ name

def splitOpen? (n : String) : Option String :=
  if n.startsWith "open " then some ((n.drop "open ".length).toString) else none

def splitClose? (n : String) : Option String :=
  if n.startsWith "close " then some ((n.drop "close ".length).toString) else none

/-- The name a half of a frame carries: the environment's name, or the
delimiter that opened the math. -/
def Stop.halfName : Stop → String
  | .env n => n
  | .math => "$"
  | .parenMath => "\\("
  | .displayMath => "\\["
  | .brace => "{"

/-- The frame a half's name records (`Stop.halfName` read back): a name is
an environment's unless it spells a math delimiter, which no word can. -/
def halfStop (name : String) : Stop :=
  if name == "$" then .math
  else if name == "\\(" then .parenMath
  else if name == "\\[" then .displayMath
  else .env name

/-- The two diagnostics a definer's settled halves raise (`Elab.settleSplits`)
are the parse's own, built here once. -/
def unclosedAtBrace (file : String) (stop : Stop) (pos : Pos) : Diag :=
  Diag.of .E0201 s!"unclosed: expected {stop.name} before the group's '}'" (some ⟨file, pos⟩)

def unmatchedEnd (file name : String) (pos : Pos) : Diag :=
  Diag.of .E0205 s!"'\\end\{{name}}' without matching '\\begin\{{name}}'" (some ⟨file, pos⟩)

/-- The index past the last item before `j` that is not a space. -/
private def backSkip (acc : Array Raw) (j : Nat) : Nat := Id.run do
  let mut k := j
  for _ in [0:j] do
    if k == 0 then break
    match acc[k - 1]? with
    | some .space => k := k - 1
    | _ => break
  return k

/-- The item just before index `k`, if any. -/
private def before (acc : Array Raw) (k : Nat) : Option Raw :=
  if k == 0 then none else acc[k - 1]?

private def isSym (c : Char) : Option Raw → Bool
  | some (.sym d _) => d == c
  | _ => false

/-- Does `acc` end, before `k0`, with a definer's head: option runs (`[..]`,
`(..)`), the name group, an optional `*`, and an `envDefiners` word? -/
private def definerHeadAt (acc : Array Raw) (k0 : Nat) : Bool := Id.run do
  let mut k := backSkip acc k0
  for _ in [0:acc.size] do
    let opener := if isSym ']' (before acc k) then '['
      else if isSym ')' (before acc k) then '(' else ' '
    if opener == ' ' then break
    let mut j := k - 1
    for _ in [0:k] do
      if j == 0 || isSym opener (before acc j) then break
      j := j - 1
    unless isSym opener (before acc j) do return false
    k := backSkip acc (j - 1)
  unless before acc k matches some (.group _ _) do return false
  k := backSkip acc (k - 1)
  if isSym '*' (before acc k) then k := backSkip acc (k - 1)
  match before acc k with
  | some (.ctrl d _) => return envDefiners.contains d
  | _ => return false

/-- How far back a definer head is sought from a body's `{`: a definer's
option runs (`[n]`, `[default]`, `(params)`), its name and its word are a
few items, so a window this wide holds the heads documents write, and the
scan at every `{` reads at most this many items — the parse stays linear
where scanning the level made it quadratic. -/
def definerReach : Nat := 128

/-- The items `envBodyNext` reads: the last `definerReach` of the level. -/
def definerWindow (acc : Array Raw) : Array Raw :=
  acc.extract (acc.size - definerReach) acc.size

/-- Is the group opening after `acc` one of an environment definer's two
bodies? Read off `definerWindow` alone (`envBodyNext_window_exact`). -/
private def envBodyNext (acc : Array Raw) : Bool :=
  let w := definerWindow acc
  let k := backSkip w w.size
  definerHeadAt w k ||
    (before w k matches some (.group _ _) && definerHeadAt w (k - 1))

/-- The window is its own window, so the verdict at a `{` depends on the
last `definerReach` items of the level and on nothing before them. -/
theorem definerWindow_fixed_point (acc : Array Raw) :
    definerWindow (definerWindow acc) = definerWindow acc := by
  unfold definerWindow
  rw [Array.extract_extract]
  simp only [Array.size_extract]
  have h1 : acc.size - definerReach
      + (min acc.size acc.size - (acc.size - definerReach) - definerReach)
      = acc.size - definerReach := by omega
  have h2 : min (acc.size - definerReach + (min acc.size acc.size - (acc.size - definerReach)))
      acc.size = acc.size := by omega
  rw [h1, h2]

private theorem envBodyNext_window_exact (acc : Array Raw) :
    envBodyNext acc = envBodyNext (definerWindow acc) := by
  simp only [envBodyNext, definerWindow_fixed_point]

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

/-- An open half settled to what a plain parse makes of it: its frame
closed at the body's brace, with that parse's diagnostic. -/
def settleOpenHalf (file name : String) (body : Array Raw) (pos : Pos) : Array Raw × Diag :=
  let stop := halfStop name
  ((⟨stop, pos, #[], false⟩ : Frame).close body, unclosedAtBrace file stop pos)

/-- The diagnostic a plain parse raises at a close half. -/
def closeHalfDiag (file name : String) (pos : Pos) : Diag :=
  match halfStop name with
  | .env n => unmatchedEnd file n pos
  | s => err file .E0202 s!"unexpected {s.name}" pos

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
        frames := frames.push ⟨.brace, pos, acc, envBodyNext acc⟩
        acc := #[]
      | .rbrace =>
        -- The group boundary wins: a delimiter opened inside `{...}` and
        -- still open at the `}` closes here, diagnosed — dropping the `}`
        -- instead would leave that frame to swallow everything after the
        -- group (a `\def` body's unbalanced `\begin{tabular}` once ate the
        -- rest of a venue's `.sty`, silently). In a definer's body the
        -- environment is the other body's to close: it is kept as a half.
        if frames.any (·.stop == .brace) then
          let body := (frames.findRev? (·.stop == .brace)).any (·.body)
          for _ in [0:frames.size] do
            match frames.back? with
            | some f =>
              if f.stop == .brace then break
              match body, f.stop with
              | true, s =>
                frames := frames.pop
                acc := f.outer.push (.env (splitOpen s.halfName) acc f.openPos)
              | _, _ =>
                diags := diags.push (unclosedAtBrace file f.stop f.openPos)
                frames := frames.pop
                acc := f.close acc
            | none => break
          match frames.back? with
          | some f =>
            frames := frames.pop
            acc := f.close acc
          | none => pure ()
        else
          diags := diags.push (err file .E0202 "unexpected '}'" pos)
      | .math =>
        match frames.back? with
        | some f =>
          if f.stop == .math then
            frames := frames.pop
            acc := f.close acc
          else
            frames := frames.push ⟨.math, pos, acc, false⟩
            acc := #[]
        | none =>
          frames := frames.push ⟨.math, pos, acc, false⟩
          acc := #[]
      | .ctrl "(" =>
        frames := frames.push ⟨.parenMath, pos, acc, false⟩
        acc := #[]
      | .ctrl ")" =>
        match frames.back? with
        | some f =>
          if f.stop == .parenMath then
            frames := frames.pop
            acc := f.close acc
          else if f.body then
            acc := acc.push (.env (splitClose Stop.parenMath.halfName) #[] pos)
          else
            diags := diags.push (err file .E0202 "unexpected '\\)'" pos)
        | none =>
          diags := diags.push (err file .E0202 "unexpected '\\)'" pos)
      | .ctrl "[" =>
        frames := frames.push ⟨.displayMath, pos, acc, false⟩
        acc := #[]
      | .ctrl "]" =>
        match frames.back? with
        | some f =>
          if f.stop == .displayMath then
            frames := frames.pop
            acc := f.close acc
          else if f.body then
            acc := acc.push (.env (splitClose Stop.displayMath.halfName) #[] pos)
          else
            diags := diags.push (err file .E0202 "unexpected '\\]'" pos)
        | none =>
          diags := diags.push (err file .E0202 "unexpected '\\]'" pos)
      | .ctrl "begin" =>
        let (name, j, ds) := envName toks file i pos
        diags := diags ++ ds
        i := j
        frames := frames.push ⟨.env name, pos, acc, false⟩
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
          | .brace =>
            if f.body then acc := acc.push (.env (splitClose name) #[] pos)
            else diags := diags.push (unmatchedEnd file name pos)
          | _ =>
            diags := diags.push (unmatchedEnd file name pos)
        | none =>
          diags := diags.push (unmatchedEnd file name pos)
      | .ctrl name => acc := acc.push (.ctrl name pos)
      | .word s => acc := acc.push (.word s pos)
      | .space => acc := acc.push .space
      | .par => acc := acc.push (.par pos)
      | .sym c => acc := acc.push (.sym c pos)
      | .verb env s => acc := acc.push (.verb env s pos)
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


/-- The option head of a listing environment's blind-captured body:
spaces and tabs, then `[...]` with `{}`-nesting respected (listings reads
its per-environment keys there; a bracket on a later line is content, as
in listings). Returns the option text and the index past the `]`, `none`
when no head stands or the bracket never closes. -/
def listingOptHead (s : String) : Option (String × Nat) := Id.run do
  let cs := s.toList.toArray
  let mut i := 0
  for _ in [0:cs.size] do
    if h : i < cs.size then
      if cs[i] == ' ' || cs[i] == '\t' then i := i + 1 else break
    else break
  if h : i < cs.size then
    if cs[i] != '[' then return none
    let mut depth : Nat := 0
    let mut j := i + 1
    let mut out := ""
    for _ in [0:cs.size] do
      if h2 : j < cs.size then
        let c := cs[j]
        if c == '{' then depth := depth + 1
        else if c == '}' then depth := depth - 1
        if c == ']' && depth == 0 then
          return some (out, j + 1)
        out := out.push c
        j := j + 1
      else break
    return none
  else return none

/-- The mandatory `{language}` head of a `{minted}` body, after any option
head. Shared by defaults injection and elaboration so both read the same
lexer name without changing the captured source. -/
def mintedLangHead (s : String) (start : Nat) : Option (String × Nat) := Id.run do
  let cs := s.toList.toArray
  let mut i := start
  for _ in [0:cs.size] do
    if h : i < cs.size then
      if cs[i] == ' ' || cs[i] == '\t' then i := i + 1 else break
    else break
  if h : i < cs.size then
    if cs[i] != '{' then return none
    let mut j := i + 1
    let mut out := ""
    for _ in [0:cs.size] do
      if h2 : j < cs.size then
        let c := cs[j]
        if c == '}' then return some (out, j + 1)
        out := out.push c
        j := j + 1
      else break
    return none
  else return none

/-! `Raw` back to source text. Declaration blocks and lengths are parsed from
this string, so it must round-trip what the lexer accepted. -/

/-- The synthetic environment the driver wraps an `\input` file's content in,
so every stage downstream knows which file a position belongs to. The name
holds a space, as a split half's does (`splitOpen`), so no document can
forge one. -/
def inputEnv (file : String) : String := "input " ++ file

def inputEnvFile? (name : String) : Option String :=
  if name.startsWith "input " then some ((name.drop "input ".length).toString)
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
  | .verb env s _ =>
    if env == "verb" then
      let d := (['|', '!', '+', '=', '/', '"', '@'].find? (fun c => !s.contains c)).getD '|'
      s!"\\verb{d}{s}{d}"
    else s!"\\begin\{{env}}{s}\\end\{{env}}"

end

end LeanTex.Core.Parse
