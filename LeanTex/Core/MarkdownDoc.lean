module

public import LeanTex.Core.Ir
import LeanTex.Core.CiteKey
import LeanTex.Core.Nfc
import LeanTex.Core.MdSmart
import LeanTex.Core.Contents
import Std.Data.HashSet

/-! The markdown backend: the llms.txt twin of the IR the HTML and PDF backends
read, written to read back as the same document. -/

namespace LeanTex.Core.MarkdownDoc

open LeanTex.Core LeanTex.Core.Ir

/-- Whether an `@` would open a citation on reading back: not after a letter, a digit or a `.`,
and before a key's first character or its brace. -/
private def citeOpens (prev : Option Char) (rest : List Char) : Bool :=
  !(prev.any fun p => CiteKey.isAlnum p || p == '.') &&
    (rest.head?.any fun d => CiteKey.regular d || d == '{')

/-- Escapes the characters that would read as markup anywhere in a line, after `prev`; an `@` that
would open a citation where `ats` says the twin reads citations. -/
private def escapeCharsFrom (pipes ats : Bool) (prev : Option Char) : List Char → List Char
  | [] => []
  | c :: rest =>
    if c == '\\' || c == '`' || c == '*' || c == '_' || c == '[' || c == ']'
        || (pipes && c == '|') || c == '<' || c == '&' || (c == '@' && ats && citeOpens prev rest) then
      '\\' :: c :: escapeCharsFrom pipes ats (some c) rest
    -- A line ending inside text has no other spelling.
    else if c == '\n' then '&' :: '#' :: '1' :: '0' :: ';' :: escapeCharsFrom pipes ats (some c) rest
    else if c == '\r' then '&' :: '#' :: '1' :: '3' :: ';' :: escapeCharsFrom pipes ats (some c) rest
    else c :: escapeCharsFrom pipes ats (some c) rest

/-- Escapes the characters that would read as markup anywhere in a line. -/
private def escapeChars (pipes ats : Bool) (l : List Char) : List Char :=
  escapeCharsFrom pipes ats none l

private def escapeText (pipes ats : Bool) (s : String) : String :=
  String.ofList (escapeChars pipes ats s.toList)

/-- Written text `s` after `acc` as Pandoc's smart punctuation reads it back after an abbreviation:
a space a reference to it, a no-break space with a word but no citation's spelling after it a plain
space it joins again. -/
private def keepAbbrevSpaces (acc s : String) : String := Id.run do
  if !s.contains ' ' && !s.contains '\u00a0' then return s
  let tail := (acc.takeEndWhile fun c => CiteKey.isAlnum c || c == '.').toString.toList.toArray
  let cs := tail ++ s.toList.toArray
  let mut out := ""
  for k in [tail.size:cs.size] do
    let c := cs[k]?.getD ' '
    out := if c == ' ' && MdSmart.joinsAt cs k then out ++ "&#32;"
      else if c == '\u00a0' && (cs[k + 1]?.any fun d => d != ' ' && d != '\t' && d != '\u00a0') &&
          !MdSmart.citesAt cs (k + 1) && MdSmart.joinsAt cs k then out.push ' '
      else out.push c
  return out

private theorem escapeCharsFrom_line (pipes ats : Bool) :
    (prev : Option Char) → (l : List Char) →
      ∀ x ∈ escapeCharsFrom pipes ats prev l, x ≠ '\n' ∧ x ≠ '\r'
  | _, [], x, hx => by simp [escapeCharsFrom] at hx
  | prev, c :: rest, x, hx => by
    have ih := escapeCharsFrom_line pipes ats (some c) rest x
    by_cases hn : c = '\n'
    · subst hn
      simp [escapeCharsFrom, citeOpens] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | hx
      all_goals first | decide | exact ih hx
    · by_cases hr : c = '\r'
      · subst hr
        simp [escapeCharsFrom, citeOpens] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | hx
        all_goals first | decide | exact ih hx
      · have hn' : (c == '\n') = false := by simpa using hn
        have hr' : (c == '\r') = false := by simpa using hr
        have hmem : x = '\\' ∨ x = c ∨ x ∈ escapeCharsFrom pipes ats (some c) rest := by
          unfold escapeCharsFrom at hx
          simp only [hn', hr', Bool.false_eq_true, ↓reduceIte] at hx
          split at hx
          · simp only [List.mem_cons] at hx
            rcases hx with h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
          · simp only [List.mem_cons] at hx
            rcases hx with h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
        rcases hmem with rfl | rfl | hx
        · decide
        · exact ⟨hn, hr⟩
        · exact ih hx

private theorem escapeChars_line (pipes ats : Bool) (l : List Char) :
    ∀ x ∈ escapeChars pipes ats l, x ≠ '\n' ∧ x ≠ '\r' :=
  escapeCharsFrom_line pipes ats none l

/-- Whether the rest of a line is a space, a tab or nothing, as must follow a
list marker or an ATX opening. -/
@[expose] public def spaceOrEnd : List Char → Bool
  | [] => true
  | x :: _ => x == ' ' || x == '\t'

/-- After an ATX heading's first `#`: up to five more, then a space, a tab or
the line's end (§4.2). -/
@[expose] public def atxRest : Nat → List Char → Bool
  | 0, l => spaceOrEnd l
  | n + 1, '#' :: rest => atxRest n rest
  | _ + 1, l => spaceOrEnd l

/-- A line of `c` and spaces or tabs alone, holding at least three `c`: a
thematic break (§4.1). -/
@[expose] public def thematic (c : Char) (l : List Char) : Bool :=
  l.all (fun x => x == c || x == ' ' || x == '\t') && l.count c ≥ 3

/-- A line of `c` alone, then spaces or tabs: a setext underline (§4.3). -/
@[expose] public def underline (c : Char) (l : List Char) : Bool :=
  let rest := l.dropWhile (· == c)
  rest.length < l.length && rest.all (fun x => x == ' ' || x == '\t')

/-- After an ordered marker's first digit: more digits, then `.` or `)`, then a
space, a tab or the line's end (§5.2). -/
@[expose] public def orderedRest : List Char → Bool
  | [] => false
  | c :: rest =>
    if c.isDigit then orderedRest rest else (c == '.' || c == ')') && spaceOrEnd rest

/-- Whether a line read where markdown reads a paragraph's line opens a block
(CommonMark 0.31.2 §4–5). -/
@[expose] public def opensBlockChars : List Char → Bool
  | [] => false
  | c :: rest =>
    c == ' ' || c == '\t' || c == '>' ||
      (c == '#' && atxRest 5 rest) ||
      ((c == '-' || c == '+' || c == '*') && spaceOrEnd rest) ||
      ((c == '-' || c == '*' || c == '_') && thematic c (c :: rest)) ||
      ((c == '-' || c == '=') && underline c (c :: rest)) ||
      (c == '~' && rest.take 2 == ['~', '~']) ||
      (c == '`' && rest.take 2 == ['`', '`'] && !(rest.dropWhile (· == '`')).contains '`') ||
      (c.isDigit && orderedRest rest)

@[expose] public def opensBlock (s : String) : Bool := opensBlockChars s.toList

/-- A paragraph line as the twin writes it: leading spaces dropped and, where it
would open a block, its first character escaped. -/
@[expose] public def escapeLineStart (s : String) : String :=
  let cs := s.toList.dropWhile (fun c => c == ' ' || c == '\t')
  if !opensBlockChars cs then String.ofList cs
  else match cs with
    | [] => ""
    | c :: rest =>
      if c.isDigit then
        let ds := (c :: rest).takeWhile Char.isDigit
        String.ofList (ds ++ '\\' :: (c :: rest).drop ds.length)
      else String.ofList ('\\' :: c :: rest)

private theorem orderedRest_escaped : (ds : List Char) → (∀ c ∈ ds, c.isDigit = true) →
    (m : List Char) → orderedRest (ds ++ '\\' :: m) = false
  | [], _, m => by simp [orderedRest]
  | d :: ds, h, m => by
    simp only [List.cons_append, orderedRest, h d (List.mem_cons_self ..), ite_true]
    exact orderedRest_escaped ds (fun c hc => h c (List.mem_cons_of_mem _ hc)) m

private theorem digit_beq {c : Char} (hc : c.isDigit = true) (d : Char) (hd : d.isDigit = false) :
    (c == d) = false := by
  cases h : c == d
  · rfl
  · have : c = d := by simpa using h
    subst this
    rw [hc] at hd
    exact absurd hd (by decide)

private theorem opensBlockChars_escaped (cs : List Char) : opensBlockChars ('\\' :: cs) = false := by
  simp [opensBlockChars]

public theorem escapeLineStart_contract (s : String) : opensBlock (escapeLineStart s) = false := by
  unfold escapeLineStart opensBlock
  generalize hcs : s.toList.dropWhile (fun c => c == ' ' || c == '\t') = cs
  by_cases ho : opensBlockChars cs = true
  · simp only [ho, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases cs with
    | nil => simp [opensBlockChars] at ho
    | cons c rest =>
      simp only
      by_cases hd : c.isDigit = true
      · simp only [hd, ↓reduceIte, String.toList_ofList]
        have hpre : (c :: rest).takeWhile Char.isDigit = c :: rest.takeWhile Char.isDigit := by
          simp [hd]
        rw [hpre]
        have hds : ∀ x ∈ rest.takeWhile Char.isDigit, x.isDigit = true :=
          List.all_eq_true.mp List.all_takeWhile
        simp only [opensBlockChars, List.cons_append, List.length_cons, List.drop_succ_cons,
          digit_beq hd ' ' (by decide), digit_beq hd '\t' (by decide), digit_beq hd '>' (by decide),
          digit_beq hd '#' (by decide), digit_beq hd '-' (by decide), digit_beq hd '+' (by decide),
          digit_beq hd '*' (by decide), digit_beq hd '_' (by decide), digit_beq hd '=' (by decide),
          digit_beq hd '~' (by decide), digit_beq hd '`' (by decide), hd,
          orderedRest_escaped _ hds, Bool.false_and, Bool.or_false, Bool.and_false]
      · simp only [hd, Bool.false_eq_true, ↓reduceIte, String.toList_ofList]
        exact opensBlockChars_escaped (c :: rest)
  · simp only [Bool.not_eq_true] at ho
    simp [ho, String.toList_ofList]

/-- Every `|` escaped as `\|`. -/
@[expose] public def escapePipes : List Char → List Char
  | [] => []
  | c :: rest => if c == '|' then '\\' :: '|' :: escapePipes rest else c :: escapePipes rest

/-- A row read from inside a cell: the cell's text, then the cells after it;
`held` marks a pending backslash. -/
@[expose] public def gfmSplit : Bool → List Char → List Char × List (List Char)
  | false, [] => ([], [])
  | true, [] => (['\\'], [])
  | false, c :: rest =>
    if c == '|' then
      let r := gfmSplit false rest
      ([], r.1 :: r.2)
    else if c == '\\' then gfmSplit true rest
    else
      let r := gfmSplit false rest
      (c :: r.1, r.2)
  | true, c :: rest =>
    if c == '|' then
      let r := gfmSplit false rest
      ('|' :: r.1, r.2)
    else if c == '\\' then
      let r := gfmSplit true rest
      ('\\' :: r.1, r.2)
    else
      let r := gfmSplit false rest
      ('\\' :: c :: r.1, r.2)

/-- The white space GFM trims around a cell. -/
@[expose] public def gfmSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0B' || c == '\x0C'

/-- A cell's text without the white space around it. -/
@[expose] public def gfmTrim (cs : List Char) : List Char :=
  ((cs.dropWhile gfmSpace).reverse.dropWhile gfmSpace).reverse

/-- A row written between a leading and a trailing pipe, as GFM reads it: the
cells between, each trimmed. -/
@[expose] public def gfmRow (line : String) : List String :=
  let r := gfmSplit false line.toList
  ((r.1 :: r.2).drop 1).dropLast.map fun c => String.ofList (gfmTrim c)

/-- A row's cells after its leading pipe, each padded by spaces, its pipes
escaped, and closed by a pipe. -/
@[expose] public def rowCells : List String → List Char
  | [] => []
  | c :: cs => ' ' :: escapePipes c.toList ++ ' ' :: '|' :: rowCells cs

/-- A pipe table row, `| a | b |`. -/
@[expose] public def rowLine (cells : List String) : String :=
  String.ofList ('|' :: rowCells cells)

private theorem gfmSplit_held (l : List Char) (h : l.head? ≠ some '|') :
    gfmSplit true l = ('\\' :: (gfmSplit false l).1, (gfmSplit false l).2) := by
  cases l with
  | nil => rfl
  | cons c rest =>
    have hc : (c == '|') = false := by
      simpa using h
    by_cases hb : c = '\\'
    · subst hb
      simp [gfmSplit]
    · have hb' : (c == '\\') = false := by simpa using hb
      simp [gfmSplit, hc, hb']

private theorem escapePipes_head (c rest : List Char) (h : rest.head? ≠ some '|') :
    (escapePipes c ++ rest).head? ≠ some '|' := by
  cases c with
  | nil => simpa only [escapePipes, List.nil_append] using h
  | cons x c' =>
    by_cases hx : x = '|'
    · subst hx
      simp [escapePipes]
    · have hx' : (x == '|') = false := by simpa using hx
      simp [escapePipes, hx', hx]

private theorem gfmSplit_escapePipes (c rest : List Char) (h : rest.head? ≠ some '|') :
    gfmSplit false (escapePipes c ++ rest) =
      (c ++ (gfmSplit false rest).1, (gfmSplit false rest).2) := by
  induction c with
  | nil => rfl
  | cons x c' ih =>
    by_cases hx : x = '|'
    · subst hx
      simp only [escapePipes, beq_self_eq_true, ↓reduceIte, List.cons_append]
      simp [gfmSplit, ih]
    · have hx' : (x == '|') = false := by simpa using hx
      by_cases hb : x = '\\'
      · subst hb
        simp only [escapePipes, hx', Bool.false_eq_true, ↓reduceIte, List.cons_append]
        simp only [gfmSplit, hx', Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
        rw [gfmSplit_held _ (escapePipes_head c' rest h), ih]
      · have hb' : (x == '\\') = false := by simpa using hb
        simp only [escapePipes, hx', Bool.false_eq_true, ↓reduceIte, List.cons_append]
        simp [gfmSplit, hx', hb', ih]

private theorem gfmSplit_rowCells (cells : List String) :
    (gfmSplit false (rowCells cells)).1 :: (gfmSplit false (rowCells cells)).2 =
      cells.map (fun c => ' ' :: c.toList ++ [' ']) ++ [[]] := by
  induction cells with
  | nil => rfl
  | cons c cs ih =>
    simp only [rowCells, List.cons_append]
    have hsp : gfmSplit false (' ' :: (escapePipes c.toList ++ ' ' :: '|' :: rowCells cs)) =
        (' ' :: (gfmSplit false (escapePipes c.toList ++ ' ' :: '|' :: rowCells cs)).1,
          (gfmSplit false (escapePipes c.toList ++ ' ' :: '|' :: rowCells cs)).2) := by
      simp [gfmSplit]
    rw [hsp, gfmSplit_escapePipes _ _ (by simp)]
    simp [gfmSplit, ih]

private theorem gfmTrim_pad (cs : List Char) : gfmTrim (' ' :: (cs ++ [' '])) = gfmTrim cs := by
  unfold gfmTrim
  have hs : gfmSpace ' ' = true := rfl
  rw [List.dropWhile_cons_of_pos hs, List.dropWhile_append]
  split
  · next hd =>
    rw [List.isEmpty_iff] at hd
    simp [hd, hs]
  · simp [hs]

public theorem rowLine_cells_exact (cells : List String) :
    gfmRow (rowLine cells) = cells.map fun c => String.ofList (gfmTrim c.toList) := by
  have hsplit : gfmSplit false (rowLine cells).toList =
      ([], (gfmSplit false (rowCells cells)).1 :: (gfmSplit false (rowCells cells)).2) := by
    simp [rowLine, gfmSplit]
  simp only [gfmRow, hsplit, List.drop_succ_cons, List.drop_zero, gfmSplit_rowCells,
    List.dropLast_concat, List.map_map]
  apply List.map_congr_left
  intro c _
  simp only [Function.comp_apply, List.cons_append, gfmTrim_pad]

private theorem escapePipes_mem (l : List Char) :
    ∀ x ∈ escapePipes l, x = '\\' ∨ x ∈ l := by
  induction l with
  | nil => simp [escapePipes]
  | cons y l' ih =>
    intro x hx
    by_cases hy : y = '|'
    · subst hy
      simp only [escapePipes, beq_self_eq_true, ↓reduceIte, List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact Or.inl rfl
      · exact Or.inr List.mem_cons_self
      · rcases ih x hx with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
    · have hy' : (y == '|') = false := by simpa using hy
      simp only [escapePipes, hy', Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inr List.mem_cons_self
      · rcases ih x hx with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

public theorem rowLine_mem (cells : List String) :
    ∀ x ∈ (rowLine cells).toList,
      x = '|' ∨ x = '\\' ∨ x = ' ' ∨ ∃ c ∈ cells, x ∈ c.toList := by
  have hrow : ∀ (cs : List String), ∀ x ∈ rowCells cs,
      x = '|' ∨ x = '\\' ∨ x = ' ' ∨ ∃ c ∈ cs, x ∈ c.toList := by
    intro cs
    induction cs with
    | nil => simp [rowCells]
    | cons c cs ih =>
      intro x hx
      simp only [rowCells, List.cons_append, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | rfl | rfl | hx
      · exact Or.inr (Or.inr (Or.inl rfl))
      · rcases escapePipes_mem _ x hx with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr ⟨c, List.mem_cons_self, h⟩))
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inl rfl
      · rcases ih x hx with h | h | h | ⟨c', hc', h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr ⟨c', List.mem_cons_of_mem _ hc', h⟩))
  intro x hx
  simp only [rowLine, String.toList_ofList, List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact Or.inl rfl
  · exact hrow cells x hx

public theorem rowLine_contract (cells : List String)
    (h : ∀ c ∈ cells, ∀ x ∈ c.toList, x ≠ '\n' ∧ x ≠ '\r') :
    ∀ x ∈ (rowLine cells).toList, x ≠ '\n' ∧ x ≠ '\r' := by
  intro x hx
  rcases rowLine_mem cells x hx with rfl | rfl | rfl | ⟨c, hc, hxc⟩
  · decide
  · decide
  · decide
  · exact h c hc x hxc

private def longestRun (c : Char) (s : String) : Nat :=
  (s.foldl (fun (best, cur) x => if x == c then (max best (cur + 1), cur + 1) else (best, 0))
    (0, 0)).1

/-- The byte `acc` holds at `i`, if any. -/
private def byteAt (acc : String) (i : Nat) : Option UInt8 :=
  if h : i < acc.utf8ByteSize then some (acc.getUTF8Byte ⟨i⟩ (by simpa [String.Pos.Raw.lt_iff] using h))
  else none

/-- `acc` with the bang it ends on escaped, which before a link's bracket would open an image. -/
private def bangApart (acc : String) : String := Id.run do
  let n := acc.utf8ByteSize
  unless n > 0 && byteAt acc (n - 1) == some 33 do return acc
  let mut slashes := 0
  for k in [0:n - 1] do
    if byteAt acc (n - 2 - k) == some 92 then slashes := slashes + 1 else break
  if slashes % 2 == 1 then return acc
  return (String.Pos.Raw.set acc ⟨n - 1⟩ '\\').push '!'

/-- A code span holding `s` exactly (CommonMark §6.1). -/
private def codeSpan (s : String) : String :=
  if s.isEmpty then "" else
  let ticks := String.ofList (List.replicate (longestRun '`' s + 1) '`')
  let pad := s.startsWith "`" || s.endsWith "`" ||
    (s.startsWith " " && s.endsWith " " && s.any (· != ' '))
  ticks ++ (if pad then " " ++ s ++ " " else s) ++ ticks

/-- A fence for `body`: three backticks, or one more than
the longest run inside. -/
private def fenceFor (body : String) : String :=
  String.ofList (List.replicate (max 3 (longestRun '`' body + 1)) '`')

/-- Whether a URL is an absolute URI an autolink can carry (§6.4). -/
private def autolinkable (url : String) : Bool :=
  match url.splitOn ":" with
  | scheme :: _ :: _ =>
    scheme.length ≥ 2 && scheme.length ≤ 32 &&
      (scheme.toList.head?.map Char.isAlpha).getD false &&
      scheme.all (fun c => c.isAlphanum || c == '+' || c == '.' || c == '-') &&
      url.all (fun c => c != ' ' && c != '<' && c != '>' && c.toNat ≥ 32)
  | _ => false

/-- Whether a link's body is its destination as plain text,
as an autolink writes it. -/
private def bareLink (url : String) (body : Array Inline) : Bool :=
  Ir.plainText body == url &&
    body.all fun x => x matches .text _ || x matches .colored _ _ #[.text _]

/-- A link destination as `[text](…)` reads it back (§6.3). -/
private def linkDest (url : String) : String :=
  let esc (bad : Char → Bool) : String :=
    url.foldl (init := "") fun acc c => if bad c then (acc.push '\\').push c else acc.push c
  if url.any (fun c => c == ' ' || c == '<' || c == '>') then
    "<" ++ esc (fun c => c == '<' || c == '>' || c == '\\') ++ ">"
  else esc (fun c => c == '(' || c == ')' || c == '\\')

/-- White space beside which a delimiter neither opens nor closes, as the
markdown door reads it. -/
private def mdWhite (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0C'

/-- Whether a delimiter run beside `c` flanks as beside whitespace or punctuation, Unicode's as the
reader reads them (§6.2). -/
private def flankEdge (c : Char) : Bool := mdWhite c || Nfc.isSpaceSeparator c || Nfc.isPunctuation c

/-- A run's opening white space, and the rest. -/
private def leadWhite : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
    if mdWhite c || (c == '\\' && rest.head? == some '\n') then
      let r := leadWhite rest
      (c :: r.1, r.2)
    else ([], c :: rest)

/-- A reversed run's closing white space, and the rest. -/
private def trailWhite (afterBreak : Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
    if mdWhite c || (afterBreak && c == '\\') then
      let r := trailWhite (c == '\n') rest
      (c :: r.1, r.2)
    else ([], c :: rest)

/-- Whether what follows a run lets its closing delimiter
close after a `<br>` (§6.2). -/
private def closesAfterTag (after : Bool) : List Inline → Bool
  | [] => after
  | .text s :: _ => match s.toList with
    | c :: _ => flankEdge c
    | [] => false
  | .linebreak _ :: _ => true
  | .italicCorr _ :: rest => closesAfterTag after rest
  | .label _ :: _ | .link .. :: _ => true
  | _ => false

/-- A run's closing hard breaks kept inside its delimiters as `<br>` where the
delimiter still closes after one. -/
private def closingBreaks (trail : String) (closes : Bool) : Option String :=
  if !trail.isEmpty && (trail.replace "\\\n" "").isEmpty && closes then
    some (trail.replace "\\\n" "<br>")
  else none

/-- A heading's or a cell's run text split before the `<br>`s it ends on. -/
private def trailingTags (s : String) : String × String := Id.run do
  let mut core := s
  let mut tags := ""
  for _ in [0:s.length + 1] do
    unless core.endsWith "<br>" do break
    let before := (core.dropEnd 4).toString
    unless (before.toList.reverse.takeWhile (· == '\\')).length % 2 == 0 do break
    core := before
    tags := "<br>" ++ tags
  return (core, tags)

/-- A heading's or a cell's run text split after the `<br>`s it opens with. -/
private def leadingTags (s : String) : String × String := Id.run do
  let mut core := s
  let mut tags := ""
  for _ in [0:s.length + 1] do
    unless core.startsWith "<br>" do break
    core := (core.drop 4).toString
    tags := tags ++ "<br>"
  return (tags, core)

/-- A run's text split at its own leading and trailing white space, which stands
outside the delimiters. -/
private def spaceSplit (s : String) : String × String × String :=
  let (lead, rest) := leadWhite s.toList
  let (trail, core) := trailWhite false rest.reverse
  (String.ofList lead, String.ofList core.reverse, String.ofList trail.reverse)

/-- Code-set content: one code span per run between links, each link a link
whose text is a code span. -/
private def monoInto (acc : String) (run : Array Inline) : List Inline → String
  | [] =>
    let span := codeSpan (Ir.plainText run)
    acc ++ span
  | .link url body :: rest =>
    let span := codeSpan (Ir.plainText run)
    let text := codeSpan (Ir.plainText body)
    let dest := linkDest url
    monoInto (bangApart (acc ++ span) ++ "[" ++ text ++ "](" ++ dest ++ ")") #[] rest
  | .footnote num _ :: rest =>
    let span := codeSpan (Ir.plainText run)
    monoInto (acc ++ span ++ s!"[^{num.getD 0}]") #[] rest
  | .label key :: rest =>
    let span := codeSpan (Ir.plainText run)
    monoInto (acc ++ span ++ "<a name=\"" ++ Ir.labelAnchor key ++ "\"></a>") #[] rest
  | x :: rest => monoInto acc (run.push x) rest

/-- The delimiter a style takes in markdown, where it has one. -/
private def styleMark : Style → Option String
  | .bold => some "**"
  | .italic => some "*"
  | .emph => some "*"
  | _ => none

/-- Where inline content is written: a paragraph's flow, a
heading's line, or a pipe table's cell. -/
private inductive Site where
  | flow
  | line
  | cell
  deriving BEq

/-- A citation note as the reader reads it back inside a citation's brackets. -/
private def citeNote (pipes : Bool) (s : String) : String :=
  keepAbbrevSpaces "" (String.join (s.trimAscii.toString.toList.map fun c =>
    if c == ';' || c == '@' then "\\" ++ c.toString else String.ofList (escapeChars pipes true [c])))

/-- One work of a bracketed citation, `prefix -@key, suffix`; `none` where its key has no
spelling. -/
private def bracketWork (pipes : Bool) (pre post : String) (suppress : Bool) (key : String) :
    Option String := do
  let k ← CiteKey.spelling? key none
  let preNote := citeNote pipes pre
  let postNote := citeNote pipes post
  let pre := if preNote.isEmpty then "" else preNote ++ " "
  let post := if postNote.isEmpty then "" else ", " ++ postNote
  return pre ++ (if suppress then "-" else "") ++ k ++ post

/-- Whether an author-in-text citation may open after what the twin wrote: not inside a word, after
its `.`, an emphasis delimiter, a backslash that would escape it, or a hyphen after no word, which
would suppress its author; an escaped delimiter or backslash is text. -/
private def inTextAfter (acc : String) : Bool :=
  let slashes (s : String.Slice) : Nat := (s.takeEndWhile (· == '\\')).toString.length
  match acc.back? with
  | none => true
  | some c =>
    if c == '\\' then slashes (acc.dropEnd 0) % 2 == 0
    else if c == '*' || c == '_' then slashes (acc.dropEnd 1) % 2 == 1
    else if c == '-' then ((acc.dropEnd 1).back?).any CiteKey.isAlnum
    else !(CiteKey.isAlnum c || c == '.')

/-- What both readers skip between two spellings that would otherwise read as one. -/
private def apart : String := "<!-- -->"

/-- What stands apart before and after a run whose content opens or closes on punctuation, where
`before` ends on neither whitespace nor punctuation or `blocked` says what follows lets no closer
close: an empty comment, punctuation the run then flanks (§6.2). -/
private def runApart (before core : String) (blocked : Bool) : String × String :=
  (if Nfc.isPunctuation core.front && !before.isEmpty && !flankEdge before.back then apart else "",
   if Nfc.isPunctuation core.back && blocked then apart else "")

/-- What a twin declaring its bibliography writes before a citation it cannot spell, which then
writes its citations as their marks instead. -/
private def unspelled : String := "\uE000"

/-- Whether the text after a citation would read as part of it: a bracket, a parenthesis or a brace
opening on it. -/
private def opensOn (after : String) : Bool :=
  after.startsWith "(" || after.startsWith "[" || after.startsWith "{"

/-- A citation node's form and keys, resolved or not. -/
private def citeOf? : Inline → Option (CiteForm × Array String)
  | .cite f ks => some (f, ks)
  | .cited f ks _ => some (f, ks)
  | _ => none

/-- Whether a citation's spelling opens on a bracket an author-in-text citation before it would read
as its own. -/
private def bracketCite (x : Inline) : Bool :=
  (citeOf? x).any fun (f, _) => f.cmd == .paren || f.cmd == .yearPar || f.cmd == .bracket true

/-- How an author-in-text citation without notes stands before `rest`: bare, before the space that
would join a bracket citation after it written as a reference, or apart from one right after it. -/
private def inTextTail (rest : List Inline) : String × Nat :=
  match rest with
  | .text " " :: y :: _ => if bracketCite y then ("&#32;", 1) else ("", 0)
  | y :: _ => if bracketCite y then (apart, 0) else ("", 0)
  | [] => ("", 0)

/-- A citation group's Pandoc spelling, `[see @a, p. 3; @b]`, `@a [p. 3]` or `[-@a]`, where the
form has one that reads back to it, and the siblings after it the spelling takes, set apart from
what it would read as one with; `none` where the form has none. -/
private def citeSpelling (pipes : Bool) (f : CiteForm) (keys : Array String) (acc after : String)
    (rest : List Inline) : Option (String × Nat) :=
  if f.full || f.up then none else
  let close := if opensOn after || rest.head?.any bracketCite then apart else ""
  let open_ := if inTextAfter acc then "" else apart
  match f.cmd, keys.toList with
  | .paren, _ :: _ =>
    let n := keys.size
    let works := keys.toList.zipIdx.mapM fun (k, i) =>
      bracketWork pipes (if i == 0 then f.pre else "") (if i + 1 == n then f.post else "") false k
    works.map fun ws => ("[" ++ "; ".intercalate ws ++ "]" ++ close, 0)
  | .yearPar, [k] => (bracketWork pipes f.pre f.post true k).map fun w => ("[" ++ w ++ "]" ++ close, 0)
  | .textual, [k] =>
    if !f.pre.isEmpty then none
    else if f.post.isEmpty then do
      let (tail, n) := inTextTail rest
      -- A reference's `&#` or a comment's `<` lengthens no key.
      let spelled ← CiteKey.spelling? k (if tail.isEmpty then after.front? else none)
      return (open_ ++ spelled ++ tail, n)
    else (CiteKey.spelling? k none).map fun s =>
      (open_ ++ s ++ " [" ++ citeNote pipes f.post ++ "]" ++ close, 0)
  | _, _ => none

/-- The works of a `\citetext` group after its opening mark, each its own command's single key
separated by `; `, to the closing mark: their spellings and the nodes read, the closing mark's
included. -/
private def groupWorks (pipes : Bool) (out : Array String) (n : Nat) :
    List Inline → Option (Array String × Nat)
  | [] => none
  | x :: rest =>
    match citeOf? x with
    | some (f, ks) =>
      if f.cmd == .bracket false then if out.isEmpty then none else some (out, n + 1)
      else if f.full || f.up then none
      else match f.cmd, ks.toList with
        | .alp, [k] | .year, [k] =>
          match bracketWork pipes f.pre f.post (f.cmd == .year) k, rest with
          | some w, .text "; " :: more => groupWorks pipes (out.push w) (n + 2) more
          | some w, more => groupWorks pipes (out.push w) (n + 1) more
          | _, _ => none
        | _, _ => none
    | _ => none

/-- The spelling a citation run takes at the head of `x :: rest`, and the siblings after `x` it
reads: one citation, a `\citetext` group, or an author before a group; `none` where it has none. -/
private def citeRun (pipes : Bool) (acc : String) (x : Inline) (rest : List Inline) :
    Option (String × Nat) :=
  let afterOf (l : List Inline) : String := (l.head?.map Ir.plainTextOne).getD ""
  match citeOf? x with
  | some (f, ks) =>
    if f.cmd == .bracket true then
      match groupWorks pipes #[] 0 rest with
      | some (ws, n) =>
        let close := if opensOn (afterOf (rest.drop n)) || (rest.drop n).head?.any bracketCite
          then apart else ""
        some ("[" ++ "; ".intercalate ws.toList ++ "]" ++ close, n)
      | _ => none
    else if f.cmd == .author && !f.full && !f.up && f.pre.isEmpty && f.post.isEmpty then
      match ks.toList, rest with
      | [k], .text " " :: g :: more =>
        match citeOf? g with
        | some (gf, _) =>
          if gf.cmd != .bracket true then none
          else match more with
            | y :: _ =>
              match citeOf? y, groupWorks pipes #[] 0 more with
              | some (yf, yks), some (ws, n) =>
                if yf.cmd != .year || yks != #[k] || !yf.pre.isEmpty then none
                else
                  let open_ := if inTextAfter acc then "" else apart
                  let close := if opensOn (afterOf (more.drop n)) ||
                    (more.drop n).head?.any bracketCite then apart else ""
                  let tail := if yf.post.isEmpty then ws.toList.drop 1
                    else (citeNote pipes yf.post) :: ws.toList.drop 1
                  (CiteKey.spelling? k none).map fun s =>
                    (open_ ++ s ++ " [" ++ "; ".intercalate tail ++ "]" ++ close, n + 2)
              | _, _ => none
            | [] => none
        | _ => none
      | _, _ => none
    else citeSpelling pipes f ks acc (afterOf rest) rest
  | _ => none

/-- Whether content opens on an inline formula, under any source location. -/
private def opensInlineMath : List Inline → Bool
  | .math false _ :: _ => true
  | .formula false _ _ :: _ => true
  | .located _ body :: _ => match body.toList with
    | .math false _ :: _ => true
    | .formula false _ _ :: _ => true
    | _ => false
  | _ => false

/-- An alternative's runs as the twin spells them: its words escaped and its citations as the
body's citation runs spell them, one with none marked unspelled before its text. -/
private def altSpelling (pipes : Bool) (runs : Array Ir.AltRun) : String :=
  altSpellFrom pipes "" (runs.toList.map fun r => match r with
    | .text t => .text t
    | .cite f keys _ => .cite f keys) runs.toList
where
  /-- The spelling onto `acc` of the runs `rs`, `xs` their nodes. -/
  altSpellFrom (pipes : Bool) (acc : String) : List Inline → List Ir.AltRun → String
    | [], _ | _ :: _, [] => acc
    | x :: rest, r :: rrest =>
      match citeRun pipes acc x rest with
      | some (spelled, n) => altSpellFrom pipes (acc ++ spelled) (rest.drop n) (rrest.drop n)
      | none =>
        let said := match r with
          | .text t => keepAbbrevSpaces acc (escapeText pipes true t)
          | .cite _ keys ink => unspelled ++ ink.getD (Ir.citeMarks keys)
        altSpellFrom pipes (acc ++ said) rest rrest
  termination_by xs => xs.length
  decreasing_by all_goals simp_wf; all_goals (try simp [List.length_drop]); all_goals omega

mutual

/-- Inline content onto `acc`: meaning survives, decoration degrades. -/
private def inlineInto (site : Site) (cites : Bool) (acc : String) (after : Bool := true) :
    Inline → String
  | .text s =>
    let escaped := keepAbbrevSpaces acc (escapeText (site != .cell) cites s)
    acc ++ escaped
  | .math display src =>
    if display then acc ++ s!"$${src}$$" else acc ++ s!"${src}$"
  -- Markdown's spelling of a formula is the TeX source it carries.
  | .formula display src _ =>
    if display then acc ++ s!"$${src}$$" else acc ++ s!"${src}$"
  | .image src _ alt =>
    let shown := match alt, cites with
      | .citing runs, true => altSpelling (site != .cell) runs
      | _, _ => keepAbbrevSpaces "" (escapeText (site != .cell) cites alt.text)
    let dest := linkDest src
    acc ++ "![" ++ shown ++ "](" ++ dest ++ ")"
  -- An icon's markdown spelling is its text alternative.
  | .icon _ label =>
    let escaped := keepAbbrevSpaces acc (escapeText (site != .cell) cites label)
    acc ++ escaped
  -- An anchor is written as the empty target the markdown reader reads back.
  | .label key => acc ++ "<a name=\"" ++ Ir.labelAnchor key ++ "\"></a>"
  -- A continuous medium has no page for a folio to name.
  | .ref _ form text _ =>
    if form.paged then acc else
    let escaped := escapeText (site != .cell) cites text
    acc ++ escaped
  | .styled st body =>
    match st with
    | .mono => monoInto acc #[] body.toList
    | _ =>
      let inner := inlinesInto site cites "" none after 0 body.toList
      match styleMark st with
      | some m =>
        let (lead, core, trail) := spaceSplit inner
        let (pre, post) := runApart (acc ++ lead) core (trail.isEmpty && !after)
        if core.isEmpty then acc ++ lead ++ trail
        else acc ++ lead ++ pre ++ m ++ core ++ m ++ post ++ trail
      | none => acc ++ inner
  | .colored _ _ body => inlinesInto site cites acc none after 0 body.toList
  | .located _ body => inlinesInto site cites acc none after 0 body.toList
  | .role _ body => inlinesInto site cites acc none after 0 body.toList
  | .link url body =>
    if bareLink url body && autolinkable url then acc ++ "<" ++ url ++ ">"
    else
      let inner := inlinesInto site cites "" none true 0 body.toList
      let dest := linkDest url
      bangApart acc ++ "[" ++ inner ++ "](" ++ dest ++ ")"
  | .decorated _ body | .boxed _ body => inlinesInto site cites acc none after 0 body.toList
  | .onSteps _ body => inlinesInto site cites acc none after 0 body.toList
  | .altSteps _ active otherwise =>
    inlinesInto site cites (inlinesInto site cites acc none false 0 active.toList) none after 0
      otherwise.toList
  -- `\hfill` renders as a spaced em dash: text has no margin.
  | .fill =>
    let acc := if acc.endsWith " " then (acc.dropEnd 1).toString else acc
    acc ++ " — "
  -- Horizontal glue with room separates prose; a painted rule has no textual reading.
  | .hspace e _ =>
    let zero := Dim.MeasureValues.horizontal 0 0
    let g := e.eval (Dim.MeasureValues.find zero)
    if g.fil then
      let acc := if acc.endsWith " " then (acc.dropEnd 1).toString else acc
      acc ++ " — "
    else if e.anyRef (fun _ => true) || g.width.sp > 0 || g.width.em > 0 || g.width.ex > 0 then
      if acc.endsWith " " then acc else acc ++ " "
    else acc
  | .rule _ _ _ => acc
  | .pageNumber => acc
  | .pageCount => acc
  | .strut _ => acc
  | .italicCorr _ => acc
  -- An unresolved citation is worth its marks.
  | .cite _ keys =>
    let marks := Ir.citeMarks keys
    (if cites then acc ++ unspelled else acc) ++ marks
  | .cited _ _ ink => inlinesInto site cites (if cites then acc ++ unspelled else acc) none after 0
    ink.toList
  -- The mark in footnote syntax; the body is a `[^k]: ...` definition after the document.
  | .footnote num _ => acc ++ s!"[^{num.getD 0}]"
  | .linebreak _ =>
    if site == .flow then acc ++ "\\\n" else acc ++ "<br>"

/-- The sibling walk: a run following a run of its own delimiter reopens it, and zero glue between
two formulas is a space, so the second never reads as a display's `$$`. -/
private def inlinesInto (site : Site) (cites : Bool) (acc : String) (prev : Option String)
    (after : Bool) (skip : Nat) : List Inline → String
  | [] => acc
  | x :: rest =>
    -- The siblings a citation's spelling already read write nothing of their own.
    if skip > 0 then inlinesInto site cites acc prev after (skip - 1) rest else
    match (if cites then citeRun (site != .cell) acc x rest else none) with
    | some (spelled, n) => inlinesInto site cites (acc ++ spelled) none after n rest
    | none =>
    match x with
    | .hspace e keep =>
      let zero := Dim.MeasureValues.horizontal 0 0
      let g := e.eval (Dim.MeasureValues.find zero)
      let bare := !g.fil && !e.anyRef (fun _ => true) && g.width.sp == 0 && g.width.em == 0 &&
        g.width.ex == 0
      if bare && acc.endsWith "$" && opensInlineMath rest then
        inlinesInto site cites (acc ++ " ") prev after 0 rest
      else
        let next := inlineInto site cites acc (closesAfterTag after rest) (.hspace e keep)
        inlinesInto site cites next (if next.utf8ByteSize == acc.utf8ByteSize then prev else none) after 0
          rest
    | .styled st body =>
      match styleMark st with
      | some m =>
        let closes := closesAfterTag after rest
        let (lead, core, trail) := spaceSplit (inlinesInto site cites "" none closes 0 body.toList)
        -- A paragraph's run keeps closing breaks inside as `<br>` where its closer still closes.
        let (lead, core, trail) := if site == .flow then
            match closingBreaks trail closes with
            | some brs => (lead, core ++ brs, "")
            | none => (lead, core, trail)
          else
            let (opening, core) := leadingTags core
            let (core, closing) := if closes then (core, "") else trailingTags core
            (lead ++ opening, core, closing ++ trail)
        let (pre, post) := runApart (acc ++ lead) core (trail.isEmpty && !closes)
        let ends := if trail.isEmpty && post.isEmpty then some m else none
        if core.isEmpty then
          inlinesInto site cites (acc ++ lead ++ trail) (if (lead ++ trail).isEmpty then prev else none)
            after 0 rest
        else if prev == some m then
          inlinesInto site cites ((acc.dropEnd m.length).toString ++ lead ++ core ++ m ++ post ++ trail)
            ends after 0 rest
        else inlinesInto site cites (acc ++ lead ++ pre ++ m ++ core ++ m ++ post ++ trail) ends after 0
          rest
      | none =>
        inlinesInto site cites (inlineInto site cites acc (closesAfterTag after rest) (.styled st body)) none
          after 0 rest
    | x =>
      -- An inline that writes nothing leaves the run it follows open to the next.
      let next := inlineInto site cites acc (closesAfterTag after rest) x
      inlinesInto site cites next (if next.utf8ByteSize == acc.utf8ByteSize then prev else none) after 0
        rest

end

/-- A trailing `#` escaped, so a heading's text never reads
as its closing sequence (§4.2). -/
private def closeHash (s : String) : String :=
  match s.toList.reverse.dropWhile (fun c => c == ' ' || c == '\t') with
  | '#' :: rest => String.ofList (rest.reverse ++ ['\\', '#'])
  | _ => s

/-- The markdown spelling of inline content in a paragraph's flow; `cites` where the twin declares
the document's bibliography and spells its citations. -/
public def inlineText (xs : Array Inline) (cites : Bool := false) : String :=
  closeHash (inlinesInto .flow cites "" none true 0 xs.toList)

/-- Line endings as spaces. -/
private def oneLine (s : String) : String :=
  String.ofList (s.toList.map fun c => if c == '\n' || c == '\r' then ' ' else c)

/-- A heading's text: one line, its trailing `#` escaped. -/
public def headingText (xs : Array Inline) (cites : Bool := false) : String :=
  closeHash (oneLine (inlinesInto .line cites "" none true 0 xs.toList))

/-- A pipe table cell's text: one line, its pipes bare. -/
public def cellText (xs : Array Inline) (cites : Bool := false) : String :=
  oneLine (inlinesInto .cell cites "" none true 0 xs.toList)

/-- A laid-out paragraph's indent in the twin for a line `depth` steps in: `Ir.linesStep` in em and
en spaces for each step. -/
private def linesIndent (depth : Nat) : String :=
  let em := Ir.linesStep.em.toNat
  let step := String.join (List.replicate (em / 1000) "\u2003" ++
    List.replicate (em % 1000 / 500) "\u2002")
  String.join (List.replicate depth step)

/-- A laid-out paragraph's lines after `acc` as one paragraph's text, each line after the first
opening a hard break and its indent. -/
private def linesText (cites : Bool) (acc : String) : List Ir.LaidLine → String
  | [] => acc
  | l :: rest =>
    linesText cites
      (acc ++ (if acc.isEmpty then "" else "\\\n") ++ linesIndent l.depth ++ inlineText l.content cites)
      rest

private theorem oneLine_mem (s : String) : ∀ x ∈ (oneLine s).toList, x ≠ '\n' ∧ x ≠ '\r' := by
  intro x hx
  simp only [oneLine, String.toList_ofList, List.mem_map] at hx
  obtain ⟨c, _, rfl⟩ := hx
  by_cases h : (c == '\n' || c == '\r') = true
  · simp only [h, ↓reduceIte]
    decide
  · simp only [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    exact h

private theorem closeHash_mem (s : String) (x : Char) (hx : x ∈ (closeHash s).toList) :
    x ∈ s.toList ∨ x = '\\' ∨ x = '#' := by
  unfold closeHash at hx
  split at hx
  · next rest heq =>
    simp only [String.toList_ofList, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with hx | hx
    · left
      have : x ∈ s.toList.reverse.dropWhile (fun c => c == ' ' || c == '\t') := by
        rw [heq]
        exact List.mem_cons_of_mem _ (List.mem_reverse.mp hx)
      exact List.mem_reverse.mp ((List.dropWhile_sublist _).subset this)
    · right
      exact hx
  · exact Or.inl hx

public theorem headingText_contract (xs : Array Inline) (cites : Bool := false) :
    ∀ x ∈ (headingText xs cites).toList, x ≠ '\n' ∧ x ≠ '\r' := by
  intro x hx
  rcases closeHash_mem _ x hx with hx | rfl | rfl
  · exact oneLine_mem _ x hx
  · decide
  · decide

public theorem cellText_contract (xs : Array Inline) (cites : Bool := false) :
    ∀ x ∈ (cellText xs cites).toList, x ≠ '\n' ∧ x ≠ '\r' :=
  oneLine_mem _

/-- The llms.txt title line's text: the metadata title
written as a heading's text. -/
public def titleLine (t : String) (cites : Bool := false) : String :=
  closeHash (escapeText true cites t)

/-- The llms.txt summary line's text inside its quotation. -/
public def summaryLine (s : String) (cites : Bool := false) : String :=
  escapeLineStart (escapeText true cites s)

private theorem escapeLineStart_mem (s : String) (x : Char)
    (hx : x ∈ (escapeLineStart s).toList) : x ∈ s.toList ∨ x = '\\' := by
  unfold escapeLineStart at hx
  generalize hcs : s.toList.dropWhile (fun c => c == ' ' || c == '\t') = cs at hx
  have hsub : ∀ y ∈ cs, y ∈ s.toList := fun y hy =>
    (hcs ▸ List.dropWhile_sublist _).subset hy
  simp only at hx
  split at hx
  · exact Or.inl (hsub x (by simpa using hx))
  · split at hx
    · simp at hx
    · next c rest _ =>
      split at hx
      · simp only [String.toList_ofList, List.mem_append, List.mem_cons] at hx
        rcases hx with hx | rfl | hx
        · exact Or.inl (hsub x ((List.takeWhile_sublist _).subset hx))
        · exact Or.inr rfl
        · exact Or.inl (hsub x ((List.drop_sublist _ _).subset hx))
      · rw [String.toList_ofList, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Or.inr rfl
        · exact Or.inl (hsub x hx)

public theorem titleLine_contract (t : String) (cites : Bool := false) :
    ∀ x ∈ (titleLine t cites).toList, x ≠ '\n' ∧ x ≠ '\r' := by
  intro x hx
  rcases closeHash_mem _ x hx with hx | rfl | rfl
  · exact escapeChars_line true cites t.toList x (by simpa [escapeText] using hx)
  · decide
  · decide

public theorem summaryLine_contract (s : String) (cites : Bool := false) :
    ∀ x ∈ (summaryLine s cites).toList, x ≠ '\n' ∧ x ≠ '\r' := by
  intro x hx
  rcases escapeLineStart_mem _ x hx with hx | rfl
  · exact escapeChars_line true cites s.toList x (by simpa [escapeText] using hx)
  · decide

/-- A paragraph's lines under their container, each escaped at its start and set
under the container's prefix. -/
private def paraText (first ind text : String) : String :=
  let text := String.ofList (text.toList.reverse.dropWhile (· == ' ')).reverse
  match text.splitOn "\n" with
  | [] => first
  | l :: ls =>
    ls.foldl (fun acc x => acc ++ "\n" ++ ind ++ escapeLineStart x) (first ++ escapeLineStart l)

/-- A disclosure's summary as its line in the twin: one line, `&` and `<`
written as references. -/
private def summaryHtml (head : Array Inline) : String :=
  (plainText head).foldl (fun acc c => match c with
    | '&' => acc ++ "&amp;"
    | '<' => acc ++ "&lt;"
    | '\n' | '\r' => acc.push ' '
    | c => acc.push c) ""

/-- Two blank lines in a row: what the tightening folds into one. -/
private def blankRun : List String → Bool
  | a :: b :: rest => (a.isEmpty && b.isEmpty) || blankRun (b :: rest)
  | _ => false

/-- A fence's line prefix: its container's, or at the top level one space when
the content holds two blank lines in a row. -/
private def fenceIndent (ind : String) (lines : List String) : String :=
  if ind.isEmpty && blankRun lines then " " else ind

/-- A fenced block under its container. -/
private def fencedText (ind fence info : String) (lines : List String) : String :=
  lines.foldl (fun acc l => acc ++ ind ++ l ++ "\n") (ind ++ fence ++ info ++ "\n") ++
    ind ++ fence ++ "\n\n"

/-- The reference list's markdown spelling: one paragraph per entry, the anchor its citations link
to and the style's marker leading it. -/
private def bibItemsText (cites : Bool) (ind : String) (items : Array Ir.BibItem) : String :=
    Id.run do
  let mut out := ""
  for item in items do
    let anchor := Ir.bibAnchor item.key
    let target := if Ir.labelAnchor anchor == anchor then "<a name=\"" ++ anchor ++ "\"></a>" else ""
    let mark := match item.marker with
      | some m => escapeText true cites s!"[{m}]" ++ " "
      | none => ""
    out := out ++ paraText ind ind (target ++ mark ++ inlineText item.content cites) ++ "\n\n"
  return out

/-- A reference list's entries as a comment its division holds, each marker and text on a line, read
where the twin's text is read and skipped where it is built again. -/
private def refsComment (ind : String) (items : Array Ir.BibItem) : String :=
  if items.isEmpty then "" else
  let line (it : Ir.BibItem) : String :=
    let mark := (it.marker.map fun m => "[" ++ m ++ "] ").getD ""
    let text := String.ofList ((mark ++ plainText it.content).toList.map fun c =>
      if c == '\n' || c == '\r' then ' ' else c)
    ind ++ text.replace "-->" "-- >" ++ "\n"
  ind ++ "<!--\n" ++ String.join (items.toList.map line) ++ ind ++ "-->\n"

/-- The heading marker a section level takes, as many `#` as the shared rank. -/
@[expose] public def headingMarker (level : Ir.HeadingLevel) : String :=
  String.ofList (List.replicate (Ir.headingRank level) '#')

/-- A block's text with its trailing blank lines off. -/
private def trimBlank (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (· == '\n')).reverse

/-- An item's first block, on the marker's line under the content column. -/
private def itemHead (first cont s : String) : String :=
  let s := trimBlank s
  if s.startsWith cont then first ++ (s.drop cont.length).toString
  else if s.isEmpty then first else first ++ "\n" ++ s

/-- Whether a list takes the other marker, following a list
of its kind that took the usual one. -/
private def listAlt (prev : Option (Bool × Bool)) (ordered : Bool) : Bool :=
  match prev with
  | some (o, a) => o == ordered && !a
  | none => false

mutual

/-- Whether the block's markdown opens with a list. -/
private def leadsWithList : Block → Bool
  | .list _ _ _ => true
  | .role _ body => leadsWithListList body.toList
  | .spaced _ body => leadsWithListList body.toList
  | .only _ body => leadsWithListList body.toList
  | .onSteps _ body => leadsWithListList body.toList
  | .altSteps _ active otherwise =>
    if active.isEmpty then leadsWithListList otherwise.toList else leadsWithListList active.toList
  | .center body => leadsWithListList body.toList
  | .ragged _ body => leadsWithListList body.toList
  | .link _ body => leadsWithListList body.toList
  | .titled _ title body => title.isEmpty && leadsWithListList body.toList
  | .disclosure _ _ _ => false
  | .frame title _ _ _ body => title.isEmpty && leadsWithListList body.toList
  | .float _ _ capAbove body caption =>
    (caption.isEmpty || !capAbove) && leadsWithListList body.toList
  | .columns cols => leadsWithListColumns cols.toList
  | .para _ => false
  | .lines _ => false
  | .equation _ _ => false
  | .section _ _ _ _ => false
  | .quote _ _ => false
  | .abstract _ => false
  | .verbatim _ _ _ => false
  | .algorithm _ _ _ => false
  | .table _ _ _ _ _ _ => false
  | .bibliography _ _ _ => false
  -- `twinBody` has set every table of contents as its list.
  | .contents _ _ => false
  | .nav _ _ => false
  | .note _ => false
  | .framefoot _ => false
  | .setPalette _ => false
  | .setTokens _ => false
  | .pagebreak => false
  | .logo _ => false
  | .rule _ _ _ => false
  | .picture _ => false

private def leadsWithListList : List Block → Bool
  | [] => false
  | b :: _ => leadsWithList b

private def leadsWithListColumns : List (BoxWidth × Array Block) → Bool
  | [] => false
  | (_, body) :: _ => leadsWithListList body.toList

end

/-- Where an item's writing stands. -/
private structure ItemPen where
  acc : String
  first : Option String
  prev : Option (Bool × Bool)

/-- An item's block written: the first that writes anything
takes the marker's line. -/
private def itemPut (cont : String) (pen : ItemPen) (leadsList : Bool) (s : String) : ItemPen :=
  let s := trimBlank s
  if s.isEmpty then pen
  else match pen.first with
    | some first => { acc := pen.acc ++ itemHead first cont s ++ "\n", first := none, prev := none }
    | none => { pen with acc := pen.acc ++ (if leadsList then "" else "\n") ++ s ++ "\n", prev := none }

/-- What the twin writes blocks against: the document's locale, and whether the twin declares the
document's bibliography, so its citations are spelled and its list stands in a division. -/
private structure Twin where
  loc : Locale
  cites : Bool

mutual

/-- One block onto `acc`; `ind` is the line prefix every
line of the block carries. -/
private def blockInto (tw : Twin) (summary ind acc : String) : Block → String
  | .para xs => acc ++ paraText ind ind (inlineText xs tw.cites) ++ "\n\n"
  | .lines ls => acc ++ paraText ind ind (linesText tw.cites "" ls.toList) ++ "\n\n"
  -- the number rides beside the formula, as it does on the page
  | .equation num xs => acc ++ paraText ind ind (inlineText xs tw.cites ++ " " ++ inlineText num tw.cites) ++ "\n\n"
  | .section level _ num title =>
    -- The heading line carries its resolved number as the page does.
    let numTxt := match num with
      | some n => n ++ " "
      | none => ""
    let head := acc ++ ind ++ headingMarker level ++ " " ++ numTxt ++ headingText title tw.cites ++ "\n\n"
    if level == 0 then head ++ summary
    else head
  | .list ordered _ items =>
    let text := itemsInto tw summary ind ordered false 1 "" items.toList
    acc ++ text ++ "\n"
  | .center body => blocksInto tw summary ind acc none body.toList
  | .ragged _ body => blocksInto tw summary ind acc none body.toList
  -- Every quoted line takes the `> ` marker, a bare `>` between quoted blocks (§5.1).
  | .quote _ body =>
    let inner := blocksInto tw summary (ind ++ "> ") "" none body.toList
    let trimmed := String.ofList (inner.toList.reverse.dropWhile (· == '\n')).reverse
    -- An empty quotation is its bare marker.
    let joined := if trimmed.isEmpty then ind ++ ">"
      else String.intercalate ("\n" ++ ind ++ ">\n") (trimmed.splitOn "\n\n")
    acc ++ joined ++ "\n\n"
  | .spaced _ body => blocksInto tw summary ind acc none body.toList
  -- An abstract mirrors the HTML `<section>` with its heading.
  | .abstract body =>
    blocksInto tw summary ind (acc ++ (ind ++ "## " ++ tw.loc.abstract ++ "\n\n")) none body.toList
  | .titled _ title body =>
    let head := if title.isEmpty then "" else
      paraText ind ind (inlineText #[.styled .bold title] tw.cites) ++ "\n\n"
    blocksInto tw summary ind (acc ++ head) none body.toList
  -- The disclosure as the element its reader reads back.
  | .disclosure head expanded body =>
    let inner := blocksInto tw summary ind "" none body.toList
    let inner := if inner.endsWith "\n\n" then (inner.dropEnd 1).toString else inner
    acc ++ (ind ++ (if expanded then "<details open>" else "<details>") ++ "\n" ++
      ind ++ "<summary>" ++ summaryHtml head ++ "</summary>\n\n" ++ inner ++
      ind ++ "</details>\n\n")
  | .role _ body => blocksInto tw summary ind acc none body.toList
  -- CommonMark has no block-link construct; the body stays.
  | .link _ body => blocksInto tw summary ind acc none body.toList
  | .verbatim _ s spec =>
    -- The numbered caption leads the fence; the declared language is the fence's info string.
    let cap := match spec.caption with
      | some (n, c) =>
        paraText ind ind (inlineText (Ir.listingCaption tw.loc n c) tw.cites) ++ "\n\n"
      | none => ""
    let lines := (verbatimLines s).toList
    acc ++ cap ++ fencedText (fenceIndent ind lines) (fenceFor s) spec.fenceInfo lines
  -- Pseudocode as a fence, each line's keywords as plain text.
  | .algorithm _ semis lines =>
    let words := Ir.algWords tw.loc.tag
    let rendered := lines.toList.map fun l =>
      String.ofList (List.replicate (2 * l.depth) ' ') ++
        Ir.plainText (Ir.AlgLine.rendered words semis Ir.Color.black l)
    acc ++ fencedText (fenceIndent ind rendered) (fenceFor (String.join rendered)) "" rendered
  | .columns cols => columnsInto tw summary ind acc cols.toList
  | .onSteps _ body => blocksInto tw summary ind acc none body.toList
  | .altSteps _ active otherwise =>
    blocksInto tw summary ind (blocksInto tw summary ind acc none active.toList) none
      otherwise.toList
  -- `emit` already kept this node for markdown.
  | .only _ body => blocksInto tw summary ind acc none body.toList
  -- A nav is furniture, not content.
  | .nav _ _ => acc
  -- A speaker note is a side channel in every backend.
  | .note _ => acc
  -- Frame-footer chrome is page furniture.
  | .framefoot _ => acc
  -- A design declaration carries no text.
  | .setPalette _ => acc
  | .setTokens _ => acc
  -- A continuous medium has no page to break.
  | .pagebreak => acc
  -- A logo is page furniture.
  | .logo _ => acc
  -- A rule is decorative ink.
  | .rule _ _ _ => acc
  -- A picture's labels are not prose in reading order.
  | .picture _ => acc
  | .frame title _ _ _ body =>
    let head := if title.isEmpty then "" else ind ++ "## " ++ headingText title tw.cites ++ "\n\n"
    blocksInto tw summary ind (acc ++ head) none body.toList
  -- The GFM pipe table: one line per row, the separator after the first.
  | .table cols _ _ rows _ _ =>
    let line (row : Array (Array Inline)) : String := rowLine (row.toList.map (cellText · tw.cites))
    let sep := "|" ++ String.join (cols.toList.map fun c =>
      match c.align with
      | .left => " --- |"
      | .center => " :---: |"
      | .right => " ---: |")
    match rows.toList with
    | [] => acc
    | first :: rest =>
      acc ++ ind ++ line first ++ "\n" ++ ind ++ sep ++ "\n"
        ++ String.join (rest.map fun r => ind ++ line r ++ "\n") ++ "\n"
  -- A float's caption is a paragraph beside its content, in source order.
  | .float kind num capAbove body caption =>
    let cap := if caption.isEmpty then ""
      else
        paraText ind ind (inlineText (Ir.numberedCaption tw.loc kind num caption) tw.cites) ++
          "\n\n"
    if capAbove then blocksInto tw summary ind (acc ++ cap) none body.toList
    else blocksInto tw summary ind acc none body.toList ++ cap
  -- A twin that declares the bibliography places its list where the reader reads it back.
  | .bibliography src _ items =>
    let entries := bibItemsText tw.cites ind items
    let listed := refsComment ind items
    if tw.cites && !src.isEmpty then acc ++ ind ++ "::: {#refs}\n" ++ listed ++ ind ++ ":::\n\n"
    else acc ++ entries
  -- `twinBody` has set every table of contents as its list.
  | .contents _ _ => acc
termination_by structural b => b

/-- A block sequence; a list after a list of its kind takes
the other marker (§5.3). -/
private def blocksInto (tw : Twin) (summary ind acc : String)
    (prev : Option (Bool × Bool)) : List Block → String
  | [] => acc
  | .list ordered _ items :: rest =>
    let alt := listAlt prev ordered
    let text := itemsInto tw summary ind ordered alt 1 "" items.toList
    blocksInto tw summary ind (acc ++ text ++ "\n") (some (ordered, alt)) rest
  | b :: rest => blocksInto tw summary ind (blockInto tw summary ind acc b) none rest
termination_by structural bs => bs

private def columnsInto (tw : Twin) (summary ind acc : String) :
    List (BoxWidth × Array Block) → String
  | [] => acc
  | (_, body) :: rest => columnsInto tw summary ind (blocksInto tw summary ind acc none body.toList) rest
termination_by structural cols => cols

/-- List items: `- ` or `k. `, every further line indented
to the content column (§5.2). -/
private def itemsInto (tw : Twin) (summary ind : String) (ordered alt : Bool) (k : Nat)
    (acc : String) : List (Array Block) → String
  | [] => acc
  | item :: rest =>
    let marker := if ordered then s!"{k}{if alt then ")" else "."} " else if alt then "+ " else "- "
    let cont := ind ++ String.ofList (List.replicate marker.length ' ')
    let pen := itemSeq tw summary cont { acc, first := some (ind ++ marker), prev := none }
      item.toList
    let acc := match pen.first with
      | some m => pen.acc ++ m ++ "\n"
      | none => pen.acc
    itemsInto tw summary ind ordered alt (k + 1) acc rest
termination_by structural items => items

/-- An item's blocks, in order, from where the pen stands. -/
private def itemSeq (tw : Twin) (summary cont : String) (pen : ItemPen) :
    List Block → ItemPen
  | [] => pen
  | b :: rest =>
    let write (_ : Unit) := itemPut cont pen (leadsWithList b) (blockInto tw summary cont "" b)
    let pen := match (generalizing := false) b with
      | .list ordered _ items =>
        match pen.first with
        | some first =>
          let head := itemHead first cont (itemsInto tw summary cont ordered false 1 "" items.toList)
          { acc := pen.acc ++ head ++ "\n", first := none, prev := some (ordered, false) }
        | none =>
          let alt := listAlt pen.prev ordered
          { pen with acc := pen.acc ++ itemsInto tw summary cont ordered alt 1 "" items.toList,
                     prev := some (ordered, alt) }
      | .role _ body => itemSeq tw summary cont pen body.toList
      | .spaced _ body => itemSeq tw summary cont pen body.toList
      | .only _ body => itemSeq tw summary cont pen body.toList
      | .onSteps _ body => itemSeq tw summary cont pen body.toList
      | .altSteps _ active otherwise =>
        itemSeq tw summary cont (itemSeq tw summary cont pen active.toList) otherwise.toList
      | .center body => itemSeq tw summary cont pen body.toList
      | .ragged _ body => itemSeq tw summary cont pen body.toList
      | .link _ body => itemSeq tw summary cont pen body.toList
      | .columns cols => itemColumns tw summary cont pen cols.toList
      | .para _ => write ()
      | .lines _ => write ()
      | .equation _ _ => write ()
      | .section _ _ _ _ => write ()
      | .quote _ _ => write ()
      | .abstract _ => write ()
      | .titled _ _ _ => write ()
      | .disclosure _ _ _ => write ()
      | .bibliography _ _ _ => write ()
      | .contents _ _ => write ()
      | .verbatim _ _ _ => write ()
      | .algorithm _ _ _ => write ()
      | .nav _ _ => write ()
      | .note _ => write ()
      | .framefoot _ => write ()
      | .setPalette _ => write ()
      | .setTokens _ => write ()
      | .pagebreak => write ()
      | .logo _ => write ()
      | .rule _ _ _ => write ()
      | .picture _ => write ()
      | .frame _ _ _ _ _ => write ()
      | .table _ _ _ _ _ _ => write ()
      | .float _ _ _ _ _ => write ()
    itemSeq tw summary cont pen rest
termination_by structural bs => bs

/-- Columns inside an item: each column's blocks in turn. -/
private def itemColumns (tw : Twin) (summary cont : String) (pen : ItemPen) :
    List (BoxWidth × Array Block) → ItemPen
  | [] => pen
  | (_, body) :: rest =>
    itemColumns tw summary cont (itemSeq tw summary cont pen body.toList) rest
termination_by structural cols => cols

end

/-- The tightening walk: a newline past the second in a row is dropped. -/
private def tightenGo (nn : Nat) (acc : List Char) : List Char → List Char
  | [] => acc
  | c :: rest =>
    if c == '\n' then
      if nn ≥ 2 then tightenGo nn acc rest
      else tightenGo (nn + 1) (c :: acc) rest
    else tightenGo 0 (c :: acc) rest

/-- At most one blank line in a row, exactly one trailing newline. -/
private def tighten (s : String) : String :=
  let trimmed := String.ofList ((tightenGo 0 [] s.toList).dropWhile (· == '\n')).reverse
  if trimmed.isEmpty then trimmed else trimmed ++ "\n"

/-- A note's content with each note nested in it spelled in place, in parentheses: markdown's notes
hold no note. -/
-- conserves: none — moves a nested note's text into the note holding it.
private def unnest (content : Array Inline) : Array Inline :=
  Ir.mapInlines id content (finish := fun ys => ys.foldl (init := #[]) fun acc y => match y with
    | .footnote _ inner =>
      let spaced := match acc.back? with
        | some (.text t) => t.endsWith " " || t.endsWith "\u00a0"
        | _ => false
      acc.push (.text (if spaced then "(" else " (")) ++ inner |>.push (.text ")")
    | y => acc.push y)

/-- Footnotes numbered by the place of their first equal one among the body's, so a twin's label
names one note whatever marks the document repeats, a nested note spelled inside its own. -/
-- conserves: none — renumbers notes only, through the generic map's sibling hook.
private def notesByPlace (body : Array Block) : Array Block :=
  let flat := Ir.mapBlocks id body (finish := fun xs => xs.map fun x => match x with
    | .footnote n content => .footnote n (unnest content)
    | x => x)
  let notes := Ir.footnotesOf flat
  if notes.isEmpty then flat else
  let key (n : Option Nat) (content : Array Inline) : String := s!"{n}|{Ir.plainText content}"
  let table : Std.HashMap String (Array ((Option Nat × Array Inline) × Nat)) :=
    notes.zipIdx.foldl (init := {}) fun m (e, i) => m.insert (key e.1 e.2) ((m.getD (key e.1 e.2) #[]).push (e, i + 1))
  let place (n : Option Nat) (content : Array Inline) : Option Nat :=
    ((table.getD (key n content) #[]).find? (·.1 == (n, content))).map (·.2)
  Ir.mapBlocks id flat (finish := fun xs => xs.map fun x => match x with
    | .footnote n content => .footnote ((place n content).orElse fun _ => n) content
    | x => x)

/-- The twin's view of a document's body: source locations erased, backend conditionals resolved
for markdown, footnotes numbered by their place and each table of contents a list. -/
public def twinBody (doc : Doc) : Array Block :=
  notesByPlace (Ir.rewriteContents (fun _ entries => Ir.contentsList entries)
    (Ir.keepFor "md" (Ir.eraseLocations doc).body))

/-- The `[^k]: …` definitions, one per footnote in flow
order; empty without notes. -/
private def noteDefs (cites : Bool) (body : Array Block) : String := Id.run do
  let notes := Ir.footnotesOf body
  if notes.isEmpty then return ""
  let mut out := ""
  let mut written : Std.HashSet Nat := {}
  for (num, content) in notes do
    let label := num.getD 0
    unless written.contains label do
      written := written.insert label
      -- The reader sets a definition at its reference, so a note's citation keeps its place.
      -- An empty note's comment keeps the next definition from reading as its content.
      let text := inlineText content cites
      let text := if text.trimAscii.isEmpty then "<!-- -->" else text
      out := out ++ "\n" ++ paraText s!"[^{label}]: " "    " text ++ "\n"
  return out

/-- A YAML scalar the twin's metadata writes: plain where the reader reads it so, else quoted. -/
private def yamlScalar (s : String) : String :=
  if !s.isEmpty && !s.startsWith "-" &&
      s.all (fun c => c.isAlphanum || c == '.' || c == '-' || c == '_' || c == '/') then s
  else "'" ++ s.replace "'" "''" ++ "'"

/-- The twin's closing metadata block, where the document's citations can read back through
Pandoc's syntax: its one list's bibliography, named as `bibName` places it, its style, natbib's
options, and every listed entry as `nocite`, so the list reads back whole; empty elsewhere. -/
public def twinMeta (doc : Doc) (bibName : String → String := id) : String :=
  let lists := Ir.foldBlocks (fun out b => match b with
    | .bibliography src style items => out.push (src, style, items)
    | _ => out) (fun out _ => out) #[] doc.body
  match lists.toList, doc.citeSetup.bind CiteDecl.options? with
  | [(src, style, items)], some opts =>
    if src.isEmpty then "" else
    let lists := #[(style, items)]
    let names := (Ir.bibRefs doc).map fun n => bibName (if n.endsWith ".bib" then n else n ++ ".bib")
    let bib := match names.toList with
      | [one] => yamlScalar one
      | many => "[" ++ ", ".intercalate (many.map yamlScalar) ++ "]"
    let listed := Id.run do
      let mut seen : Std.HashSet String := {}
      let mut out : Array String := #[]
      for (_, items) in lists do
        for it in items do
          unless seen.contains it.key do
            seen := seen.insert it.key
            out := out.push it.key
      return out
    let nocite := listed.filterMap fun k => CiteKey.spelling? k none
    let optLine := if opts.isEmpty then "" else
      "\nnatbiboptions: " ++ yamlScalar (",".intercalate opts.toList)
    let nociteLine := if nocite.isEmpty then "" else
      "\nnocite: '" ++ (", ".intercalate nocite.toList).replace "'" "''" ++ "'"
    "\n---\nbibliography: " ++ bib ++ "\nbiblio-style: " ++ yamlScalar (style.getD "unsrtnat") ++
      optLine ++ nociteLine ++ "\n---\n"
  | _, _ => ""

/-- The twin in a citation mode: its body, its footnotes, then `back`. -/
public def twinIn (doc : Doc) (cites : Bool) (back : String) : String :=
  let doc := { doc with body := twinBody doc }
  let summary := match doc.info.subject with
    | some s => "> " ++ summaryLine s cites ++ "\n\n"
    | none => ""
  let bodyTitled := (headingLevels doc.body).contains 0
  let title := match doc.info.title with
    | some t => if bodyTitled then "" else "# " ++ titleLine t cites ++ "\n\n"
    | none => ""
  let preamble := title ++ (if bodyTitled then "" else summary)
  tighten (preamble ++ blocksInto ⟨doc.info.locale, cites⟩ summary "" "" none doc.body.toList)
    ++ noteDefs cites doc.body ++ back

/-- The twin's closing metadata block, with `bibName` placing its bibliography. -/
public def twinBack (doc : Doc) (bibName : String → String) : String :=
  twinMeta { doc with body := twinBody doc } bibName

/-- Whether the twin spells the document's citations in Pandoc's syntax: they read back through a
closing metadata block, each spelled where it stands. -/
public def twinCites (doc : Doc) (bibName : String → String := id) : Bool :=
  let back := twinBack doc bibName
  !back.isEmpty && !(twinIn doc true back).contains '\uE000'

/-- The document's markdown twin: its citations in Pandoc's syntax under the metadata block it
closes with, where they read back so, else as their marks. -/
public def emit (doc : Doc) (bibName : String → String := id) : String :=
  let cites := twinCites doc bibName
  twinIn doc cites (if cites then twinBack doc bibName else "")

-- Sealed so unification cannot unfold the collection walk.
seal noteDefs

private theorem append_nil (a : String) : ∃ r, a = a ++ r :=
  ⟨"", by simp⟩

private theorem append_chain₂ (a b c : String) : ∃ r, a ++ b ++ c = a ++ r :=
  ⟨b ++ c, by simp [String.append_assoc]⟩

private theorem append_chain₆ (a b c d e f g : String) :
    ∃ r, a ++ b ++ c ++ d ++ e ++ f ++ g = a ++ r :=
  ⟨b ++ (c ++ (d ++ (e ++ (f ++ g)))), by simp [String.append_assoc]⟩

private theorem append_chain₇ (a b c d e f g h : String) :
    ∃ r, a ++ b ++ c ++ d ++ e ++ f ++ g ++ h = a ++ r :=
  ⟨b ++ (c ++ (d ++ (e ++ (f ++ (g ++ h))))), by simp [String.append_assoc]⟩

private theorem append_chain₈ (a b c d e f g h i : String) :
    ∃ r, a ++ b ++ c ++ d ++ e ++ f ++ g ++ h ++ i = a ++ r :=
  ⟨b ++ (c ++ (d ++ (e ++ (f ++ (g ++ (h ++ i)))))), by simp [String.append_assoc]⟩

private theorem extends_comp {a g f : String} (h₁ : ∃ r, g = a ++ r)
    (h₂ : ∃ r, f = g ++ r) : ∃ q, f = a ++ q := by
  obtain ⟨r₁, h₁⟩ := h₁
  obtain ⟨r₂, h₂⟩ := h₂
  exact ⟨r₁ ++ r₂, by rw [h₂, h₁, String.append_assoc]⟩

mutual

private theorem blockInto_extends (tw : Twin) (summary ind acc : String) :
    (b : Block) → ∃ r, blockInto tw summary ind acc b = acc ++ r
  | .para _ => by
    simp only [blockInto]
    exact append_chain₂ _ _ _
  | .lines _ => by
    simp only [blockInto]
    exact append_chain₂ _ _ _
  | .equation _ _ => by
    simp only [blockInto]
    exact append_chain₂ _ _ _
  | .section _ _ _ _ => by
    simp only [blockInto]
    split
    · exact append_chain₇ _ _ _ _ _ _ _ _
    · exact append_chain₆ _ _ _ _ _ _ _
  | .list _ _ _ => by
    simp only [blockInto]
    exact append_chain₂ _ _ _
  | .center body => blocksInto_extends tw summary ind acc none body.toList
  | .ragged _ body => blocksInto_extends tw summary ind acc none body.toList
  | .quote _ _ => by
    simp only [blockInto]
    exact append_chain₂ _ _ _
  | .abstract body =>
    extends_comp ⟨_, rfl⟩ (blocksInto_extends tw summary ind
      (acc ++ (ind ++ "## " ++ tw.loc.abstract ++ "\n\n")) none body.toList)
  | .titled _ title body =>
    extends_comp ⟨_, rfl⟩ (blocksInto_extends tw summary ind
      (acc ++ if title.isEmpty then "" else
        paraText ind ind (inlineText #[.styled .bold title] tw.cites) ++ "\n\n")
      none body.toList)
  | .disclosure _ _ _ => ⟨_, rfl⟩
  | .spaced _ body => blocksInto_extends tw summary ind acc none body.toList
  | .bibliography src _ items => by
    simp only [blockInto]
    split
    · exact ⟨ind ++ "::: {#refs}\n" ++ refsComment ind items ++ ind ++ ":::\n\n",
        by simp [String.append_assoc]⟩
    · exact ⟨_, rfl⟩
  | .contents _ _ => append_nil acc
  | .role _ body => blocksInto_extends tw summary ind acc none body.toList
  | .link _ body => blocksInto_extends tw summary ind acc none body.toList
  | .verbatim _ _ _ => by
    simp only [blockInto]
    exact append_chain₂ _ _ _
  | .algorithm _ _ _ => ⟨_, rfl⟩
  | .columns cols => columnsInto_extends tw summary ind acc cols.toList
  | .onSteps _ body => blocksInto_extends tw summary ind acc none body.toList
  | .altSteps _ active otherwise =>
    extends_comp (blocksInto_extends tw summary ind acc none active.toList)
      (blocksInto_extends tw summary ind _ none otherwise.toList)
  | .only _ body => blocksInto_extends tw summary ind acc none body.toList
  | .nav _ _ => append_nil acc
  | .note _ => append_nil acc
  | .framefoot _ => append_nil acc
  | .setPalette _ => append_nil acc
  | .setTokens _ => append_nil acc
  | .pagebreak => append_nil acc
  | .logo _ => append_nil acc
  | .rule _ _ _ => append_nil acc
  | .picture _ => append_nil acc
  | .frame title _ _ _ body =>
    extends_comp ⟨_, rfl⟩ (blocksInto_extends tw summary ind
      (acc ++ if title.isEmpty then "" else ind ++ "## " ++ headingText title tw.cites ++ "\n\n")
      none body.toList)
  | .table _ _ _ rows _ _ => by
    simp only [blockInto]
    split
    · exact append_nil acc
    · exact append_chain₈ _ _ _ _ _ _ _ _ _
  | .float kind num capAbove body caption => by
    simp only [blockInto]
    split
    · exact extends_comp ⟨_, rfl⟩ (blocksInto_extends tw summary ind
        (acc ++ if caption.isEmpty then "" else
          paraText ind ind (inlineText (Ir.numberedCaption tw.loc kind num caption) tw.cites) ++
            "\n\n")
        none body.toList)
    · exact extends_comp (blocksInto_extends tw summary ind acc none body.toList) ⟨_, rfl⟩

private theorem blocksInto_extends (tw : Twin) (summary ind acc : String)
    (prev : Option (Bool × Bool)) :
    (bs : List Block) → ∃ r, blocksInto tw summary ind acc prev bs = acc ++ r
  | [] => append_nil acc
  | .list _ _ _ :: rest => by
    simp only [blocksInto]
    exact extends_comp (append_chain₂ _ _ _) (blocksInto_extends tw summary ind _ _ rest)
  | b :: rest => by
    have hb := blockInto_extends tw summary ind acc b
    have hrest := fun acc' p => blocksInto_extends tw summary ind acc' p rest
    cases b with
    | list _ _ =>
      simp only [blocksInto]
      exact extends_comp (append_chain₂ _ _ _) (hrest _ _)
    | _ =>
      simp only [blocksInto]
      exact extends_comp hb (hrest _ _)

private theorem columnsInto_extends (tw : Twin) (summary ind acc : String) :
    (cols : List (BoxWidth × Array Block)) →
      ∃ r, columnsInto tw summary ind acc cols = acc ++ r
  | [] => append_nil acc
  | (_, body) :: rest =>
    extends_comp (blocksInto_extends tw summary ind acc none body.toList)
      (columnsInto_extends tw summary ind (blocksInto tw summary ind acc none body.toList) rest)

end

private theorem tightenGo_extends : (l : List Char) → ∀ (nn : Nat) (acc : List Char),
    ∃ w, tightenGo nn acc l = w ++ acc
  | [], _, _ => ⟨[], rfl⟩
  | c :: rest, nn, acc => by
    simp only [tightenGo]
    split
    · split
      · exact tightenGo_extends rest nn acc
      · obtain ⟨w, hw⟩ := tightenGo_extends rest (nn + 1) (c :: acc)
        exact ⟨w ++ [c], by simp [hw]⟩
    · obtain ⟨w, hw⟩ := tightenGo_extends rest 0 (c :: acc)
      exact ⟨w ++ [c], by simp [hw]⟩

private theorem tightenGo_flat : (cs : List Char) → (∀ c ∈ cs, c ≠ '\n') → cs ≠ [] →
    ∀ (nn : Nat) (acc l : List Char),
      tightenGo nn acc (cs ++ l) = tightenGo 0 (cs.reverse ++ acc) l
  | [], _, hne => absurd rfl hne
  | c :: cs, h, _ => by
    intro nn acc l
    have hc : (c == '\n') = false := by
      simpa using h c (List.mem_cons_self ..)
    simp only [List.cons_append, tightenGo, hc]
    cases cs with
    | nil => simp
    | cons d ds =>
      rw [tightenGo_flat (d :: ds) (fun x hx => h x (List.mem_cons_of_mem _ hx))
        (by simp) 0 (c :: acc) l]
      simp

private theorem tightenGo_blank (acc l : List Char) :
    tightenGo 0 acc ('\n' :: '\n' :: l) = tightenGo 2 ('\n' :: '\n' :: acc) l := by
  simp [tightenGo]

private theorem head_mem_left {c : Char} : (xs : List Char) → xs ≠ [] →
    ∀ ys, (xs ++ ys).head? = some c → c ∈ xs
  | [], hne, _, _ => absurd rfl hne
  | x :: _, _, ys, h => by
    simp only [List.cons_append, List.head?_cons, Option.some.injEq] at h
    exact h ▸ List.mem_cons_self

private theorem tighten_of_fold (s : String) (w Qrev : List Char) (hne : Qrev ≠ [])
    (hhead : ∀ c, Qrev.head? = some c → c ≠ '\n')
    (hfold : tightenGo 0 [] s.toList = w ++ '\n' :: '\n' :: Qrev) :
    ∃ q, tighten s = String.ofList Qrev.reverse ++ q := by
  obtain ⟨c, cs, rfl⟩ : ∃ c cs, Qrev = c :: cs := by
    cases Qrev with
    | nil => exact absurd rfl hne
    | cons c cs => exact ⟨c, cs, rfl⟩
  have hc : (c == '\n') = false := by
    simpa using hhead c rfl
  simp only [tighten, hfold, List.dropWhile_append]
  split
  · rw [show List.dropWhile (· == '\n') ('\n' :: '\n' :: c :: cs) = c :: cs by
      simp [hc]]
    refine ⟨"\n", ?_⟩
    split
    · next hemp => simp at hemp
    · rfl
  · refine ⟨String.ofList (['\n', '\n'] ++
      (List.dropWhile (· == '\n') w).reverse) ++ "\n", ?_⟩
    rw [show (List.dropWhile (· == '\n') w ++ '\n' :: '\n' :: c :: cs).reverse =
      (c :: cs).reverse ++ (['\n', '\n'] ++
        (List.dropWhile (· == '\n') w).reverse) by simp]
    split
    · next hemp => simp at hemp
    · rw [String.ofList_append, String.append_assoc]

private theorem tighten_head (X s r : String)
    (hX : ∀ c ∈ X.toList, c ≠ '\n') (hs : ∀ c ∈ s.toList, c ≠ '\n') :
    ∃ q, tighten ("# " ++ X ++ "\n\n" ++ ("> " ++ s ++ "\n\n") ++ r) =
      "# " ++ X ++ "\n\n" ++ "> " ++ s ++ q := by
  have hA : ∀ c ∈ '#' :: ' ' :: X.toList, c ≠ '\n' := by
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | rfl | hc
    · decide
    · decide
    · exact hX c hc
  have hB : ∀ c ∈ '>' :: ' ' :: s.toList, c ≠ '\n' := by
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | rfl | hc
    · decide
    · decide
    · exact hs c hc
  obtain ⟨w, hw⟩ := tightenGo_extends r.toList 2
    ('\n' :: '\n' :: (('>' :: ' ' :: s.toList).reverse ++
      '\n' :: '\n' :: (('#' :: ' ' :: X.toList).reverse ++ [])))
  have hfold : tightenGo 0 []
      (("# " ++ X ++ "\n\n" ++ ("> " ++ s ++ "\n\n") ++ r).toList) =
      w ++ '\n' :: '\n' :: (('>' :: ' ' :: s.toList).reverse ++
        '\n' :: '\n' :: ('#' :: ' ' :: X.toList).reverse) := by
    rw [show ("# " ++ X ++ "\n\n" ++ ("> " ++ s ++ "\n\n") ++ r).toList =
      ('#' :: ' ' :: X.toList) ++ '\n' :: '\n' ::
        (('>' :: ' ' :: s.toList) ++ '\n' :: '\n' :: r.toList) by
      simp [String.toList_append, show "# ".toList = ['#', ' '] from rfl,
        show "\n\n".toList = ['\n', '\n'] from rfl,
        show "> ".toList = ['>', ' '] from rfl]]
    rw [tightenGo_flat ('#' :: ' ' :: X.toList) hA (by simp)]
    rw [tightenGo_blank]
    rw [tightenGo_flat ('>' :: ' ' :: s.toList) hB (by simp)]
    rw [tightenGo_blank]
    rw [hw]
    simp
  have hhead : ∀ c, (('>' :: ' ' :: s.toList).reverse ++
      '\n' :: '\n' :: ('#' :: ' ' :: X.toList).reverse).head? = some c →
      c ≠ '\n' := fun c hc =>
    hB c (List.mem_reverse.mp
      (head_mem_left (('>' :: ' ' :: s.toList).reverse) (by simp) _ hc))
  obtain ⟨q, hq⟩ := tighten_of_fold _ w _ (by simp) hhead hfold
  have key : String.ofList ((('>' :: ' ' :: s.toList).reverse ++
      '\n' :: '\n' :: ('#' :: ' ' :: X.toList).reverse).reverse) =
      "# " ++ X ++ "\n\n" ++ "> " ++ s := by
    rw [show (('>' :: ' ' :: s.toList).reverse ++
        '\n' :: '\n' :: ('#' :: ' ' :: X.toList).reverse).reverse =
      ['#', ' '] ++ (X.toList ++ (['\n', '\n'] ++ (['>', ' '] ++ s.toList))) by simp]
    simp only [String.ofList_append, String.ofList_toList]
    rw [show String.ofList ['#', ' '] = "# " from rfl,
      show String.ofList ['\n', '\n'] = "\n\n" from rfl,
      show String.ofList ['>', ' '] = "> " from rfl]
    simp [String.append_assoc]
    rw [← String.append_assoc, show ("\n\n" : String) ++ "> " = "\n\n> " from rfl]
  exact ⟨q, by rw [hq, key]⟩

mutual

private theorem headingLevelList_mem (x : Ir.HeadingLevel) :
    (l : List Block) → (out : Array Ir.HeadingLevel) → x ∈ out → x ∈ Ir.headingLevelList out l
  | [], _, h => h
  | b :: rest, out, h =>
    headingLevelList_mem x rest (Ir.headingLevelOne out b)
      (headingLevelOne_mem x b out h)

private theorem headingLevelOne_mem (x : Ir.HeadingLevel) :
    (b : Block) → (out : Array Ir.HeadingLevel) → x ∈ out → x ∈ Ir.headingLevelOne out b
  | .section _ _ _ _, _, h => Array.mem_push_of_mem _ h
  | .para _, _, h => h
  | .equation _ _, _, h => h
  | .list _ _ items, out, h => headingLevelItems_mem x items.toList out h
  | .center body, out, h => headingLevelList_mem x body.toList out h
  | .ragged _ body, out, h => headingLevelList_mem x body.toList out h
  | .quote _ body, out, h => headingLevelList_mem x body.toList out h
  | .lines _, _, h => h
  | .abstract body, out, h => headingLevelList_mem x body.toList out h
  | .titled _ _ body, out, h => headingLevelList_mem x body.toList out h
  | .disclosure _ _ body, out, h => headingLevelList_mem x body.toList out h
  | .role _ body, out, h => headingLevelList_mem x body.toList out h
  | .link _ body, out, h => headingLevelList_mem x body.toList out h
  | .spaced _ body, out, h => headingLevelList_mem x body.toList out h
  | .columns cols, out, h => headingLevelColumns_mem x cols.toList out h
  | .onSteps _ body, out, h => headingLevelList_mem x body.toList out h
  | .altSteps _ active otherwise, out, h =>
    headingLevelList_mem x otherwise.toList (Ir.headingLevelList out active.toList)
      (headingLevelList_mem x active.toList out h)
  | .only _ body, out, h => headingLevelList_mem x body.toList out h
  | .nav _ body, out, h => headingLevelList_mem x body.toList out h
  | .frame _ _ _ _ body, out, h => headingLevelList_mem x body.toList out h
  | .note _, _, h => h
  | .verbatim _ _ _, _, h => h
  | .algorithm _ _ _, _, h => h
  | .bibliography _ _ _, _, h => h
  | .contents _ _, _, h => h
  | .framefoot _, _, h => h
  | .setPalette _, _, h => h
  | .setTokens _, _, h => h
  | .pagebreak, _, h => h
  | .logo _, _, h => h
  | .rule _ _ _, _, h => h
  | .picture _, _, h => h
  | .table _ _ _ _ _ _, _, h => h
  | .float _ _ _ body _, out, h => headingLevelList_mem x body.toList out h

private theorem headingLevelItems_mem (x : Ir.HeadingLevel) :
    (items : List (Array Block)) → (out : Array Ir.HeadingLevel) → x ∈ out →
      x ∈ Ir.headingLevelItems out items
  | [], _, h => h
  | item :: rest, out, h =>
    headingLevelItems_mem x rest (Ir.headingLevelList out item.toList)
      (headingLevelList_mem x item.toList out h)

private theorem headingLevelColumns_mem (x : Ir.HeadingLevel) :
    (cols : List (BoxWidth × Array Block)) → (out : Array Ir.HeadingLevel) → x ∈ out →
      x ∈ Ir.headingLevelColumns out cols
  | [], _, h => h
  | (_, body) :: rest, out, h =>
    headingLevelColumns_mem x rest (Ir.headingLevelList out body.toList)
      (headingLevelList_mem x body.toList out h)

end

public theorem emit_meta_title_first (doc : Doc) (bibName : String → String) (t s : String)
    (ht : doc.info.title = some t) (hs : doc.info.subject = some s)
    (hbody : ((Ir.headingLevels (twinBody doc)).contains 0) = false) :
    ∃ q, emit doc bibName = "# " ++ titleLine t (twinCites doc bibName) ++ "\n\n" ++ "> " ++
      summaryLine s (twinCites doc bibName) ++ q := by
  let c := twinCites doc bibName
  let back := if c then twinBack doc bibName else ""
  obtain ⟨q, hq⟩ := tighten_head (titleLine t c) (summaryLine s c)
    (blocksInto ⟨doc.info.locale, c⟩ ("> " ++ summaryLine s c ++ "\n\n") "" "" none
      (twinBody doc).toList)
    (fun x hx => (titleLine_contract t _ x hx).1) (fun x hx => (summaryLine_contract s _ x hx).1)
  refine ⟨q ++ noteDefs c (twinBody doc) ++ back, ?_⟩
  show twinIn doc c back = _
  simp only [twinIn, ht, hs, hbody, Bool.false_eq_true, ↓reduceIte]
  rw [hq]
  simp only [String.append_assoc]
  rfl

public theorem emit_body_title_first (doc : Doc) (bibName : String → String) (s : String)
    (st : Bool) (ttl : Array Inline) (rest : List Block)
    (hs : doc.info.subject = some s)
    (hbody : (twinBody doc).toList = .section 0 st none ttl :: rest) :
    ∃ q, emit doc bibName = "# " ++ headingText ttl (twinCites doc bibName) ++ "\n\n" ++ "> " ++
      summaryLine s (twinCites doc bibName) ++ q := by
  have h0 : (0 : Ir.HeadingLevel) ∈ Ir.headingLevels (twinBody doc) := by
    show (0 : Ir.HeadingLevel) ∈ Ir.headingLevelList #[] (twinBody doc).toList
    rw [hbody]
    exact headingLevelList_mem 0 rest _ (by
      show (0 : Ir.HeadingLevel) ∈ (#[] : Array Ir.HeadingLevel).push 0
      simp)
  have hbt : (Ir.headingLevels (twinBody doc)).contains 0 = true :=
    Array.contains_eq_true_of_mem h0
  let c := twinCites doc bibName
  let back := if c then twinBack doc bibName else ""
  let tw : Twin := ⟨doc.info.locale, c⟩
  let sm := "> " ++ summaryLine s c ++ "\n\n"
  have hfirst : blocksInto tw sm "" "" none (twinBody doc).toList =
      blocksInto tw sm "" ("# " ++ headingText ttl c ++ "\n\n" ++ sm) none rest := by
    rw [hbody]
    simp [blocksInto, blockInto, headingMarker, Ir.headingRank, tw, sm]
  obtain ⟨w, hw⟩ := blocksInto_extends tw sm "" ("# " ++ headingText ttl c ++ "\n\n" ++ sm) none rest
  obtain ⟨q, hq⟩ := tighten_head (headingText ttl c) (summaryLine s c) w
    (fun x hx => (headingText_contract ttl _ x hx).1)
    (fun x hx => (summaryLine_contract s _ x hx).1)
  refine ⟨q ++ noteDefs c (twinBody doc) ++ back, ?_⟩
  show twinIn doc c back = _
  cases hT : doc.info.title with
  | some t =>
    simp only [twinIn, hs, hbt, hT, ite_true, String.empty_append]
    rw [hfirst, hw, hq]
    simp only [String.append_assoc]
    rfl
  | none =>
    simp only [twinIn, hs, hbt, hT, ite_true, String.empty_append]
    rw [hfirst, hw, hq]
    simp only [String.append_assoc]
    rfl

end LeanTex.Core.MarkdownDoc
