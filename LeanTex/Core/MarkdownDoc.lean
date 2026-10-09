module

public import LeanTex.Core.Ir

/-! The markdown backend. A web page today publishes a plain-text twin — the
llms.txt convention (llmstxt.org): `# title`, a `> summary`, then sections —
and the twin is only trustworthy if it comes from the same source as the
page. Here it is the same IR the HTML and PDF backends consume: the document
metadata renders as the llms.txt preamble (markdown has no `<head>`, so the
title and subject become the `#` line and the blockquote), and the body maps
structurally. Like every backend, this one consumes the IR and nothing else.

The twin is written to be read back. Text escapes what would read as
markup, raw HTML and character references included (`escapeText`); a
paragraph's every line goes through `escapeLineStart` (`paraText`), whose
output opens no block (`escapeLineStart_contract` — the theorem is the
helper's, and the paragraph arms reaching it is this file's code, which the
twin rows check end to end); a code span holds its text exactly, and a fence
the lines every backend shows (`verbatimLines`), blank lines included; a
container's prefix stands on every line of its blocks; a link's destination
reads back as it stands, a link whose text is its plain destination is an
autolink, and a link in code-set text keeps its destination and its face.
A heading, a pipe table's cell and the llms.txt title and summary each
stand on one line (`headingText_contract`, `cellText_contract`,
`titleLine_contract`, `summaryLine_contract`), the metadata written as text
as the body's text is, and a row reads as exactly its cells under GFM's row
grammar (`rowLine_cells_exact`), every pipe a cell holds escaped. Where markdown has no spelling for what the IR holds —
a formula, a footnote, an overlay, a table the reader does not read yet, a
hard break inside a heading or a cell, which is written as a space — the
twin writes the nearest one, and the difference is a loss, not a spelling.
The round trip is measured, never assumed: the `mdtwin` tier counts the
CommonMark examples and corpus documents whose twin re-reads to the same IR,
and `Tests/MarkdownTwin.lean` pins each spelling class.

**External premise — the reader hop.** What a twin means to the world is
what a CommonMark reader makes of it; this module claims that a CommonMark
reader parses every spelling the twin writes as the markdown door does. A
premise about a tool, held by evidence and never proved: the commonmark
tier's `match` verdicts, ratcheted, in the sections those spellings live in
— ATX headings, lists, list items, fenced code, code spans, emphasis,
links, images, autolinks, block quotes, hard breaks, backslash escapes —
and the direct check, `scripts/commonmark.lean --reader-hop`, which reads
every corpus document's twin and every accepted CommonMark example's twin
with an external CommonMark reader and with the door, at the classifier's
comparison, and every twin's pipe tables with an external GFM table reader
against the rows `gfmRow` reads. It needs the tool, so it is a report and
never a gate. -/

namespace LeanTex.Core.MarkdownDoc

open LeanTex.Core LeanTex.Core.Ir

/-- Escape the characters that would read as markup anywhere in a line:
CommonMark's inline punctuation, the pipe table's cell separator where
`pipes` says the line is not a cell (a cell escapes every pipe it holds
itself, `rowLine`), and `<` and `&`, so the twin never writes raw HTML
(§6.6) or reads a character reference (§2.5) into its text — each is a
valid backslash escape (§2.4: any ASCII punctuation). A line ending inside
text is the one character it spells as a numeric reference, since it has no
other spelling. What opens a block only at a line's start is the line's
business (`escapeLineStart`). -/
private def escapeChars (pipes : Bool) : List Char → List Char
  | [] => []
  | c :: rest =>
    if c == '\\' || c == '`' || c == '*' || c == '_' || c == '[' || c == ']'
        || (pipes && c == '|') || c == '<' || c == '&' then
      '\\' :: c :: escapeChars pipes rest
    -- a line ending inside text has no other spelling: a newline would end
    -- the line, and a paragraph's text cannot hold one
    else if c == '\n' then '&' :: '#' :: '1' :: '0' :: ';' :: escapeChars pipes rest
    else if c == '\r' then '&' :: '#' :: '1' :: '3' :: ';' :: escapeChars pipes rest
    else c :: escapeChars pipes rest

private def escapeText (pipes : Bool) (s : String) : String :=
  String.ofList (escapeChars pipes s.toList)

/-- Escaped text holds no line ending. -/
private theorem escapeChars_line (pipes : Bool) :
    (l : List Char) → ∀ x ∈ escapeChars pipes l, x ≠ '\n' ∧ x ≠ '\r'
  | [], x, hx => by simp [escapeChars] at hx
  | c :: rest, x, hx => by
    have ih := escapeChars_line pipes rest x
    by_cases hn : c = '\n'
    · subst hn
      simp [escapeChars] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | hx
      all_goals first | decide | exact ih hx
    · by_cases hr : c = '\r'
      · subst hr
        simp [escapeChars] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | hx
        all_goals first | decide | exact ih hx
      · have hn' : (c == '\n') = false := by simpa using hn
        have hr' : (c == '\r') = false := by simpa using hr
        have hmem : x = '\\' ∨ x = c ∨ x ∈ escapeChars pipes rest := by
          unfold escapeChars at hx
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

/-- Is the rest of a line a space, a tab or nothing — what must follow a
list marker or an ATX opening sequence for it to open a block? -/
@[expose] public def spaceOrEnd : List Char → Bool
  | [] => true
  | x :: _ => x == ' ' || x == '\t'

/-- After an ATX heading's first `#`: up to five more, then a space, a tab
or the line's end (§4.2). -/
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

/-- After an ordered marker's first digit: more digits, then `.` or `)`,
then a space, a tab or the line's end (§5.2). -/
@[expose] public def orderedRest : List Char → Bool
  | [] => false
  | c :: rest =>
    if c.isDigit then orderedRest rest else (c == '.' || c == ')') && spaceOrEnd rest

/-- Does a line, read where markdown reads a paragraph's line — its start, or
a continuation after a hard break — open a block (CommonMark 0.31.2 §4–5)?
Leading indentation (up to an indented code block, §4.4), a block quote's
`>` (§5.1), an ATX opening sequence (§4.2), a bullet marker (§5.2), a
thematic break (§4.1), a setext underline (§4.3), a fence of three
tildes, or of three backticks whose info string holds none (§4.5), an
ordered marker (§5.2). An HTML block (§4.6)
is not modelled: the twin escapes every `<` its text holds, and the one it
writes bare opens an autolink, which is no tag. -/
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

/-- A paragraph line as the twin writes it: its leading spaces dropped, as
CommonMark drops them (§4.8), and, where it would open a block, its first
character escaped — for an ordered marker, its delimiter, since a backslash
before a digit is no escape (§2.4). A line that opens nothing is written
as it is: escaping an emphasis opener would make it literal. -/
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

/-- An ordered marker's tail reads through digits and stops at the escape:
a digit run, a backslash, anything — no marker. -/
private theorem orderedRest_escaped : (ds : List Char) → (∀ c ∈ ds, c.isDigit = true) →
    (m : List Char) → orderedRest (ds ++ '\\' :: m) = false
  | [], _, m => by simp [orderedRest]
  | d :: ds, h, m => by
    simp only [List.cons_append, orderedRest, h d (List.mem_cons_self ..), ite_true]
    exact orderedRest_escaped ds (fun c hc => h c (List.mem_cons_of_mem _ hc)) m

/-- A digit is none of the characters a block opens with. -/
private theorem digit_beq {c : Char} (hc : c.isDigit = true) (d : Char) (hd : d.isDigit = false) :
    (c == d) = false := by
  cases h : c == d
  · rfl
  · have : c = d := by simpa using h
    subst this
    rw [hc] at hd
    exact absurd hd (by decide)

/-- A line that opens with a backslash opens no block. -/
private theorem opensBlockChars_escaped (cs : List Char) : opensBlockChars ('\\' :: cs) = false := by
  simp [opensBlockChars]

/-- **No line the twin writes in a paragraph opens a block.** Whatever the
text, the line `escapeLineStart` makes of it starts no block under the
CommonMark model `opensBlock` declares — so a paragraph's text cannot become
a heading, a list, a quotation, a fence, a break or an underline when it is
read back. -/
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

/-! ### A pipe table's row

GFM's pipe table (§4.10) reads a row as cells split at each `|`, where a
`\|` pair — whatever stands before it — is the cell's own `|`, unescaped
before the cell's inline content is read, a code span's and a link
destination's included; each cell is then trimmed of the white space around
it. `gfmRow` is that reading, for a row written between a leading and a
trailing pipe: the shape the twin writes. The twin writes every pipe a cell
holds escaped (`rowLine`), so the row reads as exactly its cells
(`rowLine_cells_exact`), and a cell's text holds no line ending
(`cellText_contract`), so the row is one line (`rowLine_contract`). -/

/-- Every `|` escaped as `\|`. -/
@[expose] public def escapePipes : List Char → List Char
  | [] => []
  | c :: rest => if c == '|' then '\\' :: '|' :: escapePipes rest else c :: escapePipes rest

/-- A row read from inside a cell: the cell's text, then the cells after it.
`held` says the last character read was a backslash not yet written, which
a `|` makes the cell's own pipe, and anything else writes as it is. -/
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

/-- The white space GFM trims around a cell: space, tab, line endings,
vertical tab and form feed. -/
@[expose] public def gfmSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0B' || c == '\x0C'

/-- A cell's text without the white space around it. -/
@[expose] public def gfmTrim (cs : List Char) : List Char :=
  ((cs.dropWhile gfmSpace).reverse.dropWhile gfmSpace).reverse

/-- A row written between a leading and a trailing pipe, as GFM reads it:
the cells between the two, each trimmed. -/
@[expose] public def gfmRow (line : String) : List String :=
  let r := gfmSplit false line.toList
  ((r.1 :: r.2).drop 1).dropLast.map fun c => String.ofList (gfmTrim c)

/-- A row's cells after its leading pipe: each between a space on either
side, its pipes escaped, and closed by a pipe. -/
@[expose] public def rowCells : List String → List Char
  | [] => []
  | c :: cs => ' ' :: escapePipes c.toList ++ ' ' :: '|' :: rowCells cs

/-- A pipe table row, `| a | b |`. -/
@[expose] public def rowLine (cells : List String) : String :=
  String.ofList ('|' :: rowCells cells)

/-- A held backslash before anything but a pipe is written as it is. -/
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

/-- Escaping keeps a row's next character off a pipe. -/
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

/-- An escaped cell's text reads back as the text, and the row goes on. -/
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

/-- The cells after a row's leading pipe, each between its two spaces, and
the empty text after the closing pipe. -/
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

/-- The two spaces the twin sets around a cell are trimmed with the cell's
own. -/
private theorem gfmTrim_pad (cs : List Char) : gfmTrim (' ' :: (cs ++ [' '])) = gfmTrim cs := by
  unfold gfmTrim
  have hs : gfmSpace ' ' = true := rfl
  rw [List.dropWhile_cons_of_pos hs, List.dropWhile_append]
  split
  · next hd =>
    rw [List.isEmpty_iff] at hd
    simp [hd, hs]
  · simp [hs]

/-- **A row the twin writes reads as exactly its cells.** Under GFM's row
reading (`gfmRow`), the row `rowLine` writes splits into one cell per cell
written — no pipe a cell holds, in its text, a code span or a destination,
opens a cell — and each reads as the cell's own text, trimmed as GFM trims
every cell. -/
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

/-- Escaping a cell's pipes writes only its characters and backslashes. -/
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

/-- **A row writes only its cells' characters**, besides its pipes, the
backslashes escaping a cell's pipes and the spaces around each cell. -/
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

/-- **A row of one-line cells is one line**: it holds no line ending its
cells do not hold. -/
public theorem rowLine_contract (cells : List String)
    (h : ∀ c ∈ cells, ∀ x ∈ c.toList, x ≠ '\n' ∧ x ≠ '\r') :
    ∀ x ∈ (rowLine cells).toList, x ≠ '\n' ∧ x ≠ '\r' := by
  intro x hx
  rcases rowLine_mem cells x hx with rfl | rfl | rfl | ⟨c, hc, hxc⟩
  · decide
  · decide
  · decide
  · exact h c hc x hxc

/-- The longest run of `c` in `s`. -/
private def longestRun (c : Char) (s : String) : Nat :=
  (s.foldl (fun (best, cur) x => if x == c then (max best (cur + 1), cur + 1) else (best, 0))
    (0, 0)).1

/-- A code span holding `s` exactly (CommonMark §6.1): delimited by a
backtick run longer than any inside, and padded with one space where the
content opens or closes with a backtick, or opens and closes with a space
without being only spaces — the reader strips one such pair. Code span
content is not unescaped, so it is written as it is. -/
private def codeSpan (s : String) : String :=
  if s.isEmpty then "" else
  let ticks := String.ofList (List.replicate (longestRun '`' s + 1) '`')
  let pad := s.startsWith "`" || s.endsWith "`" ||
    (s.startsWith " " && s.endsWith " " && s.any (· != ' '))
  ticks ++ (if pad then " " ++ s ++ " " else s) ++ ticks

/-- A fence for `body`: three backticks, or one more than the longest run
inside — a closing fence is at least as long as its opening (§4.5). -/
private def fenceFor (body : String) : String :=
  String.ofList (List.replicate (max 3 (longestRun '`' body + 1)) '`')

/-- An absolute URI an autolink can carry (§6.4): a scheme of two to
thirty-two letters, digits, `+`, `.` or `-`, opening with a letter, then
`:`, and no space, `<`, `>` or control character after it. -/
private def autolinkable (url : String) : Bool :=
  match url.splitOn ":" with
  | scheme :: _ :: _ =>
    scheme.length ≥ 2 && scheme.length ≤ 32 &&
      (scheme.toList.head?.map Char.isAlpha).getD false &&
      scheme.all (fun c => c.isAlphanum || c == '+' || c == '.' || c == '-') &&
      url.all (fun c => c != ' ' && c != '<' && c != '>' && c.toNat ≥ 32)
  | _ => false

/-- A link's body as an autolink writes it: the destination as plain text,
in the link ink at most (`Styles.linkInk`). An autolink has no spelling
for a face, so a code-set URL (`\url`) stays a link whose text is code. -/
private def bareLink (url : String) (body : Array Inline) : Bool :=
  Ir.plainText body == url &&
    body.all fun x => x matches .text _ || x matches .colored _ _ #[.text _]

/-- A link destination as `[text](…)` reads it back (§6.3): angle-bracketed
where it holds a space, with `<` and `>` escaped; otherwise bare, with
parentheses and backslashes escaped. -/
private def linkDest (url : String) : String :=
  let esc (bad : Char → Bool) : String :=
    url.foldl (init := "") fun acc c => if bad c then (acc.push '\\').push c else acc.push c
  if url.any (fun c => c == ' ' || c == '<' || c == '>') then
    "<" ++ esc (fun c => c == '<' || c == '>' || c == '\\') ++ ">"
  else esc (fun c => c == '(' || c == ')' || c == '\\')

/-- A run's text split at its own leading and trailing spaces: a delimiter
beside a space neither opens nor closes (§6.2), so the spaces stand outside
the delimiters. -/
private def spaceSplit (s : String) : String × String × String :=
  let cs := s.toList
  let lead := cs.takeWhile (· == ' ')
  let rest := cs.drop lead.length
  let trail := rest.reverse.takeWhile (· == ' ')
  (String.ofList lead, String.ofList (rest.take (rest.length - trail.length)), String.ofList trail)

/-- Code-set content onto `acc`: one code span for each run between links,
and each link a link whose text is a code span. A code span holds no link —
its content is literal (§6.1) — so a link inside code-set text stands
outside its code, which keeps both its destination and its face. `run` is
the code-set content since the last link. -/
private def monoInto (acc : String) (run : Array Inline) : List Inline → String
  | [] =>
    let span := codeSpan (Ir.plainText run)
    acc ++ span
  | .link url body :: rest =>
    let span := codeSpan (Ir.plainText run)
    let text := codeSpan (Ir.plainText body)
    let dest := linkDest url
    monoInto (acc ++ span ++ "[" ++ text ++ "](" ++ dest ++ ")") #[] rest
  | x :: rest => monoInto acc (run.push x) rest

/-- The delimiter a style takes in markdown, where it has one. -/
private def styleMark : Style → Option String
  | .bold => some "**"
  | .italic => some "*"
  | .emph => some "*"
  | _ => none

/-- Where inline content is written. A paragraph's lines (`flow`) hold a
hard break as a backslash ending its line. A heading (`line`) and a pipe
table's cell (`cell`) are one line each: a hard break has no spelling there
and is written as a space, the break a loss, and a cell writes its text's
pipes bare, since its row escapes every pipe the cell holds (`rowLine`). -/
private inductive Site where
  | flow
  | line
  | cell
  deriving BEq

mutual

/-- Inline content onto `acc`. Meaning survives, decoration degrades: bold,
italic, and code have markdown spellings; colour, small caps, and underline
have none and render as their text. The accumulator threads through the
sibling walk, as everywhere (`#[x] ++ rest` copies). -/
private def inlineInto (site : Site) (acc : String) : Inline → String
  | .text s =>
    let escaped := escapeText (site != .cell) s
    acc ++ escaped
  | .math display src =>
    if display then acc ++ s!"$${src}$$" else acc ++ s!"${src}$"
  -- an elaborated formula's meaning lives in its atoms, but markdown's
  -- spelling of a formula IS the TeX source it carries
  | .formula display src _ =>
    if display then acc ++ s!"$${src}$$" else acc ++ s!"${src}$"
  -- the alt text rides as markdown's own image construct; the size
  -- request degrades like colour
  | .image src _ alt =>
    let shown := escapeText (site != .cell) alt.text
    let dest := linkDest src
    acc ++ "![" ++ shown ++ "](" ++ dest ++ ")"
  -- an icon's markdown spelling is its text alternative: prose keeps the
  -- meaning, the glyph is a web/print rendering
  | .icon _ label =>
    -- bound first: the append is one-off, not a walk (the cost gate's shape)
    let escaped := escapeText (site != .cell) label
    acc ++ escaped
  -- an anchor has no prose; a reference is worth what it resolved to
  | .label _ => acc
  | .ref _ _ text _ =>
    let escaped := escapeText (site != .cell) text
    acc ++ escaped
  | .styled st body =>
    match st with
    -- a code span's content is not unescaped: its text, as it is
    | .mono => monoInto acc #[] body.toList
    | _ =>
      let inner := inlinesInto site "" none body.toList
      match styleMark st with
      | some m =>
        let (lead, core, trail) := spaceSplit inner
        if core.isEmpty then acc ++ lead ++ trail else acc ++ lead ++ m ++ core ++ m ++ trail
      | none => acc ++ inner
  | .colored _ _ body => inlinesInto site acc none body.toList
  | .located _ body => inlinesInto site acc none body.toList
  -- the role's class is a web styling hook; prose keeps the words
  | .role _ body => inlinesInto site acc none body.toList
  | .link url body =>
    -- A link whose text is its plain destination is an autolink
    -- (`bareLink`); anything else writes its text and a destination that
    -- reads back exactly.
    if bareLink url body && autolinkable url then acc ++ "<" ++ url ++ ">"
    else
      let inner := inlinesInto site "" none body.toList
      let dest := linkDest url
      acc ++ "[" ++ inner ++ "](" ++ dest ++ ")"
  | .decorated _ body => inlinesInto site acc none body.toList
  | .onSteps _ body => inlinesInto site acc none body.toList
  | .altSteps _ active otherwise =>
    inlinesInto site (inlinesInto site acc none active.toList) none otherwise.toList
  -- `\hfill` separates a label from what it pushes to the far margin; text
  -- has no margin, so the separation renders as a spaced em dash. The space
  -- the author typed before it folds in rather than doubling.
  | .fill =>
    let acc := if acc.endsWith " " then (acc.dropEnd 1).toString else acc
    acc ++ " — "
  -- Horizontal glue separates prose when it has positive room or a local
  -- measure; a fill has the same prose separator as `\hfill`. A painted
  -- rule has no textual reading.
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
  -- a strut is metric, and text has no line box to prop open
  | .strut _ => acc
  -- an italic correction is a kern, and text has no glyph to correct
  | .italicCorr _ => acc
  -- an unresolved citation is worth its marks; the diagnostic that let it
  -- through already named the missing entry
  | .cite _ keys =>
    -- bound first: the append is one-off, not a walk (the cost gate's shape)
    let marks := Ir.citeMarks keys
    acc ++ marks
  -- The mark, CommonMark-extension footnote syntax: the body lands once,
  -- as the `[^k]: ...` definition after the document (`noteDefs`).
  | .footnote num _ => acc ++ s!"[^{num.getD 0}]"
  | .linebreak _ =>
    if site == .flow then acc ++ "\\\n"
    else if acc.endsWith " " then acc else acc ++ " "

/-- The sibling walk. Adjacent runs written with one delimiter are written
as one run — `**a****b**` reads back as neither two runs nor one — so a run
that follows a run of its own delimiter reopens it: the closing delimiter
written last comes off, and this run's opening one is not written. `prev`
is the delimiter the text written so far ends on, if it ends on a closing
one; a run's own spaces stand outside its delimiters (`spaceSplit`). -/
private def inlinesInto (site : Site) (acc : String) (prev : Option String := none) :
    List Inline → String
  | [] => acc
  | .styled st body :: rest =>
    match styleMark st with
    | some m =>
      let (lead, core, trail) := spaceSplit (inlinesInto site "" none body.toList)
      let ends := if trail.isEmpty then some m else none
      if core.isEmpty then
        inlinesInto site (acc ++ lead ++ trail) (if (lead ++ trail).isEmpty then prev else none) rest
      else if prev == some m then
        inlinesInto site ((acc.dropEnd m.length).toString ++ lead ++ core ++ m ++ trail) ends rest
      else inlinesInto site (acc ++ lead ++ m ++ core ++ m ++ trail) ends rest
    | none => inlinesInto site (inlineInto site acc (.styled st body)) none rest
  | x :: rest =>
    -- an inline that writes nothing (an italic correction, a label) leaves
    -- the run it follows open to the next
    let next := inlineInto site acc x
    inlinesInto site next (if next.utf8ByteSize == acc.utf8ByteSize then prev else none) rest

end

/-- A trailing `#` escaped, so a heading's text never reads as its closing
sequence (§4.2). -/
private def closeHash (s : String) : String :=
  match s.toList.reverse.dropWhile (fun c => c == ' ' || c == '\t') with
  | '#' :: rest => String.ofList (rest.reverse ++ ['\\', '#'])
  | _ => s

/-- The markdown spelling of inline content in a paragraph's flow, its
trailing `#` escaped (`closeHash`). -/
public def inlineText (xs : Array Inline) : String :=
  closeHash (inlinesInto .flow "" none xs.toList)

/-- Line endings as spaces: what stands on one line. A line ending a code
span holds reads as a space (§6.1), and one in a formula's source is TeX's
space. -/
private def oneLine (s : String) : String :=
  String.ofList (s.toList.map fun c => if c == '\n' || c == '\r' then ' ' else c)

/-- A heading's text: one line, its trailing `#` escaped. Public because the
placement theorems below quote it — the emitted title line is `# ` followed
by exactly this. -/
public def headingText (xs : Array Inline) : String :=
  closeHash (oneLine (inlinesInto .line "" none xs.toList))

/-- A pipe table cell's text as the cell reads: one line, its pipes bare —
the row escapes them (`rowLine`). -/
public def cellText (xs : Array Inline) : String :=
  oneLine (inlinesInto .cell "" none xs.toList)

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

/-- **A heading's text is one line**: whatever its content — a hard break,
a formula or code whose source spans lines — the heading the twin writes
holds no line ending, so it stands on its own line and reads back as one
heading. -/
public theorem headingText_contract (xs : Array Inline) :
    ∀ x ∈ (headingText xs).toList, x ≠ '\n' ∧ x ≠ '\r' := by
  intro x hx
  rcases closeHash_mem _ x hx with hx | rfl | rfl
  · exact oneLine_mem _ x hx
  · decide
  · decide

/-- **A cell's text is one line**: it holds no line ending, so the row that
holds it is one row (`rowLine_contract`). -/
public theorem cellText_contract (xs : Array Inline) :
    ∀ x ∈ (cellText xs).toList, x ≠ '\n' ∧ x ≠ '\r' :=
  oneLine_mem _

/-- The llms.txt title line's text: the metadata title written as a
heading's text — markup, raw HTML and character references read back as
the title's own characters — its trailing `#` its own (`closeHash`). -/
public def titleLine (t : String) : String := closeHash (escapeText true t)

/-- The llms.txt summary line's text inside its quotation: written as
text, and its start escaped so it opens no block there (`escapeLineStart`).
-/
public def summaryLine (s : String) : String := escapeLineStart (escapeText true s)

/-- Escaping a line's start writes only the line's characters and a
backslash. -/
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

/-- **The llms.txt head lines are lines**: whatever the metadata title and
summary hold, line endings included, each is written on one line. -/
public theorem titleLine_contract (t : String) :
    ∀ x ∈ (titleLine t).toList, x ≠ '\n' ∧ x ≠ '\r' := by
  intro x hx
  rcases closeHash_mem _ x hx with hx | rfl | rfl
  · exact escapeChars_line true t.toList x (by simpa [escapeText] using hx)
  · decide
  · decide

/-- The summary line is a line, as the title line is. -/
public theorem summaryLine_contract (s : String) :
    ∀ x ∈ (summaryLine s).toList, x ≠ '\n' ∧ x ≠ '\r' := by
  intro x hx
  rcases escapeLineStart_mem _ x hx with hx | rfl
  · exact escapeChars_line true s.toList x (by simpa [escapeText] using hx)
  · decide

/-- A paragraph's lines under their container: each line — the first, and
each after a hard break — escaped at its start (`escapeLineStart`) and set
under the container's prefix, so no line opens a block or falls out of the
container that holds it; the paragraph's trailing spaces, which a reader
drops, are not written. `first` prefixes the first line (a list item's
marker, or the container's prefix), `ind` every other. -/
private def paraText (first ind text : String) : String :=
  let text := String.ofList (text.toList.reverse.dropWhile (· == ' ')).reverse
  match text.splitOn "\n" with
  | [] => first
  | l :: ls =>
    ls.foldl (fun acc x => acc ++ "\n" ++ ind ++ escapeLineStart x) (first ++ escapeLineStart l)

/-- Two blank lines in a row: what the tightening folds into one. -/
private def blankRun : List String → Bool
  | a :: b :: rest => (a.isEmpty && b.isEmpty) || blankRun (b :: rest)
  | _ => false

/-- A fence's line prefix: its container's, which stands on every line —
and at the top level, where there is none, one space when the content holds
two blank lines in a row. The tightening keeps one blank line in a row, not
two, and CommonMark removes up to the fence's own indentation from each of
its lines (§4.5), so a fence opened one space in carries its blank lines as
lines the tightening keeps, and reads back with its content exact. -/
private def fenceIndent (ind : String) (lines : List String) : String :=
  if ind.isEmpty && blankRun lines then " " else ind

/-- A fenced block under its container: the fence, each line of `lines`
behind the container's prefix, the fence again. -/
private def fencedText (ind fence info : String) (lines : List String) : String :=
  lines.foldl (fun acc l => acc ++ ind ++ l ++ "\n") (ind ++ fence ++ info ++ "\n") ++
    ind ++ fence ++ "\n\n"

/-- The reference list's markdown spelling: one paragraph per entry, the
style's marker leading it — thebibliography's shape in prose. -/
private def bibItemsText (ind : String) (items : Array Ir.BibItem) : String := Id.run do
  let mut out := ""
  for item in items do
    let mark := match item.marker with
      | some m => s!"[{m}] "
      | none => ""
    out := out ++ paraText ind ind (mark ++ inlineText item.content) ++ "\n\n"
  return out

/-- The heading marker a section level takes: as many `#` as the shared
rank (`Ir.headingRank`, whose type bounds it to six), so the
marker and the HTML tag cannot drift; `heading_renderings_agree` in Tests
states the agreement over every level. -/
@[expose] public def headingMarker (level : Ir.HeadingLevel) : String :=
  String.ofList (List.replicate (Ir.headingRank level) '#')

/-- A block's text with its trailing blank lines off. -/
private def trimBlank (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (· == '\n')).reverse

/-- An item's first block, written under the content column, on the
marker's line: its trailing blank lines off, its first line moved up to the
marker `first`. -/
private def itemHead (first cont s : String) : String :=
  let s := trimBlank s
  if s.startsWith cont then first ++ (s.drop cont.length).toString
  else if s.isEmpty then first else first ++ "\n" ++ s

/-- Whether a list takes the other marker: when the text written so far
ends on a list of its kind that took the usual one. `prev` is the kind of
the list written last, with whether it took the other marker. -/
private def listAlt (prev : Option (Bool × Bool)) (ordered : Bool) : Bool :=
  match prev with
  | some (o, a) => o == ordered && !a
  | none => false

mutual

/-- Does the block's markdown open with a list? A list does, and so does a
block the twin writes as its body first — a role, a spacing scope, a
resolved step or backend conditional, an alignment, a block link, a
titleless frame or titled block, a float captioned below — whose first block
does. Every other block opens with its own line, or writes nothing. -/
private def leadsWithList : Block → Bool
  | .list _ _ => true
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
  | .frame title _ _ _ body => title.isEmpty && leadsWithListList body.toList
  | .float _ _ capAbove body caption =>
    (caption.isEmpty || !capAbove) && leadsWithListList body.toList
  | .columns cols => leadsWithListColumns cols.toList
  | .para _ => false
  | .equation _ _ => false
  | .section _ _ _ _ => false
  | .quote _ => false
  | .abstract _ => false
  | .verbatim _ _ _ => false
  | .algorithm _ _ _ => false
  | .table _ _ _ _ _ _ => false
  | .bibliography _ _ _ => false
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

/-- Where an item's writing stands: the text so far; the marker's line,
while no block has written anything to take it; and the list written last,
with whether it took the other marker, as `blocksInto` tracks it. -/
private structure ItemPen where
  acc : String
  first : Option String
  prev : Option (Bool × Bool)

/-- An item's block written: the first block that writes anything takes the
marker's line (`itemHead`); a later one stands on its own lines under the
content column, a blank line before it — a paragraph after a paragraph is a
second paragraph, not its continuation — unless it opens with a list, which
nests under what precedes it with none. Each block stands with its own
trailing blank lines off, so an item ends on its last line: a sibling marker
needs no blank line to open, and a blank line before it would make the list
loose. A block that writes nothing leaves the pen where it was. -/
private def itemPut (cont : String) (pen : ItemPen) (leadsList : Bool) (s : String) : ItemPen :=
  let s := trimBlank s
  if s.isEmpty then pen
  else match pen.first with
    | some first => { acc := pen.acc ++ itemHead first cont s ++ "\n", first := none, prev := none }
    | none => { pen with acc := pen.acc ++ (if leadsList then "" else "\n") ++ s ++ "\n", prev := none }

mutual

/-- One block onto `acc`. `ind` is the current line prefix (list nesting,
quotation), which every line of the block carries; `summary` is the
llms.txt summary blockquote, emitted immediately after the level-0 heading
when the body carries the document title — the summary's place is after
the title line, wherever that line comes from (`emit`). -/
private def blockInto (loc : Locale) (summary ind acc : String) : Block → String
  | .para xs => acc ++ paraText ind ind (inlineText xs) ++ "\n\n"
  -- the number rides beside the formula, as it does on the page
  | .equation num xs => acc ++ paraText ind ind (inlineText xs ++ " " ++ inlineText num) ++ "\n\n"
  | .section level _ num title =>
    -- The heading line carries its resolved number the way the page does;
    -- a level-0 heading (the document title) never has one.
    let numTxt := match num with
      | some n => n ++ " "
      | none => ""
    let head := acc ++ ind ++ headingMarker level ++ " " ++ numTxt ++ headingText title ++ "\n\n"
    if level == 0 then head ++ summary
    else head
  | .list ordered items =>
    let text := itemsInto loc summary ind ordered false 1 "" items.toList
    acc ++ text ++ "\n"
  | .center body => blocksInto loc summary ind acc none body.toList
  | .ragged _ body => blocksInto loc summary ind acc none body.toList
  -- Markdown's own quotation: every line of the body takes the `> `
  -- marker as part of its prefix, and the separator line between two
  -- quoted blocks keeps a bare `>` so the quotation stays one block
  -- (CommonMark §5.1: a blockquote does not span a blank line).
  | .quote body =>
    let inner := blocksInto loc summary (ind ++ "> ") "" none body.toList
    let trimmed := String.ofList (inner.toList.reverse.dropWhile (· == '\n')).reverse
    -- An empty quotation is its bare marker: written as nothing, it would
    -- not be there to read back.
    let joined := if trimmed.isEmpty then ind ++ ">"
      else String.intercalate ("\n" ++ ind ++ ">\n") (trimmed.splitOn "\n\n")
    acc ++ joined ++ "\n\n"
  | .spaced _ body => blocksInto loc summary ind acc none body.toList
  -- The class's own titled block: a heading line, then the body plain --
  -- the twin mirrors the HTML <section> with its heading, not the PDF's
  -- quotation margins, which are ink. "Abstract" is class furniture
  -- (article.cls's \abstractname), generated here as in both backends.
  | .abstract body =>
    blocksInto loc summary ind (acc ++ (ind ++ "## " ++ loc.abstract ++ "\n\n")) none body.toList
  -- The titled block mirrors the HTML <section> and its header: the
  -- title as its own bold paragraph, then the body plain.
  | .titled _ title body =>
    let head := if title.isEmpty then "" else
      paraText ind ind (inlineText #[.styled .bold title]) ++ "\n\n"
    blocksInto loc summary ind (acc ++ head) none body.toList
  -- the role's class is a web styling hook; the twin keeps the content
  | .role _ body => blocksInto loc summary ind acc none body.toList
  -- CommonMark has no block-link construct; the twin preserves the body.
  | .link _ body => blocksInto loc summary ind acc none body.toList
  | .verbatim _ s spec =>
    -- The numbered caption leads the fence, as the twin sets a float's
    -- caption; line numbers are page furniture a text stream cannot carry.
    -- The declared language is the fence's info string, read from the one
    -- IR projection the HTML class reads too (`listing_language_agree`).
    -- The fence outlasts any backtick run inside, and every line stands
    -- behind the container's prefix.
    let cap := match spec.caption with
      | some (n, c) => paraText ind ind (inlineText (Ir.listingCaption loc n c)) ++ "\n\n"
      | none => ""
    let lines := (verbatimLines s).toList
    acc ++ cap ++ fencedText (fenceIndent ind lines) (fenceFor s) spec.fenceInfo lines
  -- Pseudocode as a fence: each line with its generated keywords rendered
  -- to plain text (`AlgLine.rendered`, the site both artifact backends
  -- read too), depth as two spaces — code for a text twin, as verbatim.
  | .algorithm _ semis lines =>
    let words := Ir.algWords loc.tag
    let rendered := lines.toList.map fun l =>
      String.ofList (List.replicate (2 * l.depth) ' ') ++
        Ir.plainText (Ir.AlgLine.rendered words semis Ir.Color.black l)
    acc ++ fencedText (fenceIndent ind rendered) (fenceFor (String.join rendered)) "" rendered
  | .columns cols => columnsInto loc summary ind acc cols.toList
  | .onSteps _ body => blocksInto loc summary ind acc none body.toList
  | .altSteps _ active otherwise =>
    blocksInto loc summary ind (blocksInto loc summary ind acc none active.toList) none
      otherwise.toList
  -- `emit` already kept this node for markdown (`Ir.keepFor "md"`): by here
  -- it is a transparent group, as a resolved step is.
  | .only _ body => blocksInto loc summary ind acc none body.toList
  -- A nav is furniture, not content: the twin drops it — a menu printed
  -- as `[One](#one)` body text was the leak that forced backend wrappers.
  -- The HTML page keeps the landmark; the paged surface renders the
  -- unpinned form as the PDF outline.
  | .nav _ _ => acc
  -- A speaker note is a side channel in every backend; text is no exception.
  | .note _ => acc
  -- Frame-footer chrome is page furniture, as the running head is.
  | .framefoot _ => acc
  -- A stateful design declaration: the twin carries text, not styling.
  | .setPalette _ => acc
  | .setTokens _ => acc
  -- A continuous medium has no page to break.
  | .pagebreak => acc
  -- A logo is page furniture, scoped and replayed per page; a continuous
  -- text has no page corner to put it in.
  | .logo _ => acc
  -- A rule is decorative ink; it carries no text.
  | .rule _ _ _ => acc
  -- A picture is diagram ink; its labels are coordinates' text, not prose
  -- the twin can carry in reading order.
  | .picture _ => acc
  | .frame title _ _ _ body =>
    let head := if title.isEmpty then "" else ind ++ "## " ++ headingText title ++ "\n\n"
    blocksInto loc summary ind (acc ++ head) none body.toList
  -- Markdown's own table is the pipe table: one line per row, the GFM
  -- separator (which plays the head rule) after the first, alignment from
  -- the column spec. booktabs' rule weights have no markdown spelling.
  | .table cols _ _ rows _ _ =>
    let line (row : Array (Array Inline)) : String := rowLine (row.toList.map cellText)
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
  -- A float's caption is a paragraph beside its content, in source order,
  -- with the number prefix every backend spells from the one site.
  | .float kind num capAbove body caption =>
    let cap := if caption.isEmpty then ""
      else paraText ind ind (inlineText (Ir.numberedCaption loc kind num caption)) ++ "\n\n"
    if capAbove then blocksInto loc summary ind (acc ++ cap) none body.toList
    else blocksInto loc summary ind acc none body.toList ++ cap
  | .bibliography _ _ items =>
    let entries := bibItemsText ind items
    acc ++ entries
termination_by structural b => b

/-- A block sequence. Two lists of one kind side by side are two lists in
the IR, and markdown reads them as one unless their markers differ (§5.3),
so a list that follows a list of its kind takes the other marker: `prev`
is the kind of the list written last, with whether it took the other one. -/
private def blocksInto (loc : Locale) (summary ind acc : String)
    (prev : Option (Bool × Bool)) : List Block → String
  | [] => acc
  | .list ordered items :: rest =>
    let alt := listAlt prev ordered
    let text := itemsInto loc summary ind ordered alt 1 "" items.toList
    blocksInto loc summary ind (acc ++ text ++ "\n") (some (ordered, alt)) rest
  | b :: rest => blocksInto loc summary ind (blockInto loc summary ind acc b) none rest
termination_by structural bs => bs

private def columnsInto (loc : Locale) (summary ind acc : String) :
    List (BoxWidth × Array Block) → String
  | [] => acc
  | (_, body) :: rest => columnsInto loc summary ind (blocksInto loc summary ind acc none body.toList) rest
termination_by structural cols => cols

/-- List items: `- ` or `k. `, a first paragraph on the marker's line, and
every further line of the item indented by the marker's width — the
content column CommonMark reads a list item's continuation at (§5.2). An
item no block writes anything for is its marker alone. -/
private def itemsInto (loc : Locale) (summary ind : String) (ordered alt : Bool) (k : Nat)
    (acc : String) : List (Array Block) → String
  | [] => acc
  | item :: rest =>
    let marker := if ordered then s!"{k}{if alt then ")" else "."} " else if alt then "+ " else "- "
    let cont := ind ++ String.ofList (List.replicate marker.length ' ')
    let pen := itemSeq loc summary cont { acc, first := some (ind ++ marker), prev := none }
      item.toList
    let acc := match pen.first with
      | some m => pen.acc ++ m ++ "\n"
      | none => pen.acc
    itemsInto loc summary ind ordered alt (k + 1) acc rest
termination_by structural items => items

/-- An item's blocks, in order, from where the pen stands (`itemPut`). The
wrappers the twin writes as their bodies — a role, a spacing scope, a
backend conditional, a resolved step, an alignment, a block link, columns —
are opened rather than written, so their blocks stand at the item's own
level: a paragraph and the list nested under it keep no blank line between
them, as the tight item the IR holds is written. A list after a list of its
kind takes the other marker, as in a block sequence: the marker alone makes
it a list of its own (§5.3). -/
private def itemSeq (loc : Locale) (summary cont : String) (pen : ItemPen) :
    List Block → ItemPen
  | [] => pen
  | b :: rest =>
    -- `b` stays the list's own element in every arm, the argument the
    -- writer's structural recursion descends through
    let write (_ : Unit) := itemPut cont pen (leadsWithList b) (blockInto loc summary cont "" b)
    let pen := match (generalizing := false) b with
      | .list ordered items =>
        match pen.first with
        | some first =>
          -- the list as `blockInto` writes one, under the content column
          let head := itemHead first cont (itemsInto loc summary cont ordered false 1 "" items.toList)
          { acc := pen.acc ++ head ++ "\n", first := none, prev := some (ordered, false) }
        | none =>
          let alt := listAlt pen.prev ordered
          { pen with acc := pen.acc ++ itemsInto loc summary cont ordered alt 1 "" items.toList,
                     prev := some (ordered, alt) }
      | .role _ body => itemSeq loc summary cont pen body.toList
      | .spaced _ body => itemSeq loc summary cont pen body.toList
      | .only _ body => itemSeq loc summary cont pen body.toList
      | .onSteps _ body => itemSeq loc summary cont pen body.toList
      | .altSteps _ active otherwise =>
        itemSeq loc summary cont (itemSeq loc summary cont pen active.toList) otherwise.toList
      | .center body => itemSeq loc summary cont pen body.toList
      | .ragged _ body => itemSeq loc summary cont pen body.toList
      | .link _ body => itemSeq loc summary cont pen body.toList
      | .columns cols => itemColumns loc summary cont pen cols.toList
      | .para _ => write ()
      | .equation _ _ => write ()
      | .section _ _ _ _ => write ()
      | .quote _ => write ()
      | .abstract _ => write ()
      | .titled _ _ _ => write ()
      | .bibliography _ _ _ => write ()
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
    itemSeq loc summary cont pen rest
termination_by structural bs => bs

/-- Columns inside an item, opened as `columnsInto` writes them: each
column's blocks in turn. -/
private def itemColumns (loc : Locale) (summary cont : String) (pen : ItemPen) :
    List (BoxWidth × Array Block) → ItemPen
  | [] => pen
  | (_, body) :: rest =>
    itemColumns loc summary cont (itemSeq loc summary cont pen body.toList) rest
termination_by structural cols => cols

end

/-- The tightening walk, one character at a time: `nn` counts the newlines
the output currently ends with, and a newline past the second is dropped —
at most one blank line in a row. Kept characters cons onto `acc` in reverse
(the accumulator discipline for a `List` walk), so the trailing-blank trim
is the head `dropWhile` of this walk's own result. -/
private def tightenGo (nn : Nat) (acc : List Char) : List Char → List Char
  | [] => acc
  | c :: rest =>
    if c == '\n' then
      if nn ≥ 2 then tightenGo nn acc rest
      else tightenGo (nn + 1) (c :: acc) rest
    else tightenGo 0 (c :: acc) rest

/-- At most one blank line in a row, exactly one trailing newline: the block
emitters end with `\n\n` unconditionally, and adjacency decides the rest. -/
private def tighten (s : String) : String :=
  let trimmed := String.ofList ((tightenGo 0 [] s.toList).dropWhile (· == '\n')).reverse
  if trimmed.isEmpty then trimmed else trimmed ++ "\n"

/-- The twin's view of a document's body: its source locations erased, as
the HTML backend erases them before it writes (`Ir.eraseLocations`), so the
twin writes the IR both artifacts read; and backend conditionals resolved
for markdown (`Ir.keepFor`, whose `_covers` is why dropping cannot lose
content). -/
public def twinBody (doc : Doc) : Array Block := Ir.keepFor "md" (Ir.eraseLocations doc).body

/-- The `[^k]: …` definitions, one per footnote in flow order — the
markdown twin of the endnotes section, after the body. Empty when the
document has no notes, so an unnoted document emits exactly what it always
did. The locale is threaded for the day a definition needs furniture
words; today the syntax is the label. -/
private def noteDefs (_loc : Locale) (body : Array Block) : String := Id.run do
  let notes := Ir.footnotesOf body
  if notes.isEmpty then return ""
  let mut out := ""
  for (num, content) in notes do
    out := out ++ "\n" ++ paraText s!"[^{num.getD 0}]: " "    " (inlineText content) ++ "\n"
  return out

/-- Emit the document. Small caps land as their text with the authored
casing — since `\scshape` renders uniform small capitals, the source
carries the reading form and the twin is correct as typed (the retired
W0344 named the loss back when uniform required a lowercase workaround).
The metadata renders as the llms.txt preamble — the title as the one `#`
heading, the subject as the summary blockquote — and the summary's place
is fixed by the convention, not by its source: immediately after the title
line, wherever that line comes from. A body that carries its own level-0
heading (`\maketitle`) already states the title where it stands, so the
preamble yields to it — the body's heading is real content and wins, and
the walk sets the summary right after it. The placement theorems below pin
both title sources (`emit_meta_title_first`, `emit_body_title_first`); the
titleless remainder — summary first, nothing for it to follow — is pinned by
test. -/
public def emit (doc : Doc) : String :=
  -- The twin's view of the document, at the backend's entry (`twinBody`).
  let doc := { doc with body := twinBody doc }
  let summary := match doc.info.subject with
    | some s => "> " ++ summaryLine s ++ "\n\n"
    | none => ""
  let bodyTitled := (headingLevels doc.body).contains 0
  let title := match doc.info.title with
    | some t => if bodyTitled then "" else "# " ++ titleLine t ++ "\n\n"
    | none => ""
  let preamble := title ++ (if bodyTitled then "" else summary)
  tighten (preamble ++ blocksInto doc.info.locale summary "" "" none doc.body.toList)
    ++ noteDefs doc.info.locale doc.body

-- The definitions are data to the placement proofs, never proof material:
-- sealed so unification cannot whnf through the collection walk.
seal noteDefs

/-! ## The placement theorems

llms.txt (llmstxt.org) fixes the file's opening: `# title`, a `> summary`
blockquote, then sections. The defect these pin against: with the preamble
title suppressed (the body carries its own level-0 heading), the summary
was emitted *above* the body — `> summary` before `# title`. The invariant
is positional, not source-conditional: the summary stands immediately after
the title line, wherever that line comes from. Stated over `emit`, the
function the driver runs; the newline-free hypotheses name the shape a
metadata string must have to be a *line* at all. -/

private theorem append_nil (a : String) : ∃ r, a = a ++ r :=
  ⟨"", by simp⟩

private theorem append_chain₂ (a b c : String) : ∃ r, a ++ b ++ c = a ++ r :=
  ⟨b ++ c, by simp [String.append_assoc]⟩

private theorem append_chain₃ (a b c d : String) : ∃ r, a ++ b ++ c ++ d = a ++ r :=
  ⟨b ++ (c ++ d), by simp [String.append_assoc]⟩

private theorem append_chain₄ (a b c d e : String) :
    ∃ r, a ++ b ++ c ++ d ++ e = a ++ r :=
  ⟨b ++ (c ++ (d ++ e)), by simp [String.append_assoc]⟩

private theorem append_chain₅ (a b c d e f : String) :
    ∃ r, a ++ b ++ c ++ d ++ e ++ f = a ++ r :=
  ⟨b ++ (c ++ (d ++ (e ++ f))), by simp [String.append_assoc]⟩

private theorem append_chain₆ (a b c d e f g : String) :
    ∃ r, a ++ b ++ c ++ d ++ e ++ f ++ g = a ++ r :=
  ⟨b ++ (c ++ (d ++ (e ++ (f ++ g)))), by simp [String.append_assoc]⟩

private theorem append_chain₇ (a b c d e f g h : String) :
    ∃ r, a ++ b ++ c ++ d ++ e ++ f ++ g ++ h = a ++ r :=
  ⟨b ++ (c ++ (d ++ (e ++ (f ++ (g ++ h))))), by simp [String.append_assoc]⟩

private theorem append_chain₈ (a b c d e f g h i : String) :
    ∃ r, a ++ b ++ c ++ d ++ e ++ f ++ g ++ h ++ i = a ++ r :=
  ⟨b ++ (c ++ (d ++ (e ++ (f ++ (g ++ (h ++ i)))))), by simp [String.append_assoc]⟩

private theorem extends_trans₃ {f a b c d r : String}
    (h : f = a ++ b ++ c ++ d ++ r) : ∃ q, f = a ++ q :=
  ⟨b ++ (c ++ (d ++ r)), by rw [h]; simp [String.append_assoc]⟩

private theorem extends_comp {a g f : String} (h₁ : ∃ r, g = a ++ r)
    (h₂ : ∃ r, f = g ++ r) : ∃ q, f = a ++ q := by
  obtain ⟨r₁, h₁⟩ := h₁
  obtain ⟨r₂, h₂⟩ := h₂
  exact ⟨r₁ ++ r₂, by rw [h₂, h₁, String.append_assoc]⟩

mutual

/-- Every emitting walk extends its accumulator: the output is `acc` plus a
tail. The structural fact the placement theorems ride — whatever the rest of
the body emits lands after the title-and-summary head, never before it. -/
private theorem blockInto_extends (loc : Locale) (summary ind acc : String) :
    (b : Block) → ∃ r, blockInto loc summary ind acc b = acc ++ r
  | .para _ => by
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
  | .list _ _ => by
    simp only [blockInto]
    exact append_chain₂ _ _ _
  | .center body => blocksInto_extends loc summary ind acc none body.toList
  | .ragged _ body => blocksInto_extends loc summary ind acc none body.toList
  | .quote _ => by
    simp only [blockInto]
    exact append_chain₂ _ _ _
  | .abstract body =>
    extends_comp ⟨_, rfl⟩ (blocksInto_extends loc summary ind
      (acc ++ (ind ++ "## " ++ loc.abstract ++ "\n\n")) none body.toList)
  | .titled _ title body =>
    extends_comp ⟨_, rfl⟩ (blocksInto_extends loc summary ind
      (acc ++ if title.isEmpty then "" else
        paraText ind ind (inlineText #[.styled .bold title]) ++ "\n\n")
      none body.toList)
  | .spaced _ body => blocksInto_extends loc summary ind acc none body.toList
  | .bibliography _ _ items => ⟨bibItemsText ind items, rfl⟩
  | .role _ body => blocksInto_extends loc summary ind acc none body.toList
  | .link _ body => blocksInto_extends loc summary ind acc none body.toList
  | .verbatim _ _ _ => by
    simp only [blockInto]
    exact append_chain₂ _ _ _
  | .algorithm _ _ _ => ⟨_, rfl⟩
  | .columns cols => columnsInto_extends loc summary ind acc cols.toList
  | .onSteps _ body => blocksInto_extends loc summary ind acc none body.toList
  | .altSteps _ active otherwise =>
    extends_comp (blocksInto_extends loc summary ind acc none active.toList)
      (blocksInto_extends loc summary ind _ none otherwise.toList)
  | .only _ body => blocksInto_extends loc summary ind acc none body.toList
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
    extends_comp ⟨_, rfl⟩ (blocksInto_extends loc summary ind
      (acc ++ if title.isEmpty then "" else ind ++ "## " ++ headingText title ++ "\n\n")
      none body.toList)
  | .table _ _ _ rows _ _ => by
    simp only [blockInto]
    split
    · exact append_nil acc
    · exact append_chain₈ _ _ _ _ _ _ _ _ _
  | .float kind num capAbove body caption => by
    simp only [blockInto]
    split
    · exact extends_comp ⟨_, rfl⟩ (blocksInto_extends loc summary ind
        (acc ++ if caption.isEmpty then "" else
          paraText ind ind (inlineText (Ir.numberedCaption loc kind num caption)) ++ "\n\n")
        none body.toList)
    · exact extends_comp (blocksInto_extends loc summary ind acc none body.toList) ⟨_, rfl⟩

private theorem blocksInto_extends (loc : Locale) (summary ind acc : String)
    (prev : Option (Bool × Bool)) :
    (bs : List Block) → ∃ r, blocksInto loc summary ind acc prev bs = acc ++ r
  | [] => append_nil acc
  | .list _ _ :: rest => by
    simp only [blocksInto]
    exact extends_comp (append_chain₂ _ _ _) (blocksInto_extends loc summary ind _ _ rest)
  | b :: rest => by
    have hb := blockInto_extends loc summary ind acc b
    have hrest := fun acc' p => blocksInto_extends loc summary ind acc' p rest
    cases b with
    | list _ _ =>
      simp only [blocksInto]
      exact extends_comp (append_chain₂ _ _ _) (hrest _ _)
    | _ =>
      simp only [blocksInto]
      exact extends_comp hb (hrest _ _)

private theorem columnsInto_extends (loc : Locale) (summary ind acc : String) :
    (cols : List (BoxWidth × Array Block)) →
      ∃ r, columnsInto loc summary ind acc cols = acc ++ r
  | [] => append_nil acc
  | (_, body) :: rest =>
    extends_comp (blocksInto_extends loc summary ind acc none body.toList)
      (columnsInto_extends loc summary ind (blocksInto loc summary ind acc none body.toList) rest)

end

/-! ### `tighten` passes the head through

`tighten` folds the emitted stream character by character (`tightenGo`) and
then trims trailing blank lines. The facts below let the placement theorems
read the head of its output: a newline-free segment folds verbatim
(`tightenGo_flat`), a blank line folds verbatim from a fresh line
(`tightenGo_blank`), whatever the fold does later only ever appends
(`tightenGo_extends`) — so a head of the form `line, blank, line` survives
the fold, and the trailing trim stops at the head's last character
(`tighten_of_fold`). -/

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

/-- The head of a concatenation is in its nonempty left part. -/
private theorem head_mem_left {c : Char} : (xs : List Char) → xs ≠ [] →
    ∀ ys, (xs ++ ys).head? = some c → c ∈ xs
  | [], hne, _, _ => absurd rfl hne
  | x :: _, _, ys, h => by
    simp only [List.cons_append, List.head?_cons, Option.some.injEq] at h
    exact h ▸ List.mem_cons_self

/-- A fold that has produced `Qrev` (in reverse) under two blank-line
newlines survives the trailing trim whole, whatever else the fold added on
top: the trim eats newlines from the tail and stops at `Qrev`'s first
character — the head's *last* — which the hypothesis says is no newline. -/
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

/-- The llms.txt head survives `tighten`: the title line, one blank line,
and the summary line pass through the fold verbatim, and the trailing trim
cannot reach past the summary's last character. -/
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

/-! ### The placement, from either title source -/

mutual

/-- `headingLevels` only accumulates: what its seed carries, its result
carries. This is how the body's own level-0 heading is seen by the
preamble's suppression check, whatever follows it. -/
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
  | .list _ items, out, h => headingLevelItems_mem x items.toList out h
  | .center body, out, h => headingLevelList_mem x body.toList out h
  | .ragged _ body, out, h => headingLevelList_mem x body.toList out h
  | .quote body, out, h => headingLevelList_mem x body.toList out h
  | .abstract body, out, h => headingLevelList_mem x body.toList out h
  | .titled _ _ body, out, h => headingLevelList_mem x body.toList out h
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

/-- llms.txt (llmstxt.org): the twin opens `# title`, one blank line, then
the `> summary` blockquote. Title from the metadata — the body carries no
level-0 heading — so the preamble states both lines, in that order: the
summary can never precede the title line, and nothing the body emits can
move either. Each metadata string is written as text (`titleLine`,
`summaryLine`), a line whatever it holds. -/
public theorem emit_meta_title_first (doc : Doc) (t s : String)
    (ht : doc.info.title = some t) (hs : doc.info.subject = some s)
    (hbody : ((Ir.headingLevels (twinBody doc)).contains 0) = false) :
    ∃ q, emit doc = "# " ++ titleLine t ++ "\n\n" ++ "> " ++ summaryLine s ++ q := by
  obtain ⟨q, hq⟩ := tighten_head (titleLine t) (summaryLine s)
    (blocksInto doc.info.locale ("> " ++ summaryLine s ++ "\n\n") "" "" none
      (twinBody doc).toList)
    (fun c hc => (titleLine_contract t c hc).1) (fun c hc => (summaryLine_contract s c hc).1)
  refine ⟨q ++ noteDefs doc.info.locale (twinBody doc), ?_⟩
  simp only [emit, ht, hs, hbody]
  exact (congrArg (· ++ noteDefs doc.info.locale (twinBody doc)) hq).trans
    (String.append_assoc ..)

/-- Title from the body: when the twin's view of the body opens with its own
level-0 heading (`\maketitle`), the preamble yields — no second `#` line, no
summary above the body — and the summary lands immediately after the body's
title line, whatever the rest of the body emits and whether or not the
metadata also declares a title. This is the defect's contrapositive: the
summary follows the title, wherever the title came from. The title and the
summary are lines whatever they hold (`headingText_contract`,
`summaryLine_contract`). -/
public theorem emit_body_title_first (doc : Doc) (s : String) (st : Bool)
    (ttl : Array Inline) (rest : List Block)
    (hs : doc.info.subject = some s)
    (hbody : (twinBody doc).toList = .section 0 st none ttl :: rest) :
    ∃ q, emit doc = "# " ++ headingText ttl ++ "\n\n" ++ "> " ++ summaryLine s ++ q := by
  have h0 : (0 : Ir.HeadingLevel) ∈ Ir.headingLevels (twinBody doc) := by
    show (0 : Ir.HeadingLevel) ∈ Ir.headingLevelList #[] (twinBody doc).toList
    rw [hbody]
    exact headingLevelList_mem 0 rest _ (by
      show (0 : Ir.HeadingLevel) ∈ (#[] : Array Ir.HeadingLevel).push 0
      simp)
  have hbt : (Ir.headingLevels (twinBody doc)).contains 0 = true :=
    Array.contains_eq_true_of_mem h0
  have hfirst : blocksInto doc.info.locale ("> " ++ summaryLine s ++ "\n\n") "" "" none
      (twinBody doc).toList =
      blocksInto doc.info.locale ("> " ++ summaryLine s ++ "\n\n") ""
        ("# " ++ headingText ttl ++ "\n\n" ++ ("> " ++ summaryLine s ++ "\n\n")) none rest := by
    rw [hbody]
    simp [blocksInto, blockInto, headingMarker, Ir.headingRank]
  obtain ⟨w, hw⟩ := blocksInto_extends doc.info.locale ("> " ++ summaryLine s ++ "\n\n") ""
    ("# " ++ headingText ttl ++ "\n\n" ++ ("> " ++ summaryLine s ++ "\n\n")) none rest
  obtain ⟨q, hq⟩ := tighten_head (headingText ttl) (summaryLine s) w
    (fun c hc => (headingText_contract ttl c hc).1) (fun c hc => (summaryLine_contract s c hc).1)
  refine ⟨q ++ noteDefs doc.info.locale (twinBody doc), ?_⟩
  cases hT : doc.info.title with
  | some t =>
    simp only [emit, hs, hbt, hT, ite_true, String.empty_append]
    rw [hfirst, hw]
    exact (congrArg (· ++ noteDefs doc.info.locale (twinBody doc)) hq).trans
      (String.append_assoc ..)
  | none =>
    simp only [emit, hs, hbt, hT, ite_true, String.empty_append]
    rw [hfirst, hw]
    exact (congrArg (· ++ noteDefs doc.info.locale (twinBody doc)) hq).trans
      (String.append_assoc ..)

end LeanTex.Core.MarkdownDoc
