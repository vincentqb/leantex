module

public import LeanTex.Core.Ir

/-! The markdown backend: the llms.txt twin of the IR the HTML and PDF backends
read, written to read back as the same document. -/

namespace LeanTex.Core.MarkdownDoc

open LeanTex.Core LeanTex.Core.Ir

/-- Escapes the characters that would read as markup anywhere in a line. -/
private def escapeChars (pipes : Bool) : List Char → List Char
  | [] => []
  | c :: rest =>
    if c == '\\' || c == '`' || c == '*' || c == '_' || c == '[' || c == ']'
        || (pipes && c == '|') || c == '<' || c == '&' then
      '\\' :: c :: escapeChars pipes rest
    -- A line ending inside text has no other spelling.
    else if c == '\n' then '&' :: '#' :: '1' :: '0' :: ';' :: escapeChars pipes rest
    else if c == '\r' then '&' :: '#' :: '1' :: '3' :: ';' :: escapeChars pipes rest
    else c :: escapeChars pipes rest

private def escapeText (pipes : Bool) (s : String) : String :=
  String.ofList (escapeChars pipes s.toList)

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

/-- The longest run of `c` in `s`. -/
private def longestRun (c : Char) (s : String) : Nat :=
  (s.foldl (fun (best, cur) x => if x == c then (max best (cur + 1), cur + 1) else (best, 0))
    (0, 0)).1

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
    | c :: _ => mdWhite c || (c.toNat < 128 && !c.isAlphanum && c.toNat > 32)
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
    monoInto (acc ++ span ++ "[" ++ text ++ "](" ++ dest ++ ")") #[] rest
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

mutual

/-- Inline content onto `acc`: meaning survives, decoration degrades. -/
private def inlineInto (site : Site) (acc : String) (after : Bool := true) : Inline → String
  | .text s =>
    let escaped := escapeText (site != .cell) s
    acc ++ escaped
  | .math display src =>
    if display then acc ++ s!"$${src}$$" else acc ++ s!"${src}$"
  -- Markdown's spelling of a formula is the TeX source it carries.
  | .formula display src _ =>
    if display then acc ++ s!"$${src}$$" else acc ++ s!"${src}$"
  | .image src _ alt =>
    let shown := escapeText (site != .cell) alt.text
    let dest := linkDest src
    acc ++ "![" ++ shown ++ "](" ++ dest ++ ")"
  -- An icon's markdown spelling is its text alternative.
  | .icon _ label =>
    let escaped := escapeText (site != .cell) label
    acc ++ escaped
  -- An anchor is written as the empty target the markdown reader reads back.
  | .label key => acc ++ "<a name=\"" ++ Ir.labelAnchor key ++ "\"></a>"
  | .ref _ _ text _ =>
    let escaped := escapeText (site != .cell) text
    acc ++ escaped
  | .styled st body =>
    match st with
    | .mono => monoInto acc #[] body.toList
    | _ =>
      let inner := inlinesInto site "" none after body.toList
      match styleMark st with
      | some m =>
        let (lead, core, trail) := spaceSplit inner
        if core.isEmpty then acc ++ lead ++ trail else acc ++ lead ++ m ++ core ++ m ++ trail
      | none => acc ++ inner
  | .colored _ _ body => inlinesInto site acc none after body.toList
  | .located _ body => inlinesInto site acc none after body.toList
  | .role _ body => inlinesInto site acc none after body.toList
  | .link url body =>
    if bareLink url body && autolinkable url then acc ++ "<" ++ url ++ ">"
    else
      let inner := inlinesInto site "" none true body.toList
      let dest := linkDest url
      acc ++ "[" ++ inner ++ "](" ++ dest ++ ")"
  | .decorated _ body => inlinesInto site acc none after body.toList
  | .onSteps _ body => inlinesInto site acc none after body.toList
  | .altSteps _ active otherwise =>
    inlinesInto site (inlinesInto site acc none false active.toList) none after otherwise.toList
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
    acc ++ marks
  -- The mark in footnote syntax; the body is a `[^k]: ...` definition after the document.
  | .footnote num _ => acc ++ s!"[^{num.getD 0}]"
  | .linebreak _ =>
    if site == .flow then acc ++ "\\\n" else acc ++ "<br>"

/-- The sibling walk: a run following a run of its own delimiter reopens it. -/
private def inlinesInto (site : Site) (acc : String) (prev : Option String := none)
    (after : Bool := true) : List Inline → String
  | [] => acc
  | .styled st body :: rest =>
    match styleMark st with
    | some m =>
      let closes := closesAfterTag after rest
      let (lead, core, trail) := spaceSplit (inlinesInto site "" none closes body.toList)
      -- A paragraph's run keeps closing breaks inside as `<br>` where its closer still closes.
      let (lead, core, trail) := if site == .flow then
          match closingBreaks trail closes with
          | some brs => (lead, core ++ brs, "")
          | none => (lead, core, trail)
        else
          let (opening, core) := leadingTags core
          let (core, closing) := if closes then (core, "") else trailingTags core
          (lead ++ opening, core, closing ++ trail)
      let ends := if trail.isEmpty then some m else none
      if core.isEmpty then
        inlinesInto site (acc ++ lead ++ trail) (if (lead ++ trail).isEmpty then prev else none)
          after rest
      else if prev == some m then
        inlinesInto site ((acc.dropEnd m.length).toString ++ lead ++ core ++ m ++ trail) ends
          after rest
      else inlinesInto site (acc ++ lead ++ m ++ core ++ m ++ trail) ends after rest
    | none =>
      inlinesInto site (inlineInto site acc (closesAfterTag after rest) (.styled st body)) none
        after rest
  | x :: rest =>
    -- An inline that writes nothing leaves the run it follows open to the next.
    let next := inlineInto site acc (closesAfterTag after rest) x
    inlinesInto site next (if next.utf8ByteSize == acc.utf8ByteSize then prev else none) after
      rest

end

/-- A trailing `#` escaped, so a heading's text never reads
as its closing sequence (§4.2). -/
private def closeHash (s : String) : String :=
  match s.toList.reverse.dropWhile (fun c => c == ' ' || c == '\t') with
  | '#' :: rest => String.ofList (rest.reverse ++ ['\\', '#'])
  | _ => s

/-- The markdown spelling of inline content in a paragraph's flow. -/
public def inlineText (xs : Array Inline) : String :=
  closeHash (inlinesInto .flow "" none true xs.toList)

/-- Line endings as spaces. -/
private def oneLine (s : String) : String :=
  String.ofList (s.toList.map fun c => if c == '\n' || c == '\r' then ' ' else c)

/-- A heading's text: one line, its trailing `#` escaped. -/
public def headingText (xs : Array Inline) : String :=
  closeHash (oneLine (inlinesInto .line "" none true xs.toList))

/-- A pipe table cell's text: one line, its pipes bare. -/
public def cellText (xs : Array Inline) : String :=
  oneLine (inlinesInto .cell "" none true xs.toList)

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

public theorem headingText_contract (xs : Array Inline) :
    ∀ x ∈ (headingText xs).toList, x ≠ '\n' ∧ x ≠ '\r' := by
  intro x hx
  rcases closeHash_mem _ x hx with hx | rfl | rfl
  · exact oneLine_mem _ x hx
  · decide
  · decide

public theorem cellText_contract (xs : Array Inline) :
    ∀ x ∈ (cellText xs).toList, x ≠ '\n' ∧ x ≠ '\r' :=
  oneLine_mem _

/-- The llms.txt title line's text: the metadata title
written as a heading's text. -/
public def titleLine (t : String) : String := closeHash (escapeText true t)

/-- The llms.txt summary line's text inside its quotation. -/
public def summaryLine (s : String) : String := escapeLineStart (escapeText true s)

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

public theorem titleLine_contract (t : String) :
    ∀ x ∈ (titleLine t).toList, x ≠ '\n' ∧ x ≠ '\r' := by
  intro x hx
  rcases closeHash_mem _ x hx with hx | rfl | rfl
  · exact escapeChars_line true t.toList x (by simpa [escapeText] using hx)
  · decide
  · decide

public theorem summaryLine_contract (s : String) :
    ∀ x ∈ (summaryLine s).toList, x ≠ '\n' ∧ x ≠ '\r' := by
  intro x hx
  rcases escapeLineStart_mem _ x hx with hx | rfl
  · exact escapeChars_line true s.toList x (by simpa [escapeText] using hx)
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

/-- The reference list's markdown spelling: one paragraph
per entry, the style's marker leading it. -/
private def bibItemsText (ind : String) (items : Array Ir.BibItem) : String := Id.run do
  let mut out := ""
  for item in items do
    let mark := match item.marker with
      | some m => escapeText true s!"[{m}]" ++ " "
      | none => ""
    out := out ++ paraText ind ind (mark ++ inlineText item.content) ++ "\n\n"
  return out

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
  | .disclosure _ _ _ => false
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

mutual

/-- One block onto `acc`; `ind` is the line prefix every
line of the block carries. -/
private def blockInto (loc : Locale) (summary ind acc : String) : Block → String
  | .para xs => acc ++ paraText ind ind (inlineText xs) ++ "\n\n"
  -- the number rides beside the formula, as it does on the page
  | .equation num xs => acc ++ paraText ind ind (inlineText xs ++ " " ++ inlineText num) ++ "\n\n"
  | .section level _ num title =>
    -- The heading line carries its resolved number as the page does.
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
  -- Every quoted line takes the `> ` marker, a bare `>` between quoted blocks (§5.1).
  | .quote body =>
    let inner := blocksInto loc summary (ind ++ "> ") "" none body.toList
    let trimmed := String.ofList (inner.toList.reverse.dropWhile (· == '\n')).reverse
    -- An empty quotation is its bare marker.
    let joined := if trimmed.isEmpty then ind ++ ">"
      else String.intercalate ("\n" ++ ind ++ ">\n") (trimmed.splitOn "\n\n")
    acc ++ joined ++ "\n\n"
  | .spaced _ body => blocksInto loc summary ind acc none body.toList
  -- An abstract mirrors the HTML `<section>` with its heading.
  | .abstract body =>
    blocksInto loc summary ind (acc ++ (ind ++ "## " ++ loc.abstract ++ "\n\n")) none body.toList
  | .titled _ title body =>
    let head := if title.isEmpty then "" else
      paraText ind ind (inlineText #[.styled .bold title]) ++ "\n\n"
    blocksInto loc summary ind (acc ++ head) none body.toList
  -- The disclosure as the element its reader reads back.
  | .disclosure head expanded body =>
    let inner := blocksInto loc summary ind "" none body.toList
    let inner := if inner.endsWith "\n\n" then (inner.dropEnd 1).toString else inner
    acc ++ (ind ++ (if expanded then "<details open>" else "<details>") ++ "\n" ++
      ind ++ "<summary>" ++ summaryHtml head ++ "</summary>\n\n" ++ inner ++
      ind ++ "</details>\n\n")
  | .role _ body => blocksInto loc summary ind acc none body.toList
  -- CommonMark has no block-link construct; the body stays.
  | .link _ body => blocksInto loc summary ind acc none body.toList
  | .verbatim _ s spec =>
    -- The numbered caption leads the fence; the declared language is the fence's info string.
    let cap := match spec.caption with
      | some (n, c) => paraText ind ind (inlineText (Ir.listingCaption loc n c)) ++ "\n\n"
      | none => ""
    let lines := (verbatimLines s).toList
    acc ++ cap ++ fencedText (fenceIndent ind lines) (fenceFor s) spec.fenceInfo lines
  -- Pseudocode as a fence, each line's keywords as plain text.
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
  -- `emit` already kept this node for markdown.
  | .only _ body => blocksInto loc summary ind acc none body.toList
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
    let head := if title.isEmpty then "" else ind ++ "## " ++ headingText title ++ "\n\n"
    blocksInto loc summary ind (acc ++ head) none body.toList
  -- The GFM pipe table: one line per row, the separator after the first.
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
  -- A float's caption is a paragraph beside its content, in source order.
  | .float kind num capAbove body caption =>
    let cap := if caption.isEmpty then ""
      else paraText ind ind (inlineText (Ir.numberedCaption loc kind num caption)) ++ "\n\n"
    if capAbove then blocksInto loc summary ind (acc ++ cap) none body.toList
    else blocksInto loc summary ind acc none body.toList ++ cap
  | .bibliography _ _ items =>
    let entries := bibItemsText ind items
    acc ++ entries
termination_by structural b => b

/-- A block sequence; a list after a list of its kind takes
the other marker (§5.3). -/
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

/-- List items: `- ` or `k. `, every further line indented
to the content column (§5.2). -/
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

/-- An item's blocks, in order, from where the pen stands. -/
private def itemSeq (loc : Locale) (summary cont : String) (pen : ItemPen) :
    List Block → ItemPen
  | [] => pen
  | b :: rest =>
    let write (_ : Unit) := itemPut cont pen (leadsWithList b) (blockInto loc summary cont "" b)
    let pen := match (generalizing := false) b with
      | .list ordered items =>
        match pen.first with
        | some first =>
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
      | .disclosure _ _ _ => write ()
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

/-- Columns inside an item: each column's blocks in turn. -/
private def itemColumns (loc : Locale) (summary cont : String) (pen : ItemPen) :
    List (BoxWidth × Array Block) → ItemPen
  | [] => pen
  | (_, body) :: rest =>
    itemColumns loc summary cont (itemSeq loc summary cont pen body.toList) rest
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

/-- The twin's view of a document's body: source locations erased and backend
conditionals resolved for markdown. -/
public def twinBody (doc : Doc) : Array Block := Ir.keepFor "md" (Ir.eraseLocations doc).body

/-- The `[^k]: …` definitions, one per footnote in flow
order; empty without notes. -/
private def noteDefs (_loc : Locale) (body : Array Block) : String := Id.run do
  let notes := Ir.footnotesOf body
  if notes.isEmpty then return ""
  let mut out := ""
  for (num, content) in notes do
    out := out ++ "\n" ++ paraText s!"[^{num.getD 0}]: " "    " (inlineText content) ++ "\n"
  return out

/-- The document's markdown twin. -/
public def emit (doc : Doc) : String :=
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

-- Sealed so unification cannot unfold the collection walk.
seal noteDefs

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
  | .disclosure _ _ _ => ⟨_, rfl⟩
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
  | .list _ items, out, h => headingLevelItems_mem x items.toList out h
  | .center body, out, h => headingLevelList_mem x body.toList out h
  | .ragged _ body, out, h => headingLevelList_mem x body.toList out h
  | .quote body, out, h => headingLevelList_mem x body.toList out h
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

/-- llms.txt: with the title from the metadata, the twin opens `# title`, one
blank line, then the `> summary` blockquote. -/
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

/-- With the title from the body's own level-0 heading, the preamble yields and
the summary follows that heading. -/
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
