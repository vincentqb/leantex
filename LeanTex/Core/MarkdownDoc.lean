import LeanTex.Core.Ir

/-! The markdown backend. A web page today publishes a plain-text twin — the
llms.txt convention (llmstxt.org): `# title`, a `> summary`, then sections —
and the twin is only trustworthy if it comes from the same source as the
page. Here it is the same IR the HTML and PDF backends consume: the document
metadata renders as the llms.txt preamble (markdown has no `<head>`, so the
title and subject become the `#` line and the blockquote), and the body maps
structurally. Like every backend, this one consumes the IR and nothing else. -/

namespace LeanTex.Core.MarkdownDoc

open LeanTex.Core LeanTex.Core.Ir

/-- Escape the characters that would read as markup. `#` and `-` are left
alone: they mark up only at line starts, where the emitter itself decides
what a line starts with. -/
private def escapeText (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    if c == '\\' || c == '`' || c == '*' || c == '_' || c == '[' || c == ']' then
      (acc.push '\\').push c
    else acc.push c

mutual

/-- Inline content onto `acc`. Meaning survives, decoration degrades: bold,
italic, and code have markdown spellings; colour, small caps, and underline
have none and render as their text. The accumulator threads through the
sibling walk, as everywhere (`#[x] ++ rest` copies). -/
private def inlineInto (acc : String) : Inline → String
  | .text s =>
    let escaped := escapeText s
    acc ++ escaped
  | .math display src =>
    if display then acc ++ s!"$${src}$$" else acc ++ s!"${src}$"
  -- an elaborated formula's meaning lives in its atoms, but markdown's
  -- spelling of a formula IS the TeX source it carries
  | .formula display src _ =>
    if display then acc ++ s!"$${src}$$" else acc ++ s!"${src}$"
  -- the alt text rides as markdown's own image construct; the size
  -- request degrades like colour
  | .image src _ alt => acc ++ s!"![{alt}]({src})"
  -- an icon's markdown spelling is its text alternative: prose keeps the
  -- meaning, the glyph is a web/print rendering
  | .icon _ label =>
    -- bound first: the append is one-off, not a walk (the cost gate's shape)
    let escaped := escapeText label
    acc ++ escaped
  | .styled st body =>
    let inner := inlinesInto "" body.toList
    match st with
    | .bold => acc ++ s!"**{inner}**"
    | .italic => acc ++ s!"*{inner}*"
    | .emph => acc ++ s!"*{inner}*"
    | .mono => acc ++ s!"`{inner}`"
    | _ => acc ++ inner
  | .colored _ _ body => inlinesInto acc body.toList
  -- the role's class is a web styling hook; prose keeps the words
  | .role _ body => inlinesInto acc body.toList
  | .link url body =>
    let inner := inlinesInto "" body.toList
    -- A bare link prints its own URL; wrapping it as [url](url) says nothing.
    if inner == url then acc ++ url else acc ++ s!"[{inner}]({url})"
  | .underline body => inlinesInto acc body.toList
  | .step _ _ body => inlinesInto acc body.toList
  -- `\hfill` separates a label from what it pushes to the far margin; text
  -- has no margin, so the separation renders as a spaced em dash. The space
  -- the author typed before it folds in rather than doubling.
  | .fill =>
    let acc := if acc.endsWith " " then (acc.dropEnd 1).toString else acc
    acc ++ " — "
  | .pageNumber => acc
  | .pageCount => acc
  | .linebreak _ => acc ++ "\\\n"

private def inlinesInto (acc : String) : List Inline → String
  | [] => acc
  | x :: rest => inlinesInto (inlineInto acc x) rest

end

/-- The markdown spelling of inline content: what a heading or a cell sets.
Public because the placement theorems below quote it — the emitted title
line is `# ` followed by exactly this. -/
def inlineText (xs : Array Inline) : String :=
  inlinesInto "" xs.toList

/-- The heading marker a section level takes: `#` marks the level-0
document title, exactly as the HTML backend reserves `<h1>` for it, and
each deeper level adds one `#` (capped at `####`, the deepest level the
elaborator produces plus one). One fact, shared with the HTML backend's
tag; `heading_renderings_agree` in Tests pins the agreement. -/
def headingMarker (level : Nat) : String :=
  String.ofList (List.replicate (min (level + 1) 4) '#')

mutual

/-- One block onto `acc`. `ind` is the current line prefix (list nesting);
`summary` is the llms.txt summary blockquote, emitted immediately after the
level-0 heading when the body carries the document title — the summary's
place is after the title line, wherever that line comes from (`emit`). -/
private def blockInto (summary ind acc : String) : Block → String
  | .para xs => acc ++ ind ++ inlineText xs ++ "\n\n"
  | .section level _ title =>
    let head := acc ++ ind ++ headingMarker level ++ " " ++ inlineText title ++ "\n\n"
    if level == 0 then head ++ summary
    else head
  | .list ordered items => itemsInto summary ind ordered 1 acc items.toList ++ "\n"
  | .center body => blocksInto summary ind acc body.toList
  -- Markdown's own quotation: every line of the body takes the `> `
  -- marker as part of its prefix, and the separator line between two
  -- quoted blocks keeps a bare `>` so the quotation stays one block
  -- (CommonMark §5.1: a blockquote does not span a blank line).
  | .quote body =>
    let inner := blocksInto summary (ind ++ "> ") "" body.toList
    let trimmed := String.ofList (inner.toList.reverse.dropWhile (· == '\n')).reverse
    let joined := String.intercalate ("\n" ++ ind ++ ">\n") (trimmed.splitOn "\n\n")
    acc ++ joined ++ "\n\n"
  | .spaced _ body => blocksInto summary ind acc body.toList
  -- the role's class is a web styling hook; the twin keeps the content
  | .role _ body => blocksInto summary ind acc body.toList
  | .verbatim _ s =>
    let lines := String.intercalate "\n" (verbatimLines s).toList
    acc ++ "```\n" ++ lines ++ "\n```\n\n"
  | .columns cols => columnsInto summary ind acc cols.toList
  | .step _ _ body => blocksInto summary ind acc body.toList
  -- `emit` already kept this node for markdown (`Ir.keepFor "md"`): by here
  -- it is a transparent group, as a resolved step is.
  | .only _ body => blocksInto summary ind acc body.toList
  -- Markdown has no landmark; the navigation's content is content.
  | .nav _ body => blocksInto summary ind acc body.toList
  -- A speaker note is a side channel in every backend; text is no exception.
  | .note _ => acc
  -- Frame-footer chrome is page furniture, as the running head is.
  | .framefoot _ => acc
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
  | .frame title _ _ body =>
    let head := if title.isEmpty then "" else ind ++ "## " ++ inlineText title ++ "\n\n"
    blocksInto summary ind (acc ++ head) body.toList
  -- Markdown's own table is the pipe table: one line per row, the GFM
  -- separator (which plays the head rule) after the first, alignment from
  -- the column spec. booktabs' rule weights have no markdown spelling.
  | .table cols _ _ rows _ =>
    let line (row : Array (Array Inline)) : String :=
      "| " ++ String.intercalate " | " (row.toList.map inlineText) ++ " |"
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
  | .float _ capAbove body caption =>
    let cap := if caption.isEmpty then "" else ind ++ inlineText caption ++ "\n\n"
    if capAbove then blocksInto summary ind (acc ++ cap) body.toList
    else blocksInto summary ind acc body.toList ++ cap

private def blocksInto (summary ind acc : String) : List Block → String
  | [] => acc
  | b :: rest => blocksInto summary ind (blockInto summary ind acc b) rest

private def columnsInto (summary ind acc : String) :
    List (Option Nat × Array Block) → String
  | [] => acc
  | (_, body) :: rest => columnsInto summary ind (blocksInto summary ind acc body.toList) rest

/-- List items: `- ` or `k. `, a first paragraph on the marker's line,
anything further indented under it. -/
private def itemsInto (summary ind : String) (ordered : Bool) (k : Nat) (acc : String) :
    List (Array Block) → String
  | [] => acc
  | item :: rest =>
    let marker := if ordered then s!"{k}. " else "- "
    let acc := itemInto summary ind marker acc item.toList
    itemsInto summary ind ordered (k + 1) acc rest

private def itemInto (summary ind marker acc : String) : List Block → String
  | [] => acc ++ ind ++ marker ++ "\n"
  | b :: rest =>
    let acc := match b with
      | .para xs => acc ++ ind ++ marker ++ inlineText xs ++ "\n"
      | other => blockInto summary (ind ++ "  ") (acc ++ ind ++ marker ++ "\n") other
    blocksInto summary (ind ++ "  ") acc rest

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

mutual

/-- The small-caps runs this backend will set as plain text: the styled
text of every `.smallcaps` inline that ships through the twin, in document
order. Walked exactly over what emits — a speaker note or frame footer
never reaches the twin, so nothing is lost there. A casing chosen *for*
small caps (`phd`, set uniform by the face) survives into plain text as a
misreading, and the engine cannot restore the reading form — that is
authorial knowledge — so the loss is named (`emit`), never silent. The
accumulator threads through, as every walk here does. -/
private def scBlocks (acc : Array String) : List Block → Array String
  | [] => acc
  | b :: rest => scBlocks (scBlock acc b) rest

private def scBlock (acc : Array String) : Block → Array String
  | .para xs => scInlines acc xs.toList
  | .section _ _ title => scInlines acc title.toList
  | .list _ items => scItems acc items.toList
  | .center body => scBlocks acc body.toList
  | .quote body => scBlocks acc body.toList
  | .spaced _ body => scBlocks acc body.toList
  | .role _ body => scBlocks acc body.toList
  | .verbatim _ _ => acc
  | .columns cols => scColumns acc cols.toList
  | .step _ _ body => scBlocks acc body.toList
  | .only _ body => scBlocks acc body.toList
  | .nav _ body => scBlocks acc body.toList
  | .note _ => acc
  | .framefoot _ => acc
  | .pagebreak => acc
  | .logo _ => acc
  | .rule _ _ _ => acc
  | .picture _ => acc
  | .frame title _ _ body => scBlocks (scInlines acc title.toList) body.toList
  | .table _ _ _ rows _ => scRows acc rows.toList
  | .float _ _ body caption => scBlocks (scInlines acc caption.toList) body.toList

private def scItems (acc : Array String) : List (Array Block) → Array String
  | [] => acc
  | item :: rest => scItems (scBlocks acc item.toList) rest

private def scColumns (acc : Array String) : List (Option Nat × Array Block) → Array String
  | [] => acc
  | (_, body) :: rest => scColumns (scBlocks acc body.toList) rest

private def scRows (acc : Array String) : List (Array (Array Inline)) → Array String
  | [] => acc
  | row :: rest => scRows (scCells acc row.toList) rest

private def scCells (acc : Array String) : List (Array Inline) → Array String
  | [] => acc
  | cell :: rest => scCells (scInlines acc cell.toList) rest

private def scInlines (acc : Array String) : List Inline → Array String
  | [] => acc
  | x :: rest => scInlines (scInline acc x) rest

private def scInline (acc : Array String) : Inline → Array String
  | .styled st body =>
    if st == .smallcaps then
      let text := plainText body
      if text.isEmpty then acc else acc.push text
    else scInlines acc body.toList
  | .colored _ _ body => scInlines acc body.toList
  | .role _ body => scInlines acc body.toList
  | .link _ body => scInlines acc body.toList
  | .underline body => scInlines acc body.toList
  | .step _ _ body => scInlines acc body.toList
  | .text _ => acc
  | .math _ _ => acc
  | .formula _ _ _ => acc
  | .image _ _ _ => acc
  | .icon _ _ => acc
  | .fill => acc
  | .pageNumber => acc
  | .pageCount => acc
  | .linebreak _ => acc

end

/-- The one diagnostic this backend raises: small caps have no markdown
spelling, so their text lands as typed — and a casing the author chose for
uniform small capitals (`{\scshape phd}`) reads as a misspelling in plain
text. Named once per document, quoting the first affected run. -/
private def smallCapsDiag (body : Array Block) : Array Diag :=
  let runs := scBlocks #[] body.toList
  match runs[0]? with
  | none => #[]
  | some first =>
    let short := if first.length > 24 then (first.take 23).toString ++ "…" else first
    let msg := if runs.size == 1 then
        "small caps have no markdown spelling; '" ++ short ++ "' is set as typed"
      else
        "small caps have no markdown spelling; '" ++ short ++ "' and " ++
          toString (runs.size - 1) ++
          (if runs.size == 2 then " more run are set as typed"
           else " more runs are set as typed")
    #[Diag.of .W0344 msg
      (help := some "markdown keeps the letters as typed: write the casing \
prose should read, or \\allow{W0344} accepts the loss")]

/-- Emit the document, and the diagnostics this backend itself raises. The
metadata renders as the llms.txt preamble — the title as the one `#`
heading, the subject as the summary blockquote — and the summary's place
is fixed by the convention, not by its source: immediately after the title
line, wherever that line comes from. A body that carries its own level-0
heading (`\maketitle`) already states the title where it stands, so the
preamble yields to it — the body's heading is real content and wins, and
the walk sets the summary right after it. The placement theorems below pin
both title sources (`emit_meta_title_first`, `emit_body_title_first`); the
titleless remainder — summary first, nothing for it to follow — is pinned by
test. -/
def emit (doc : Doc) : String × Array Diag :=
  -- The twin's view of the document: backend conditionals resolve here, at
  -- the backend's entry (`Ir.keepFor_covers` is why dropping cannot lose
  -- content).
  let doc := { doc with body := Ir.keepFor "md" doc.body }
  let summary := match doc.info.subject with
    | some s => "> " ++ s ++ "\n\n"
    | none => ""
  let bodyTitled := (headingLevels doc.body).contains 0
  let title := match doc.info.title with
    | some t => if bodyTitled then "" else "# " ++ t ++ "\n\n"
    | none => ""
  let preamble := title ++ (if bodyTitled then "" else summary)
  (tighten (preamble ++ blocksInto summary "" "" doc.body.toList),
    smallCapsDiag doc.body)

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
private theorem blockInto_extends (summary ind acc : String) :
    (b : Block) → ∃ r, blockInto summary ind acc b = acc ++ r
  | .para _ => by
    simp only [blockInto]
    exact append_chain₃ _ _ _ _
  | .section _ _ _ => by
    simp only [blockInto]
    split
    · exact append_chain₆ _ _ _ _ _ _ _
    · exact append_chain₅ _ _ _ _ _ _
  | .list _ items =>
    extends_comp (itemsInto_extends summary ind _ 1 acc items.toList) ⟨"\n", rfl⟩
  | .center body => blocksInto_extends summary ind acc body.toList
  | .quote _ => by
    simp only [blockInto]
    exact append_chain₂ _ _ _
  | .spaced _ body => blocksInto_extends summary ind acc body.toList
  | .role _ body => blocksInto_extends summary ind acc body.toList
  | .verbatim _ _ => by
    simp only [blockInto]
    exact append_chain₃ _ _ _ _
  | .columns cols => columnsInto_extends summary ind acc cols.toList
  | .step _ _ body => blocksInto_extends summary ind acc body.toList
  | .only _ body => blocksInto_extends summary ind acc body.toList
  | .nav _ body => blocksInto_extends summary ind acc body.toList
  | .note _ => append_nil acc
  | .framefoot _ => append_nil acc
  | .pagebreak => append_nil acc
  | .logo _ => append_nil acc
  | .rule _ _ _ => append_nil acc
  | .picture _ => append_nil acc
  | .frame title _ _ body =>
    extends_comp ⟨_, rfl⟩ (blocksInto_extends summary ind
      (acc ++ if title.isEmpty then "" else ind ++ "## " ++ inlineText title ++ "\n\n")
      body.toList)
  | .table _ _ _ rows _ => by
    simp only [blockInto]
    split
    · exact append_nil acc
    · exact append_chain₈ _ _ _ _ _ _ _ _ _
  | .float _ capAbove body caption => by
    simp only [blockInto]
    split
    · exact extends_comp ⟨_, rfl⟩ (blocksInto_extends summary ind
        (acc ++ if caption.isEmpty then "" else ind ++ inlineText caption ++ "\n\n")
        body.toList)
    · exact extends_comp (blocksInto_extends summary ind acc body.toList) ⟨_, rfl⟩

private theorem blocksInto_extends (summary ind acc : String) :
    (bs : List Block) → ∃ r, blocksInto summary ind acc bs = acc ++ r
  | [] => append_nil acc
  | b :: rest =>
    extends_comp (blockInto_extends summary ind acc b)
      (blocksInto_extends summary ind (blockInto summary ind acc b) rest)

private theorem columnsInto_extends (summary ind acc : String) :
    (cols : List (Option Nat × Array Block)) →
      ∃ r, columnsInto summary ind acc cols = acc ++ r
  | [] => append_nil acc
  | (_, body) :: rest =>
    extends_comp (blocksInto_extends summary ind acc body.toList)
      (columnsInto_extends summary ind (blocksInto summary ind acc body.toList) rest)

private theorem itemsInto_extends (summary ind : String) (ordered : Bool) (k : Nat)
    (acc : String) :
    (items : List (Array Block)) →
      ∃ r, itemsInto summary ind ordered k acc items = acc ++ r
  | [] => append_nil acc
  | item :: rest =>
    extends_comp
      (itemInto_extends summary ind (if ordered then s!"{k}. " else "- ") acc
        item.toList)
      (itemsInto_extends summary ind ordered (k + 1)
        (itemInto summary ind (if ordered then s!"{k}. " else "- ") acc item.toList)
        rest)

private theorem itemInto_extends (summary ind marker acc : String) :
    (bs : List Block) → ∃ r, itemInto summary ind marker acc bs = acc ++ r
  | [] => append_chain₃ acc ind marker "\n"
  | b :: rest => by
    obtain ⟨rb, hb⟩ := blockInto_extends summary (ind ++ "  ")
      (acc ++ ind ++ marker ++ "\n") b
    have hblocks : ∀ g, ∃ r, blocksInto summary (ind ++ "  ") g rest = g ++ r :=
      fun g => blocksInto_extends summary (ind ++ "  ") g rest
    cases b
    case para xs =>
      exact extends_comp (append_chain₄ acc ind marker (inlineText xs) "\n")
        (hblocks (acc ++ ind ++ marker ++ inlineText xs ++ "\n"))
    all_goals exact extends_comp (extends_trans₃ hb) (hblocks _)

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
private theorem headingLevelList_mem (x : Nat) :
    (l : List Block) → (out : Array Nat) → x ∈ out → x ∈ Ir.headingLevelList out l
  | [], _, h => h
  | b :: rest, out, h =>
    headingLevelList_mem x rest (Ir.headingLevelOne out b)
      (headingLevelOne_mem x b out h)

private theorem headingLevelOne_mem (x : Nat) :
    (b : Block) → (out : Array Nat) → x ∈ out → x ∈ Ir.headingLevelOne out b
  | .section _ _ _, _, h => Array.mem_push_of_mem _ h
  | .para _, _, h => h
  | .list _ items, out, h => headingLevelItems_mem x items.toList out h
  | .center body, out, h => headingLevelList_mem x body.toList out h
  | .quote body, out, h => headingLevelList_mem x body.toList out h
  | .role _ body, out, h => headingLevelList_mem x body.toList out h
  | .spaced _ body, out, h => headingLevelList_mem x body.toList out h
  | .columns cols, out, h => headingLevelColumns_mem x cols.toList out h
  | .step _ _ body, out, h => headingLevelList_mem x body.toList out h
  | .only _ body, out, h => headingLevelList_mem x body.toList out h
  | .nav _ body, out, h => headingLevelList_mem x body.toList out h
  | .frame _ _ _ body, out, h => headingLevelList_mem x body.toList out h
  | .note _, _, h => h
  | .verbatim _ _, _, h => h
  | .framefoot _, _, h => h
  | .pagebreak, _, h => h
  | .logo _, _, h => h
  | .rule _ _ _, _, h => h
  | .picture _, _, h => h
  | .table _ _ _ _ _, _, h => h
  | .float _ _ body _, out, h => headingLevelList_mem x body.toList out h

private theorem headingLevelItems_mem (x : Nat) :
    (items : List (Array Block)) → (out : Array Nat) → x ∈ out →
      x ∈ Ir.headingLevelItems out items
  | [], _, h => h
  | item :: rest, out, h =>
    headingLevelItems_mem x rest (Ir.headingLevelList out item.toList)
      (headingLevelList_mem x item.toList out h)

private theorem headingLevelColumns_mem (x : Nat) :
    (cols : List (Option Nat × Array Block)) → (out : Array Nat) → x ∈ out →
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
move either. The newline-free hypotheses say the metadata strings are
lines. -/
theorem emit_meta_title_first (doc : Doc) (t s : String)
    (ht : doc.info.title = some t) (hs : doc.info.subject = some s)
    (hbody : ((Ir.headingLevels (Ir.keepFor "md" doc.body)).contains 0) = false)
    (htn : ∀ c ∈ t.toList, c ≠ '\n') (hsn : ∀ c ∈ s.toList, c ≠ '\n') :
    ∃ q, (emit doc).1 = "# " ++ t ++ "\n\n" ++ "> " ++ s ++ q := by
  obtain ⟨q, hq⟩ := tighten_head t s
    (blocksInto ("> " ++ s ++ "\n\n") "" "" (Ir.keepFor "md" doc.body).toList)
    htn hsn
  refine ⟨q, ?_⟩
  simp only [emit, ht, hs, hbody]
  exact hq

/-- Title from the body: when the twin's view of the body opens with its own
level-0 heading (`\maketitle`), the preamble yields — no second `#` line, no
summary above the body — and the summary lands immediately after the body's
title line, whatever the rest of the body emits and whether or not the
metadata also declares a title. This is the defect's contrapositive: the
summary follows the title, wherever the title came from. -/
theorem emit_body_title_first (doc : Doc) (s : String) (st : Bool)
    (ttl : Array Inline) (rest : List Block)
    (hs : doc.info.subject = some s)
    (hbody : (Ir.keepFor "md" doc.body).toList = .section 0 st ttl :: rest)
    (htn : ∀ c ∈ (inlineText ttl).toList, c ≠ '\n')
    (hsn : ∀ c ∈ s.toList, c ≠ '\n') :
    ∃ q, (emit doc).1 = "# " ++ inlineText ttl ++ "\n\n" ++ "> " ++ s ++ q := by
  have h0 : (0 : Nat) ∈ Ir.headingLevels (Ir.keepFor "md" doc.body) := by
    show (0 : Nat) ∈ Ir.headingLevelList #[] (Ir.keepFor "md" doc.body).toList
    rw [hbody]
    exact headingLevelList_mem 0 rest _ (by
      show (0 : Nat) ∈ (#[] : Array Nat).push 0
      simp)
  have hbt : (Ir.headingLevels (Ir.keepFor "md" doc.body)).contains 0 = true :=
    Array.contains_eq_true_of_mem h0
  have hfirst : blocksInto ("> " ++ s ++ "\n\n") "" ""
      (Ir.keepFor "md" doc.body).toList =
      blocksInto ("> " ++ s ++ "\n\n") ""
        ("# " ++ inlineText ttl ++ "\n\n" ++ ("> " ++ s ++ "\n\n")) rest := by
    rw [hbody]
    exact rfl
  obtain ⟨w, hw⟩ := blocksInto_extends ("> " ++ s ++ "\n\n") ""
    ("# " ++ inlineText ttl ++ "\n\n" ++ ("> " ++ s ++ "\n\n")) rest
  obtain ⟨q, hq⟩ := tighten_head (inlineText ttl) s w htn hsn
  refine ⟨q, ?_⟩
  cases hT : doc.info.title with
  | some t =>
    simp only [emit, hs, hbt, hT, ite_true, String.empty_append]
    rw [hfirst, hw]
    exact hq
  | none =>
    simp only [emit, hs, hbt, hT, ite_true, String.empty_append]
    rw [hfirst, hw]
    exact hq

end LeanTex.Core.MarkdownDoc
