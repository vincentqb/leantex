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
  | .styled st body =>
    let inner := inlinesInto "" body.toList
    match st with
    | .bold => acc ++ s!"**{inner}**"
    | .italic => acc ++ s!"*{inner}*"
    | .emph => acc ++ s!"*{inner}*"
    | .mono => acc ++ s!"`{inner}`"
    | _ => acc ++ inner
  | .colored _ _ body => inlinesInto acc body.toList
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

private def inlineText (xs : Array Inline) : String :=
  inlinesInto "" xs.toList

/-- The heading marker a section level takes: `#` marks the level-0
document title, exactly as the HTML backend reserves `<h1>` for it, and
each deeper level adds one `#` (capped at `####`, the deepest level the
elaborator produces plus one). One fact, shared with the HTML backend's
tag; `heading_renderings_agree` in Tests pins the agreement. -/
def headingMarker (level : Nat) : String :=
  String.ofList (List.replicate (min (level + 1) 4) '#')

mutual

/-- One block onto `acc`. `ind` is the current line prefix (list nesting). -/
private def blockInto (ind acc : String) : Block → String
  | .para xs => acc ++ ind ++ inlineText xs ++ "\n\n"
  | .section level _ title =>
    acc ++ ind ++ headingMarker level ++ " " ++ inlineText title ++ "\n\n"
  | .list ordered items => itemsInto ind ordered 1 acc items.toList ++ "\n"
  | .center body => blocksInto ind acc body.toList
  -- Markdown's own quotation: every line of the body takes the `> `
  -- marker as part of its prefix, and the separator line between two
  -- quoted blocks keeps a bare `>` so the quotation stays one block
  -- (CommonMark §5.1: a blockquote does not span a blank line).
  | .quote body =>
    let inner := blocksInto (ind ++ "> ") "" body.toList
    let trimmed := String.ofList (inner.toList.reverse.dropWhile (· == '\n')).reverse
    let joined := String.intercalate ("\n" ++ ind ++ ">\n") (trimmed.splitOn "\n\n")
    acc ++ joined ++ "\n\n"
  | .spaced _ body => blocksInto ind acc body.toList
  | .verbatim _ s =>
    let lines := String.intercalate "\n" (verbatimLines s).toList
    acc ++ "```\n" ++ lines ++ "\n```\n\n"
  | .columns cols => columnsInto ind acc cols.toList
  | .step _ _ body => blocksInto ind acc body.toList
  -- A speaker note is a side channel in every backend; text is no exception.
  | .note _ => acc
  -- Frame-footer chrome is page furniture, as the running head is.
  | .framefoot _ => acc
  -- A logo is page furniture, scoped and replayed per page; a continuous
  -- text has no page corner to put it in.
  | .logo _ => acc
  -- A rule is decorative ink; it carries no text.
  | .rule _ _ _ => acc
  | .frame title _ _ body =>
    let head := if title.isEmpty then "" else ind ++ "## " ++ inlineText title ++ "\n\n"
    blocksInto ind (acc ++ head) body.toList

private def blocksInto (ind acc : String) : List Block → String
  | [] => acc
  | b :: rest => blocksInto ind (blockInto ind acc b) rest

private def columnsInto (ind acc : String) : List (Option Nat × Array Block) → String
  | [] => acc
  | (_, body) :: rest => columnsInto ind (blocksInto ind acc body.toList) rest

/-- List items: `- ` or `k. `, a first paragraph on the marker's line,
anything further indented under it. -/
private def itemsInto (ind : String) (ordered : Bool) (k : Nat) (acc : String) :
    List (Array Block) → String
  | [] => acc
  | item :: rest =>
    let marker := if ordered then s!"{k}. " else "- "
    let acc := itemInto ind marker acc item.toList
    itemsInto ind ordered (k + 1) acc rest

private def itemInto (ind marker acc : String) : List Block → String
  | [] => acc ++ ind ++ marker ++ "\n"
  | b :: rest =>
    let acc := match b with
      | .para xs => acc ++ ind ++ marker ++ inlineText xs ++ "\n"
      | other => blockInto (ind ++ "  ") (acc ++ ind ++ marker ++ "\n") other
    blocksInto (ind ++ "  ") acc rest

end

/-- At most one blank line in a row, exactly one trailing newline: the block
emitters end with `\n\n` unconditionally, and adjacency decides the rest. -/
private def tighten (s : String) : String :=
  let folded := s.foldl (init := "") fun acc c =>
    if c == '\n' && acc.endsWith "\n\n" then acc else acc.push c
  let trimmed := String.ofList (folded.toList.reverse.dropWhile (· == '\n')).reverse
  if trimmed.isEmpty then trimmed else trimmed ++ "\n"

/-- Emit the document. The metadata renders as the llms.txt preamble: the
title as the one `#` heading, the subject as the summary blockquote. A
body that carries its own level-0 heading (`\maketitle`) already states
the title where it stands, so the preamble line would double it — the
body's heading is real content and wins. -/
def emit (doc : Doc) : String :=
  let title := match doc.info.title with
    | some t =>
      if (headingLevels doc.body).contains 0 then "" else s!"# {t}\n\n"
    | none => ""
  let summary := match doc.info.subject with
    | some s => s!"> {s}\n\n"
    | none => ""
  tighten (title ++ summary ++ blocksInto "" "" doc.body.toList)

end LeanTex.Core.MarkdownDoc
