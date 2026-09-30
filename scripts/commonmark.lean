/-
The CommonMark classifier: what this engine's markdown dialect does with
every one of the 652 spec examples. Run from the repository root after
`lake build`:

  lake env lean --run scripts/commonmark.lean              regenerate the verdicts and the tier, then check
  lake env lean --run scripts/commonmark.lean --check      check the committed verdicts and tier only
  lake env lean --run scripts/commonmark.lean --selftest   the reader, the comparison and the ratchet, on hand-written inputs

**A classifier, not a gate.** Every case carries a committed verdict and an
unclassified deviation fails. Four verdicts:

* `match` — the tree the engine emits equals the tree the spec expects,
  and the run names no loss. The comparison is blind to exactly the
  normalizations `normalizations` lists below and nothing else: every
  attribute is compared unless a row of `droppedAttrs` declares it, and no
  attribute that decides whether content reaches a reader (`readerAttrs`)
  can be one. `--selftest` breaks each normalization in both directions.
* `rejected` — the strict dialect refuses the construct by design, *and*
  something other than the reader says the refused construct is there: a
  raw-HTML refusal's text passes through the spec's own expected HTML
  verbatim, and an indented-code or lazy refusal is on the reviewed list
  (`tests/commonmark/strict-reviewed.tsv`), which fails in both directions.
  The reader under test raised the refusal, so it cannot also be the
  evidence for it.
* `divergence` — a deliberate difference, listed in `divergences` with its
  reason. Adding a row here is a dialect decision, never a code change's
  side effect.
* `owed` — the engine does not do this yet. Not a pass and not an excuse:
  the ratchet lets this number fall and never rise. And `owed` never hides
  silence: a gap construct the expected page carries (a rule, a start
  number, a title, a language, a fourth-level heading) that the engine's
  page drops must be named by the run, or every mode fails (`silentGaps`).

The ratchet is the tier file `tests/scoreboard/commonmark.tsv`, in the one
scoreboard format and under the one ratchet every tier obeys
(`Scoreboard.tierMain`, `Scoreboard.ratchet`): per spec section a
`<section>.match` and a `<section>.cases` row, encoded `pairs match/cases`
so the queue ranks sections by their gap. Any change fails `--check` — a
fall, a vanished section, and an unrecorded rise alike; regenerating records
a rise, and writes a fall only where the committed file carries a
human-written `# lowered:` line naming it. Hermetic — `--check` reads the
vendored spec and the committed tables, nothing else.

Comparison is over *trees*, not strings: the engine's HTML is a typed tree
already, and the spec's expected HTML is read by the tolerant reader below
into the same shape, then both are canonicalized by `canon`. A string
comparison would report the two emitters' indentation as content.
-/
import LeanTex
import scripts.Board

open LeanTex.Core

def specPath : String := "tests/commonmark/spec-0.31.2.txt"
def verdictPath : String := "tests/commonmark/verdicts.tsv"
def tierPath : String := "tests/scoreboard/commonmark.tsv"

/-- The sha256 the provenance file records. Provenance, not the gate: it is
what a human verifies against upstream, and `PROVENANCE.txt` carries it. -/
def specSha : String :=
  "257c41ad946f7a1414a499aca402a1aa8fdac3678532266611348c1cf54f4b80"

/-- The gate on the vendored input: an in-Lean content key, so the check
needs no host tool. `sha256sum` was shelled out to, which fails under the
repo's own hermetic check — PATH pointed at an empty directory — and a
classifier whose first act is to spawn a process cannot run there at all. -/
def specKey : String :=
  "9AED364DA0B11E9BF5347E88BB9B04E1"

-- ## The declared normalizations
--
-- Each one is a difference the comparison is blind to, with the reason it
-- is not a difference in what the construct means. A loose normalization
-- hides a real defect, so the list is short and every entry names what it
-- would hide. The attribute drop is one table, `droppedAttrs`: `canonG` and
-- the chrome walks read it, and the attribute entry below is rendered from
-- it, so the declaration and what the comparison does cannot drift apart.

/-- The attributes the comparison is blind to, each with what dropping it
hides. A row's attribute is dropped from both trees and from the chrome the
comparison unwraps; **every other attribute is compared as content**, so an
attribute the engine starts to emit is a difference until a row here
declares it. The filter was once the other way round — six attributes kept
and every other dropped, declared nowhere — and it certified a page whose
every paragraph was `hidden` as 323 matches. -/
def droppedAttrs : List (String × String) :=
  [("class",
    "the engine's styling classes (`numbered`, `line`). Its `language-*` \
tokens are kept and compared on both sides: the one class a spec example \
states as content, a fenced block's info string. Dropping `class` whole \
once hid three lost languages the run had named with W0110"),
   ("id", "the ids the engine generates for headings and their sections"),
   ("style", "the style=\"color: inherit\" the engine sets on a link from its \
palette: styling"),
   ("tabindex",
    "the tab stop the HTML backend gives every code block, so a keyboard can \
reach and scroll its <pre>: focus order, not content, and every reader gets \
the same text with or without it. Every match whose page carries a code \
block rests on this row")]

/-- Attributes that decide whether content reaches a reader, or how it is
read, and so are never dropped: `hidden` and `inert` take content from every
reader, `aria-hidden` from assistive technology; `role` can make a
construct's content presentational or announce it as another thing; `lang`
decides the voice and the hyphenation it is read with. No spec example
states one on a construct, so any the engine adds is a difference the
comparison must see. `--selftest` holds `droppedAttrs` disjoint from these,
and each of them a difference on an element and on the chrome. -/
def readerAttrs : List String := ["hidden", "inert", "aria-hidden", "role", "lang"]

def dropsAttr (a : String) : Bool := droppedAttrs.any (·.1 == a)

def normalizations : List (String × String) :=
  [("document chrome",
    "a spec example is a fragment; the engine emits a document. The \
comparison reads the content of <main> and unwraps the <section> elements \
the sectioning walk builds, but only through elements whose every attribute \
is a declared drop: a <section> or <main> carrying anything else, `hidden` \
among them, stays in the compared tree. Hides: those wrappers and their \
declared attributes, nothing about a construct. A construct that failed to \
reach <main> at all still fails, because the expected tree is not empty \
wherever the spec expects output."),
   ("attributes that carry no content",
    "every attribute is compared as content except these, dropped from both \
sides. Hides: " ++ "; ".intercalate (droppedAttrs.map fun (a, h) => a ++ " — " ++ h)
      ++ "."),
   ("inter-element whitespace",
    "outside <pre>, HTML collapses whitespace and the two emitters indent \
differently; inside <pre> every byte is kept and compared. Hides: a \
significant space outside <pre>, which no spec example depends on because \
HTML itself would collapse it."),
   ("heading level offset",
    "the spec's `#` is <h1>; the engine's heading is a *section* in a \
document whose own title is the <h1>, so it renders one level down. Both \
sides are normalized to a level ordinal — the engine's tag minus its \
measured base, the spec's minus one — so a wrong *relative* level still \
fails. Hides: the absolute tag, which is the document class's decision."),
   ("one trailing newline in a code block",
    "the spec's expected HTML for a fenced or indented code block always \
ends its <pre><code> content with a newline; this engine's verbatim block \
holds the lines without the final one. Exactly one trailing newline is \
dropped from each side before comparing, and every other byte inside <pre> \
is compared as it stands. Hides: nothing that renders — a browser does not \
paint a newline immediately before </pre> — and a code block that genuinely \
ends in a blank line differs by two newlines, so it still fails."),
   ("attribute order",
    "the two emitters order attributes differently; the comparison sorts \
them. Hides: nothing — HTML attribute order is not content.")]

-- ## The deliberate divergences
--
-- A case listed here differs from the spec on purpose. The rationale is
-- the entry: a row with no reason is not a divergence, it is a defect.

def divergences : List (Nat × String) := []

-- ## The vendored spec

structure Example where
  id : Nat
  section_ : String
  md : String
  html : String
  deriving Inhabited

/-- Restore the spec's tab spelling: an example body writes a tab as U+2192
so the document reads, and the reader puts the tab back. -/
def untab (s : String) : String :=
  String.ofList (s.toList.map (fun c => if c == '\u2192' then '\t' else c))

/-- The examples, in document order, each tagged with the section heading in
force. `## ` lines inside an example are the spec documenting ATX headings,
not section headings, so the state machine tracks the fences. -/
def readExamples (text : String) : Array Example := Id.run do
  let fence := String.ofList (List.replicate 32 '`')
  let mut out : Array Example := #[]
  let mut sec := "Introduction"
  let mut inside := false
  let mut afterDot := false
  let mut md : Array String := #[]
  let mut html : Array String := #[]
  let mut n := 0
  for raw in text.splitOn "\n" do
    let line := if raw.endsWith "\r" then (raw.toList.dropLast |> String.ofList) else raw
    if inside then
      if line == fence then
        n := n + 1
        out := out.push
          { id := n, section_ := sec,
            md := untab (md.foldl (fun s l => s ++ l ++ "\n") ""),
            html := untab (html.foldl (fun s l => s ++ l ++ "\n") "") }
        inside := false
        afterDot := false
        md := #[]
        html := #[]
      else if line == "." && !afterDot then
        afterDot := true
      else if afterDot then
        html := html.push line
      else
        md := md.push line
    else if line.startsWith fence && (line.splitOn "example").length > 1 then
      inside := true
    else if line.startsWith "## " then
      sec := (line.toList.drop 3 |> String.ofList)
  return out

-- ## A tolerant HTML reader
--
-- Enough of HTML to read what the spec's expected output contains: tags,
-- attributes, void elements, text, character references. Total by
-- construction: one index loop with an explicit element stack, the shape
-- `Parse.parse` uses.

structure HFrame where
  tag : String
  attrs : Array (String × String)
  kids : Array Html.Node
  deriving Inhabited

def hVoid : List String := Html.voidTags

/-- A numeric character reference's body (`#123`, `#x1F`) as its character,
or the literal text when it is not one. -/
def hNumeric (name : String) : String := Id.run do
  let rest := name.toList.drop 1
  let hex := rest.headD ' ' == 'x' || rest.headD ' ' == 'X'
  let ds := if hex then rest.drop 1 else rest
  let mut v := 0
  let mut good := !ds.isEmpty
  for c in ds do
    if '0' ≤ c && c ≤ '9' then v := v * (if hex then 16 else 10) + (c.toNat - 48)
    else if hex && 'a' ≤ c && c ≤ 'f' then v := v * 16 + (c.toNat - 87)
    else if hex && 'A' ≤ c && c ≤ 'F' then v := v * 16 + (c.toNat - 55)
    else good := false
  if good && v > 0 && v ≤ 0x10ffff && !(v ≥ 0xd800 && v ≤ 0xdfff) then
    return String.singleton (Char.ofNat v)
  if good then return "\ufffd"
  return "&" ++ name ++ ";"

def hEntity (name : String) : String :=
  match name with
  | "amp" => "&"
  | "lt" => "<"
  | "gt" => ">"
  | "quot" => "\""
  | "apos" => "'"
  | "nbsp" => "\u00a0"
  | "copy" => "\u00a9"
  | "auml" => "\u00e4"
  | "ouml" => "\u00f6"
  | "uuml" => "\u00fc"
  | "szlig" => "\u00df"
  | "Dagger" => "\u2021"
  | "dagger" => "\u2020"
  | "hellip" => "\u2026"
  | "mdash" => "\u2014"
  | "ndash" => "\u2013"
  | _ => if name.startsWith "#" then hNumeric name else "&" ++ name ++ ";"

/-- Character references in a text run. -/
def hText (cs : Array Char) : String := Id.run do
  let mut out := ""
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    if cs[i]? == some '&' then
      let mut j := i + 1
      let mut name := ""
      let mut closed := false
      for _ in [0:34] do
        unless closed do
          match cs[j]? with
          | some ';' => closed := true
          | some c =>
            name := name.push c
            j := j + 1
          | none => closed := false
      if closed && !name.isEmpty then
        out := out ++ hEntity name
        i := j + 1
      else
        out := out.push '&'
        i := i + 1
    else
      out := out.push ((cs[i]?).getD ' ')
      i := i + 1
  return out

/-- Parse a fragment of HTML into nodes. Unknown or stray tags become text
so nothing is silently dropped. -/
def hParse (src : String) : Array Html.Node := Id.run do
  let cs := src.toList.toArray
  let mut stack : Array HFrame := #[]
  let mut kids : Array Html.Node := #[]
  let mut text : Array Char := #[]
  let mut i := 0
  let flush : Array Html.Node → Array Char → Array Html.Node := fun ks t =>
    if t.isEmpty then ks else ks.push (.text (hText t))
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    if cs[i]? == some '<' then
      -- A comment or declaration: skipped whole.
      if cs[i + 1]? == some '!' then
        let mut j := i + 1
        for _ in [0:cs.size + 1] do
          if j < cs.size && cs[j]? != some '>' then j := j + 1
        i := j + 1
      else
        let closing := cs[i + 1]? == some '/'
        let mut j := if closing then i + 2 else i + 1
        let mut name := ""
        for _ in [0:cs.size + 1] do
          match cs[j]? with
          | some c =>
            if c.isAlphanum then
              name := name.push c.toLower
              j := j + 1
          | none => pure ()
        if name.isEmpty then
          text := text.push '<'
          i := i + 1
        else
          -- Attributes up to `>`.
          let mut attrs : Array (String × String) := #[]
          let mut selfClose := false
          let mut done := false
          for _ in [0:cs.size + 1] do
            unless done do
              match cs[j]? with
              | none => done := true
              | some '>' =>
                done := true
                j := j + 1
              | some '/' =>
                selfClose := true
                j := j + 1
              | some c =>
                if c == ' ' || c == '\n' || c == '\t' || c == '\r' then j := j + 1
                else
                  let mut an := ""
                  for _ in [0:cs.size + 1] do
                    match cs[j]? with
                    | some d =>
                      if d != '=' && d != '>' && d != ' ' && d != '/' then
                        an := an.push d.toLower
                        j := j + 1
                    | none => pure ()
                  let mut av := ""
                  if cs[j]? == some '=' then
                    j := j + 1
                    match cs[j]? with
                    | some q =>
                      if q == '"' || q == '\'' then
                        j := j + 1
                        let mut vs : Array Char := #[]
                        let mut vdone := false
                        for _ in [0:cs.size + 1] do
                          unless vdone do
                            match cs[j]? with
                            | none => vdone := true
                            | some d =>
                              if d == q then
                                vdone := true
                                j := j + 1
                              else
                                vs := vs.push d
                                j := j + 1
                        av := hText vs
                      else
                        let mut vs : Array Char := #[]
                        for _ in [0:cs.size + 1] do
                          match cs[j]? with
                          | some d =>
                            if d != '>' && d != ' ' then
                              vs := vs.push d
                              j := j + 1
                          | none => pure ()
                        av := hText vs
                    | none => pure ()
                  unless an.isEmpty do attrs := attrs.push (an, av)
          if closing then
            kids := flush kids text
            text := #[]
            -- Close the innermost frame with this name, dropping any
            -- unclosed frames above it.
            let mut depth : Option Nat := none
            for (f, k) in stack.zipIdx do
              if f.tag == name then depth := some k
            match depth with
            | none => pure ()
            | some d =>
              for _ in [0:stack.size] do
                if stack.size > d then
                  if let some f := stack.back? then
                    stack := stack.pop
                    kids := f.kids.push (.elem f.tag f.attrs kids)
            i := j
          else
            kids := flush kids text
            text := #[]
            if selfClose || hVoid.contains name then
              kids := kids.push (.elem name attrs #[])
            else
              stack := stack.push { tag := name, attrs, kids }
              kids := #[]
            i := j
    else
      text := text.push ((cs[i]?).getD ' ')
      i := i + 1
  kids := flush kids text
  for _ in [0:stack.size] do
    if let some f := stack.back? then
      stack := stack.pop
      kids := f.kids.push (.elem f.tag f.attrs kids)
  return kids


-- ## Canonicalization
--
-- Both trees reduced to one string by the same function, so the comparison
-- is over trees and the failure report is readable. Every attribute is kept
-- except the declared drops (`droppedAttrs`).

/-- The one class token a spec example states as content: a fenced block's
`language-x`. Every other class token is the engine's styling. -/
def languageClass? (attrs : Array (String × String)) : Option String :=
  match attrs.find? (·.1 == "class") with
  | none => none
  | some (_, v) =>
    let toks := (v.splitOn " ").filter (·.startsWith "language-")
    if toks.isEmpty then none else some (String.intercalate " " toks)

/-- The IR gaps a markdown route names, each with the one thing on the page
it costs. Read only to *attribute* an `owed` case to the gap that blocks it;
a case these hide is never a `match` (`classify`). -/
def gapSubjects : List String :=
  ["md:thematic-break", "md:list-start", "md:loose-list", "md:link-title",
   "md:image-title", "md:image-alt", "md:heading-depth", "md:code-info"]

def hLevelTag? (tag : String) : Option Nat :=
  match tag with
  | "h1" => some 1 | "h2" => some 2 | "h3" => some 3
  | "h4" => some 4 | "h5" => some 5 | "h6" => some 6
  | _ => none

/-- Collapse a run of whitespace to one space; drop it entirely when the
text is only whitespace. -/
def squeeze (s : String) : String := Id.run do
  let mut out := ""
  let mut sp := false
  for c in s.toList do
    if c == ' ' || c == '\n' || c == '\t' || c == '\r' then
      sp := true
    else
      if sp && !out.isEmpty then out := out.push ' '
      sp := false
      out := out.push c
  if sp && !out.isEmpty then out := out.push ' '
  return out

/-- One trailing newline removed: the declared code-block normalization. -/
def dropOneTrailingNewline (s : String) : String :=
  if s.endsWith "\n" then String.ofList s.toList.dropLast else s

mutual

/-- One node canonicalized. `base` is the heading level the emitter starts
sectioning at, subtracted so the two sides' ordinals line up; `pre` says
whether whitespace is significant here. `gaps` are the IR gaps whose cost
is hidden — empty for the comparison that decides `match`, and the run's
own routes only when *attributing* an `owed` case; `inLi` says the parent
is a list item, where a loose list's `<p>` sits. -/
def canonG (gaps : List String) (base : Nat) (pre inLi : Bool) (n : Html.Node) : String :=
  match n with
  | .text s => if pre then s else squeeze s
  -- A stylesheet or script node is compared as the element it prints as,
  -- never dropped: dropping them was a normalization nothing declared.
  | .style css => "<style>" ++ squeeze css ++ "</style>"
  | .script attrs js =>
    let keep := (attrs.filter (fun a => !dropsAttr a.1)).qsort (·.1 < ·.1)
    "<script" ++ keep.foldl (fun s a => s ++ " " ++ a.1 ++ "=" ++ a.2) "" ++ ">"
      ++ squeeze js ++ "</script>"
  | .elem tag attrs kids =>
    if tag == "hr" && gaps.contains "md:thematic-break" then ""
    else if tag == "p" && inLi && gaps.contains "md:loose-list" then
      canonGList gaps base pre false "" kids.toList
    else
      let tag' :=
        match hLevelTag? tag with
        | some l =>
          let ord := if l ≥ base then l - base + 1 else 1
          "h#" ++ toString (if gaps.contains "md:heading-depth" then min ord 3 else ord)
        | none => tag
      let costs (a : String) : Bool :=
        (a == "start" && gaps.contains "md:list-start")
          || (a == "title" && tag == "a" && gaps.contains "md:link-title")
          || (a == "title" && tag == "img" && gaps.contains "md:image-title")
          || (a == "alt" && gaps.contains "md:image-alt")
      let keep := attrs.filter (fun a => !dropsAttr a.1 && !costs a.1)
      let keep := match languageClass? attrs with
        | some v => if gaps.contains "md:code-info" then keep else keep.push ("class", v)
        | none => keep
      let keep := keep.qsort (·.1 < ·.1)
      let as := keep.foldl (fun s a => s ++ " " ++ a.1 ++ "=" ++ a.2) ""
      let pre' := pre || Html.preserveTags.contains tag
      if Html.voidTags.contains tag then "<" ++ tag' ++ as ++ ">"
      else
        let body := canonGList gaps base pre' (tag == "li") "" kids.toList
        -- Text-node boundaries are not line boundaries. Normalize once on
        -- the assembled block code, leaving its child elements intact.
        let body := if pre && tag == "code" then dropOneTrailingNewline body else body
        "<" ++ tag' ++ as ++ ">" ++ body ++ "</" ++ tag' ++ ">"

def canonGList (gaps : List String) (base : Nat) (pre inLi : Bool) (acc : String) :
    List Html.Node → String
  | [] => acc
  | k :: rest => canonGList gaps base pre inLi (acc ++ canonG gaps base pre inLi k) rest

end

/-- The comparison that decides `match`: no gap is hidden. -/
def canon (base : Nat) (pre : Bool) (n : Html.Node) : String := canonG [] base pre false n

def canonList (base : Nat) (pre : Bool) (acc : String) (ns : List Html.Node) : String :=
  canonGList [] base pre false acc ns

-- ## What an IR gap costs, counted
--
-- `owed` must not hide silence. A case can be owed on an IR gap only when
-- its run names the gap; a construct the expected page carries that the
-- engine's page drops *without* naming it is a reader defect — the shape a
-- list followed by `* * *` took, which shipped no rule and raised nothing,
-- so the ledger read it as one more owed case.

/-- One count per gap construct on a tree: thematic breaks, an ordered
list's start other than 1, a link's title, an image's title, a code
element's language class, and a heading below the third relative level —
each beside the count of the element that carries it, so a construct lost
with its carrier (a reference link the reader does not resolve drops its
title *and* its link) is read as the carrier's defect, not the gap's. -/
structure GapInk where
  rules : Nat := 0
  starts : Nat := 0
  ols : Nat := 0
  linkTitles : Nat := 0
  links : Nat := 0
  imageTitles : Nat := 0
  images : Nat := 0
  langs : Nat := 0
  codes : Nat := 0
  deep : Nat := 0
  headings : Nat := 0
  deriving BEq, Repr, Inhabited

mutual

def gapInkOne (base : Nat) (g : GapInk) (n : Html.Node) : GapInk :=
  match n with
  | .elem tag attrs kids =>
    let has (a : String) : Bool := attrs.any (·.1 == a)
    let g := if tag == "hr" then { g with rules := g.rules + 1 } else g
    let g := if tag == "ol" then { g with ols := g.ols + 1 } else g
    let g := if tag == "ol" && attrs.any (fun a => a.1 == "start" && a.2 != "1") then
      { g with starts := g.starts + 1 } else g
    let g := if tag == "a" then { g with links := g.links + 1 } else g
    let g := if tag == "a" && has "title" then { g with linkTitles := g.linkTitles + 1 } else g
    let g := if tag == "img" then { g with images := g.images + 1 } else g
    let g := if tag == "img" && has "title" then { g with imageTitles := g.imageTitles + 1 } else g
    let g := if tag == "code" then { g with codes := g.codes + 1 } else g
    let g := if (languageClass? attrs).isSome then { g with langs := g.langs + 1 } else g
    let g := match hLevelTag? tag with
      | some l =>
        let g := { g with headings := g.headings + 1 }
        if l ≥ base && l - base + 1 > 3 then { g with deep := g.deep + 1 } else g
      | none => g
    gapInkList base g kids.toList
  | _ => g

def gapInkList (base : Nat) (g : GapInk) : List Html.Node → GapInk
  | [] => g
  | n :: rest => gapInkList base (gapInkOne base g n) rest

end

/-- The gaps whose construct the expected page carries more of than the
engine's page, where the engine's page does carry the element the construct
sits on, and with no route in the run naming it: silence, never a verdict.
A `W0110` names a lost listing language as surely as `md:code-info` does. -/
def silentGaps (want got : GapInk) (routes : Array String) : Array String := Id.run do
  let named (g : String) : Bool :=
    routes.contains g || (g == "md:code-info" && routes.contains "W0110")
  let mut out : Array String := #[]
  for (g, w, e, wc, ec) in [("md:thematic-break", want.rules, got.rules, 0, 0),
      ("md:list-start", want.starts, got.starts, want.ols, got.ols),
      ("md:link-title", want.linkTitles, got.linkTitles, want.links, got.links),
      ("md:image-title", want.imageTitles, got.imageTitles, want.images, got.images),
      ("md:code-info", want.langs, got.langs, want.codes, got.codes),
      ("md:heading-depth", want.deep, got.deep, want.headings, got.headings)] do
    if w > e && ec ≥ wc && !named g then out := out.push g
  return out

-- The engine's page reduced to the fragment a spec example is about: the
-- content of `<main>`, with the sectioning walk's `<section>` wrappers
-- unwrapped. Each walk is a one-node function plus its `List` companion
-- with an accumulator, which is what makes the recursion structural over a
-- tree whose children are an `Array`. A wrapper is looked through only when
-- it carries nothing but declared drops: `<section hidden>` unwrapped would
-- hide from the comparison exactly what it hides from a reader.

/-- Does an element carry nothing but declared drops? Only such a wrapper
is chrome the comparison may look through. -/
def onlyDropped (attrs : Array (String × String)) : Bool :=
  attrs.all (fun a => dropsAttr a.1)

mutual

def unwrapOne (out : Array Html.Node) (n : Html.Node) : Array Html.Node :=
  match n with
  | .elem "section" attrs kids =>
    if onlyDropped attrs then unwrapList out kids.toList else out.push n
  | _ => out.push n

def unwrapList (out : Array Html.Node) : List Html.Node → Array Html.Node
  | [] => out
  | n :: rest => unwrapList (unwrapOne out n) rest

end

mutual

/-- `<main>`'s content, found through wrappers that carry only declared
drops. A `<main>` carrying anything else is its own fragment, so the
comparison sees it; an element carrying anything else is not looked
through, so the whole body is compared. -/
def mainOf? (n : Html.Node) : Option (Array Html.Node) :=
  match n with
  | .elem "main" attrs kids => if onlyDropped attrs then some kids else some #[n]
  | .elem _ attrs kids => if onlyDropped attrs then mainList? kids.toList else none
  | _ => none

def mainList? : List Html.Node → Option (Array Html.Node)
  | [] => none
  | n :: rest =>
    match mainOf? n with
    | some k => some k
    | none => mainList? rest

end

mutual

def firstHeadOne? (n : Html.Node) : Option Nat :=
  match n with
  | .elem tag _ kids =>
    match hLevelTag? tag with
    | some l => some l
    | none => firstHeadList? kids.toList
  | _ => none

def firstHeadList? : List Html.Node → Option Nat
  | [] => none
  | n :: rest =>
    match firstHeadOne? n with
    | some l => some l
    | none => firstHeadList? rest

end

-- ## The engine under test

/-- The fragment a spec example is compared against: `<main>`'s content with
the sectioning walk's wrappers unwrapped, each looked through only when it
carries nothing but declared drops (`mainOf?`, `unwrapOne`). -/
def fragmentOf (body : Array Html.Node) : Array Html.Node :=
  unwrapList #[] ((mainList? body.toList).getD body).toList

/-- One markdown source through the reader, the desugaring, the one
elaborator and the HTML backend: the fragment tree and the diagnostics. -/
def engineFragment (src : String) : Array Html.Node × Array Diag :=
  let (raws, readDiags) := Md.read "case.md" src
  let (doc, diags) := Elab.runRaws "case.md" raws readDiags
  let (_, body, htmlDiags) := HtmlDoc.emitTree {} doc
  (fragmentOf body, diags ++ htmlDiags)

/-- The heading level the engine's sectioning starts at, measured from a
one-heading probe rather than asserted: the offset the comparison
normalizes by is then a fact about this build. -/
def measuredBase : Nat :=
  (firstHeadList? (engineFragment "# probe\n").1.toList).getD 2

-- ## Verdicts

inductive Verdict where
  | match_
  | rejected
  | divergence
  | owed
  deriving BEq, Repr, Inhabited

def Verdict.name : Verdict → String
  | .match_ => "match"
  | .rejected => "rejected"
  | .divergence => "divergence"
  | .owed => "owed"

def Verdict.ofName? (s : String) : Option Verdict :=
  match s with
  | "match" => some .match_
  | "rejected" => some .rejected
  | "divergence" => some .divergence
  | "owed" => some .owed
  | _ => none

/-- The three subjects the strict dialect refuses by design. A refusal under
one of these is only a *claim* that the case is a design decision: the
reader under test raised it, so it cannot also be the evidence. `rejected`
needs corroboration from outside the reader (`corroborated`). -/
def strictSubjects : List String :=
  ["md:raw-html", "md:indented-code", "md:lazy-continuation"]

/-- One strict refusal a run raised: its subject and the source position the
reader gave for the refused construct. -/
structure Refusal where
  subject : String
  line : Nat
  col : Nat
  deriving BEq, Repr, Inhabited

def refusalsOf (diags : Array Diag) : Array Refusal :=
  diags.filterMap fun d =>
    if d.kind != .E0390 then none
    else match d.subject, d.span with
      | some s, some sp =>
        if strictSubjects.contains s then some ⟨s, sp.pos.line, sp.pos.col⟩ else none
      | _, _ => none

/-- The source text a raw-HTML refusal names: from the refusal's position to
the first `>` at or after it (across line ends), or to the end of its line
when no `>` follows. A prefix of the refused construct, computed from the
source alone and never from the reader's own tag grammar. -/
def refusedPrefix (md : String) (line col : Nat) : String := Id.run do
  let ls := (md.splitOn "\n").toArray
  let some l := ls[line - 1]? | return ""
  let start := (l.toList.drop (col - 1))
  let mut out := ""
  for c in start do
    out := out.push c
    if c == '>' then return out
  -- No `>` on the line: look across the following lines for one.
  let mut more := out
  for k in [line:ls.size] do
    let some l2 := ls[k]? | break
    more := more.push '\n'
    for c in l2.toList do
      more := more.push c
      if c == '>' then return more
  return out

/-- The reviewed list: the cases whose indented-code or lazy-continuation
refusal a human checked against the spec text (`tests/commonmark/
strict-reviewed.tsv`). A raw-HTML refusal needs no list — the spec's own
expected HTML corroborates it — but these two classes leave nothing in the
expected output a check could read. -/
def reviewedPath : String := "tests/commonmark/strict-reviewed.tsv"

def parseReviewed (text : String) : Except String (Array (Nat × String)) := do
  let mut out : Array (Nat × String) := #[]
  for raw in text.splitOn "\n" do
    let line := raw.trimAsciiEnd.toString
    if line.isEmpty || line.startsWith "#" then continue
    let fs := (line.splitOn "\t").toArray
    let some idS := fs[0]? | throw s!"reviewed row with no case: {line}"
    let some sub := fs[1]? | throw s!"reviewed row with no subject: {line}"
    let some why := fs[2]? | throw s!"reviewed row with no reason: {line}"
    let some id := idS.toNat? | throw s!"reviewed case is not a number: {line}"
    unless sub == "md:indented-code" || sub == "md:lazy-continuation" do
      throw s!"reviewed row names '{sub}': only indented code and lazy continuation are reviewed"
    if why.trimAscii.isEmpty then throw s!"reviewed row {id} gives no reason"
    if out.contains (id, sub) then throw s!"reviewed row {id} {sub} appears twice"
    out := out.push (id, sub)
  return out

/-- Is one refusal corroborated by something other than the reader? Raw
HTML: the refused construct passes through the spec's expected HTML
verbatim — escaped text there is `&lt;`, so a literal prefix is markup the
spec itself passed through. The other two classes: a reviewed row. -/
def corroborated (reviewed : Array (Nat × String)) (ex : Example) (r : Refusal) : Bool :=
  if r.subject == "md:raw-html" then
    let p := refusedPrefix ex.md r.line r.col
    p.length ≥ 2 && containsSub ex.html p
  else reviewed.contains (ex.id, r.subject)

/-- The typographic characters the elaborator's `smartPunct` produces, mapped
back to the ASCII the spec writes. A case whose only difference is this is
not a defect and not a decided divergence: it is waiting on a dialect
decision the user owns, so it stays `owed` and carries the note. -/
def unsmarten (s : String) : String := Id.run do
  let mut out := ""
  for c in s.toList do
    if c == '\u2014' then out := out ++ "---"
    else if c == '\u2013' then out := out ++ "--"
    else if c == '\u2026' then out := out ++ "..."
    else if c == '\u201c' || c == '\u201d' then out := out.push '"'
    else if c == '\u2018' || c == '\u2019' then out := out.push '\''
    else out := out.push c
  return out

/-- The note a pending dialect decision carries. -/
def smartNote : String := "pending-decision:smart-punctuation"

/-- The losses a run names that bar it from `match`, sorted: every markdown
route (`W0307`/`W0392` under an `md:` subject), and any `W0110`, which on a
markdown run means the desugaring handed the elaborator an option it could
not read — the shape the injected info strings took. Other degraded codes
(`W0601` a missing image file, `W0376` a missing alternative) are about the
document, not the reader, and the canonical trees already carry what they
are about. -/
def routesOf (diags : Array Diag) : Array String := Id.run do
  let mut out : Array String := #[]
  for d in diags do
    let s :=
      if d.kind == .W0110 then some "W0110"
      else if d.kind == .W0307 || d.kind == .W0392 then
        match d.subject with
        | some s => if s.startsWith "md:" then some s else none
        | none => none
      else none
    if let some s := s then
      unless out.contains s do out := out.push s
  return out.qsort (· < ·)

/-- A case's verdict, as a pure function of what the run produced: the two
canonical trees, the same two with the run's own routes hidden, the refusals
with their corroboration, and the routes. `classify` computes the inputs;
the selftest breaks each rule here.

* A refusal outranks a comparison, but only when *every* refusal is
  corroborated — then the case is `rejected`. An uncorroborated one is a
  reader defect, and the case is `owed` with the note naming it.
* A case whose run names a loss is never a `match`. When the trees agree
  once exactly the named gaps are hidden, the note says which gaps block it
  (`blocked-by:`): that is the verdict row an IR gap owes, never a false
  match. -/
def judge (want got wantG gotG : String) (refusals : Array (Refusal × Bool))
    (routes : Array String) (divergence : Option String) : Verdict × String :=
  let subjects (rs : Array (Refusal × Bool)) : String :=
    String.intercalate "," ((rs.map (·.1.subject)).toList.eraseDups.mergeSort (· ≤ ·))
  if !refusals.isEmpty then
    let bad := refusals.filter (!·.2)
    if bad.isEmpty then (.rejected, "refused:" ++ subjects refusals)
    else (.owed, "uncorroborated:" ++ subjects bad)
  else match divergence with
    | some why => (.divergence, why)
    | none =>
      if want == got && routes.isEmpty then (.match_, "")
      else if !routes.isEmpty && wantG == gotG then
        (.owed, "blocked-by:" ++ String.intercalate "," routes.toList)
      else if routes.isEmpty && unsmarten got == want then (.owed, smartNote)
      else (.owed, "")

/-- One case through the engine and the judge. -/
structure Judged where
  verdict : Verdict
  note : String
  want : String
  got : String
  refusals : Array (Refusal × Bool)
  routes : Array String
  /-- Gap constructs the expected page carries and the engine's page drops
  with nothing in the run naming them (`silentGaps`); empty for a run that
  raised a strict refusal, which fails the build and names its loss. -/
  silent : Array String := #[]
  deriving Inhabited

def classify (base : Nat) (reviewed : Array (Nat × String)) (ex : Example) : Judged :=
  -- The spec's own base is 1 (`#` is `<h1>`); the engine's is measured.
  -- Subtracting one number from both sides collapsed h1 and h2 to the same
  -- ordinal and reported every two-level heading document as owed.
  let wantNs := (hParse ex.html).toList
  let want := canonList 1 false "" wantNs
  let (ns, diags) := engineFragment ex.md
  let got := canonList base false "" ns.toList
  let routes := routesOf diags
  let gaps := routes.toList.filter gapSubjects.contains
  let wantG := canonGList gaps 1 false false "" wantNs
  let gotG := canonGList gaps base false false "" ns.toList
  let refusals := (refusalsOf diags).map fun r => (r, corroborated reviewed ex r)
  let (v, note) := judge want got wantG gotG refusals routes
    ((divergences.find? (·.1 == ex.id)).map (·.2))
  let silent := if !(diags.any (·.kind == .E0390)) then
      silentGaps (gapInkList 1 {} wantNs) (gapInkList base {} ns.toList) routes
    else #[]
  { verdict := v, note, want, got, refusals, routes, silent }


-- ## The committed tables

structure Row where
  id : Nat
  section_ : String
  verdict : Verdict
  note : String
  deriving Inhabited

def fields (line : String) : Array String := (line.splitOn "\t").toArray

def parseVerdicts (text : String) : Except String (Array Row) := do
  let mut out : Array Row := #[]
  for raw in text.splitOn "\n" do
    let line := raw.trimAsciiEnd.toString
    if line.isEmpty || line.startsWith "#" then continue
    let fs := fields line
    let some idS := fs[0]? | throw s!"row with no id: {line}"
    let some sec := fs[1]? | throw s!"row with no section: {line}"
    let some vS := fs[2]? | throw s!"row with no verdict: {line}"
    let some id := idS.toNat? | throw s!"row id is not a number: {line}"
    let some v := Verdict.ofName? vS | throw s!"row verdict is unknown: {line}"
    out := out.push { id, section_ := sec, verdict := v, note := (fs[3]?).getD "" }
  return out

/-- Section order as the spec states it, so the report reads in document
order rather than alphabetically. The tier file itself is sorted by item,
as the scoreboard format requires. -/
def sectionsOf (exs : Array Example) : Array String := Id.run do
  let mut out : Array String := #[]
  for e in exs do
    unless out.contains e.section_ do out := out.push e.section_
  return out

/-- The tier's rows: one `<section>.match` and one `<section>.cases` per spec
section, the `pairs match/cases` encoding. The ratchet is the scoreboard's
own (`Scoreboard.ratchet`), so this tier cannot mean something different by
"regressed" than every other tier does. -/
def tierRows (exs : Array Example) (rows : Array Row) : Array Scoreboard.Row := Id.run do
  let mut out : Array Scoreboard.Row := #[]
  for sec in sectionsOf exs do
    let ss := rows.filter (·.section_ == sec)
    out := out.push
      { item := sec ++ ".match", value := Int.ofNat (ss.filter (·.verdict == .match_)).size }
    out := out.push { item := sec ++ ".cases", value := Int.ofNat ss.size }
  return out

def verdictText (rows : Array Row) : String := Id.run do
  let mut s := "# One row per CommonMark 0.31.2 spec example: id, section, verdict, note.\n"
  s := s ++ "# verdicts: match | rejected | divergence | owed.\n"
  s := s ++ "# `rejected` is a strict refusal (E0390) corroborated from outside the reader:\n"
  s := s ++ "# the expected HTML for raw HTML, tests/commonmark/strict-reviewed.tsv otherwise;\n"
  s := s ++ "# `divergence` needs a row in `divergences` in scripts/commonmark.lean;\n"
  s := s ++ "# `owed` is not implemented yet and the ratchet lets it only fall.\n"
  s := s ++ "# This file is written only by scripts/commonmark.lean.\n"
  for r in rows do
    s := s ++ toString r.id ++ "\t" ++ r.section_ ++ "\t" ++ r.verdict.name
      ++ (if r.note.isEmpty then "" else "\t" ++ r.note) ++ "\n"
  return s

-- ## The modes

def keyOf (path : String) : IO String := do
  let bytes ← IO.FS.readBinFile path
  return Flate.contentKey bytes

def counts (rows : Array Row) : Nat × Nat × Nat × Nat :=
  ((rows.filter (·.verdict == .match_)).size,
   (rows.filter (·.verdict == .rejected)).size,
   (rows.filter (·.verdict == .divergence)).size,
   (rows.filter (·.verdict == .owed)).size)

/-- Every case through `classify`, once. The rows are the committed verdicts;
the judged values carry what the reports and the reviewed-list check read,
so nothing reruns the engine. -/
def classifyAll (exs : Array Example) (reviewed : Array (Nat × String)) :
    Array Row × Array Judged := Id.run do
  let base := measuredBase
  let mut rows : Array Row := #[]
  let mut js : Array Judged := #[]
  for e in exs do
    let j := classify base reviewed e
    rows := rows.push { id := e.id, section_ := e.section_, verdict := j.verdict, note := j.note }
    js := js.push j
  return (rows, js)

/-- The reviewed list read in its other direction: a row naming a case whose
run no longer raises that refusal is stale, and fails — a reviewed list that
may lag the reader is a list that can certify anything. -/
def staleReviewed (exs : Array Example) (js : Array Judged)
    (reviewed : Array (Nat × String)) : Array String := Id.run do
  let mut out : Array String := #[]
  for (id, sub) in reviewed do
    match (exs.zip js).find? (·.1.id == id) with
    | none => out := out.push s!"reviewed case {id} is not in the spec"
    | some (_, j) =>
      unless j.refusals.any (·.1.subject == sub) do
        out := out.push s!"reviewed case {id} no longer raises {sub}; remove its row from {reviewedPath}"
  return out

def readReviewed : IO (Except String (Array (Nat × String))) := do
  unless ← System.FilePath.pathExists reviewedPath do
    return .error s!"{reviewedPath} is missing"
  return parseReviewed (← IO.FS.readFile reviewedPath)

def die (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln msg
  return code

/-- The tier's provenance lines: data, never gated. -/
def tierProvenance (exs : Array Example) (rows : Array Row) : Array String :=
  let (m, r, d, o) := counts rows
  #[s!"# spec: CommonMark 0.31.2, {exs.size} cases, sha256 {specSha}",
    s!"# verdicts ({verdictPath}): match {m}, rejected {r}, divergence {d}, owed {o}"]

/-- The three strict classes, and how many spec cases each one touches:
read off the subject each refusal carried, not asserted — with how many of
those refusals were corroborated. -/
def strictTouch (js : Array Judged) : Array (String × Nat × Nat) :=
  (strictSubjects.map fun s =>
    let touched := js.filter (·.refusals.any (·.1.subject == s))
    let corr := touched.filter (·.refusals.all (fun (r, ok) => r.subject != s || ok))
    (s, touched.size, corr.size)).toArray

/-- Which spec cases each IR gap blocks: the `owed` cases whose trees agree
once exactly the gaps their run named are hidden. The verdict rows an IR gap
owes, read back from the table. -/
def gapReport (rows : Array Row) : Array (String × Array Nat) :=
  (gapSubjects ++ ["W0110"]).toArray.filterMap fun g =>
    let ids := (rows.filter fun r =>
      r.note.startsWith "blocked-by:" && ((r.note.drop 11).toString.splitOn ",").contains g).map (·.id)
    if ids.isEmpty then none else some (g, ids)

def selftest : IO UInt32 := do
  let mut bad : Array String := #[]
  -- A comparison *records* its finding. Written to print it instead, this
  -- helper reported a real mismatch and the run still said `ok`.
  let check (name got want : String) : Option String :=
    if got == want then none else some s!"{name}: got {got}, want {want}"
  let fence := String.ofList (List.replicate 32 '`')
  -- The reader: one example, its section, its tab restoration.
  let sample := "## Tabs\n\n" ++ fence ++ " example\n\u2192foo\n.\n<pre><code>foo\n</code></pre>\n"
    ++ fence ++ "\n"
  let exs := readExamples sample
  unless exs.size == 1 do bad := bad.push s!"reader: {exs.size} examples, want 1"
  if let some e := exs[0]? then
    unless e.section_ == "Tabs" do bad := bad.push s!"reader: section '{e.section_}'"
    unless e.md == "\tfoo\n" do bad := bad.push "reader: tab not restored"
    unless e.html == "<pre><code>foo\n</code></pre>\n" do
      bad := bad.push s!"reader: html '{e.html}'"
  -- A `## ` line inside an example is the spec documenting ATX headings,
  -- not a section heading.
  let sample2 := "## Real\n\n" ++ fence ++ " example\n## not a section\n.\n<h2>x</h2>\n"
    ++ fence ++ "\n"
  if let some e := (readExamples sample2)[0]? then
    unless e.section_ == "Real" do
      bad := bad.push s!"reader: a heading inside an example became a section '{e.section_}'"
  -- The HTML reader and the canonical form. Every declared normalization is
  -- broken once here in both directions: it hides the difference it
  -- declares, and it does not hide the one next to it.
  let cn (base : Nat) (s : String) : String := canonList base false "" (hParse s).toList
  let same (name a b : String) : Option String :=
    if cn 1 a == cn 1 b then none else some s!"{name}: '{cn 1 a}' and '{cn 1 b}' differ"
  let differ (name a b : String) : Option String :=
    if cn 1 a != cn 1 b then none else some s!"{name}: '{a}' and '{b}' compare equal"
  let cs : List (Option String) :=
    [check "canon p" (cn 1 "<p>a <em>b</em></p>") "<p>a <em>b</em></p>",
     check "canon void" (cn 1 "<p>a<br />b</p>") "<p>a<br>b</p>",
     check "canon entity" (cn 1 "<p>&amp;&#65;</p>") "<p>&A</p>",
     check "canon void container" (cn 1 "<p>a<br>b</p>") "<p>a<br>b</p>",
     -- document chrome
     check "chrome: sections unwrap"
       (canonList 1 false "" (unwrapList #[] (hParse "<section><p>a</p></section>").toList).toList)
       "<p>a</p>",
     check "chrome: a wrapper that is not a section stays"
       (canonList 1 false "" (unwrapList #[] (hParse "<div><p>a</p></div>").toList).toList)
       "<div><p>a</p></div>",
     check "chrome: the fragment is <main>'s content"
       (canonList 1 false ""
         ((mainList? (hParse "<header>h</header><main><p>a</p></main>").toList).getD #[]).toList)
       "<p>a</p>",
     check "chrome: <main>'s content is still compared"
       (toString (canonList 1 false ""
         ((mainList? (hParse "<header>h</header><main><p>a</p></main>").toList).getD #[]).toList
         == canonList 1 false ""
         ((mainList? (hParse "<header>h</header><main><p>b</p></main>").toList).getD #[]).toList))
       "false",
     -- class and id: a language class is content, every other class and id is not
     same "class: a styling class is dropped" "<a class=\"x\" href=\"u\">t</a>" "<a href=\"u\">t</a>",
     same "id: a generated id is dropped" "<h2 id=\"x\">t</h2>" "<h2>t</h2>",
     check "class: a language token is kept, a styling one dropped"
       (cn 1 "<code class=\"language-x numbered\">c</code>") "<code class=language-x>c</code>",
     differ "class: a missing language is a difference"
       "<pre><code class=\"language-x\">c</code></pre>" "<pre><code>c</code></pre>",
     -- style
     same "style: dropped" "<a style=\"color: inherit\" href=\"u\">t</a>" "<a href=\"u\">t</a>",
     differ "style: the element it sits on is still compared"
       "<a style=\"color: inherit\" href=\"u\">t</a>" "<a style=\"color: inherit\" href=\"v\">t</a>",
     -- tabindex: a code block's tab stop is dropped, and nothing beside it
     same "tabindex: dropped" "<pre tabindex=\"0\"><code>c</code></pre>" "<pre><code>c</code></pre>",
     differ "tabindex: the code beside it is still compared"
       "<pre tabindex=\"0\"><code>c</code></pre>" "<pre tabindex=\"0\"><code>d</code></pre>",
     -- an attribute no row declares is content
     differ "attributes: hidden is a difference" "<p hidden=\"hidden\">t</p>" "<p>t</p>",
     differ "attributes: a bare hidden is a difference" "<p hidden>t</p>" "<p>t</p>",
     differ "attributes: aria-hidden is a difference" "<p aria-hidden=\"true\">t</p>" "<p>t</p>",
     differ "attributes: an attribute no row declares is a difference"
       "<p data-x=\"1\">t</p>" "<p>t</p>",
     -- inter-element whitespace: collapsed outside <pre>, compared inside it
     same "whitespace: collapsed outside pre" "<p>a\n  <em>b</em></p>" "<p>a <em>b</em></p>",
     differ "whitespace: kept inside pre" "<pre><code>a  b</code></pre>" "<pre><code>a b</code></pre>",
     -- heading level offset: the absolute tag is normalized, the relative level is not
     check "heading: offset by the base" (cn 2 "<h2>t</h2>") "<h#1>t</h#1>",
     differ "heading: a relative level still differs" "<h1>a</h1><h2>b</h2>" "<h1>a</h1><h3>b</h3>",
     -- one trailing newline in a code block: exactly one
     check "pre: one trailing newline dropped" (cn 1 "<pre><code>a\n b\n</code></pre>")
       "<pre><code>a\n b</code></pre>",
     check "pre: an inner blank line is kept" (cn 1 "<pre><code>a\n\n</code></pre>")
       "<pre><code>a\n</code></pre>",
     differ "pre: a second trailing newline still differs"
       "<pre><code>a\n\n</code></pre>" "<pre><code>a\n</code></pre>",
     -- attribute order
     same "attributes: order" "<img src=\"u\" alt=\"a\">" "<img alt=\"a\" src=\"u\">",
     differ "attributes: a value still differs" "<a href=\"u\">t</a>" "<a href=\"v\">t</a>"]
  for c in cs do
    if let some m := c then bad := bad.push m
  -- Listing tokens may split text anywhere, including immediately after a
  -- newline. Only the code block's final newline is normalized, once.
  let code (kids : Array Html.Node) : String :=
    canon 1 false (.elem "pre" #[] #[.elem "code" #[] kids])
  for (raw, want) in [("", ""), ("\n", ""), ("<\n >\n", "<\n >"),
      ("aaa\n    ```\n", "aaa\n    ```"), ("α\t\nβ\n\n", "α\t\nβ\n"),
      ("a\n b", "a\n b"), ("a\n\nb\n", "a\n\nb")] do
    let chars := raw.toList
    let expected := "<pre><code>" ++ want ++ "</code></pre>"
    for i in [:chars.length + 1] do
      let kids := #[Html.Node.text (String.ofList (chars.take i)), .text "",
        .text (String.ofList (chars.drop i)), .text ""]
      if let some m := check s!"pre: text split at {i} in {repr raw}" (code kids) expected then
        bad := bad.push m
    if let some m := check s!"pre: one node per character in {repr raw}"
        (code (chars.toArray.map fun c => .text (String.singleton c))) expected then
      bad := bad.push m
  for (name, a, b) in
      [("interior newline", #[Html.Node.text "a\n", .text "b"], #[.text "ab"]),
       ("interior blank line", #[.text "a\n", .text "\n", .text "b"], #[.text "a\nb"]),
       ("second trailing newline", #[.text "a\n", .text "\n"], #[.text "a\n"]),
       ("interior spaces", #[.text "a\n", .text "  b"], #[.text "a\n b"]),
       ("child element", #[.elem "span" #[] #[.text "a"], .text "\n"], #[.text "a\n"]),
       ("child attribute", #[.elem "span" #[("hidden", "")] #[.text "a"], .text "\n"],
         #[.elem "span" #[] #[.text "a"], .text "\n"])] do
    if code a == code b then bad := bad.push s!"pre: segmentation hid a genuine {name} difference"
  for (name, source, want) in
      [("inline code", "<p><code>a\n</code></p>", "<p><code>a\n</code></p>"),
       ("textarea", "<textarea>a\n</textarea>", "<textarea>a\n</textarea>")] do
    if let some m := check s!"{name}: final newline is not the code-block normalization"
        (cn 1 source) want then bad := bad.push m
  -- The attribute table, broken row by row in both directions: each declared
  -- drop hides its own attribute and neither the text nor a compared
  -- attribute beside it; each attribute that decides whether content reaches
  -- a reader is no row's, and is a difference on an element and on the
  -- chrome the comparison unwraps. The filter once kept six attributes and
  -- dropped every other in silence, `hidden` among them.
  for (a, _) in droppedAttrs do
    let v := if a == "class" then "x" else "0"
    for r in [same s!"{a}: dropped" s!"<p {a}=\"{v}\">t</p>" "<p>t</p>",
        differ s!"{a}: the text beside it is still compared"
          s!"<p {a}=\"{v}\">t</p>" s!"<p {a}=\"{v}\">u</p>",
        differ s!"{a}: an attribute beside it is still compared"
          s!"<a {a}=\"{v}\" href=\"u\">t</a>" s!"<a {a}=\"{v}\" href=\"w\">t</a>"] do
      if let some m := r then bad := bad.push m
  let frag (s : String) : String := canonList 1 false "" (fragmentOf (hParse s)).toList
  unless frag "<main><section id=\"s\"><p>t</p></section></main>" == "<p>t</p>" do
    bad := bad.push "chrome: a section carrying only a declared drop was not unwrapped"
  for a in readerAttrs do
    if dropsAttr a then
      bad := bad.push s!"{a}: decides whether content reaches a reader, and a row drops it"
    if let some m := differ s!"{a}: compared on an element" s!"<p {a}=\"x\">t</p>" "<p>t</p>" then
      bad := bad.push m
    if frag s!"<main><section {a}=\"x\"><p>t</p></section></main>" == frag "<main><p>t</p></main>" then
      bad := bad.push s!"{a}: a section carrying it was unwrapped"
    if frag s!"<main {a}=\"x\"><p>t</p></main>" == frag "<main><p>t</p></main>" then
      bad := bad.push s!"{a}: a main carrying it was looked through"
    if frag s!"<div {a}=\"x\"><main><p>t</p></main></div>" == frag "<div><main><p>t</p></main></div>" then
      bad := bad.push s!"{a}: an element above main carrying it was looked through"
  -- A stylesheet or a script node is compared as what it prints, never dropped.
  if canonList 1 false "" [Html.Node.style "p { color: red }"] == "" then
    bad := bad.push "a style node was dropped from the comparison"
  if canonList 1 false "" [Html.Node.script #[] "go()"] == "" then
    bad := bad.push "a script node was dropped from the comparison"
  -- The gap normalizations, used only to attribute an owed case: each hides
  -- its own gap's cost and nothing else.
  let cg (gaps : List String) (s : String) : String := canonGList gaps 1 false false "" (hParse s).toList
  let gs : List (Option String) :=
    [check "gap hr" (cg ["md:thematic-break"] "<p>a</p><hr /><p>b</p>") (cg [] "<p>a</p><p>b</p>"),
     check "gap start" (cg ["md:list-start"] "<ol start=\"3\"><li>a</li></ol>")
       (cg [] "<ol><li>a</li></ol>"),
     check "gap loose" (cg ["md:loose-list"] "<ul><li><p>a</p></li></ul>") (cg [] "<ul><li>a</li></ul>"),
     check "gap link title" (cg ["md:link-title"] "<a href=\"u\" title=\"t\">x</a>")
       (cg [] "<a href=\"u\">x</a>"),
     check "gap depth" (cg ["md:heading-depth"] "<h4>x</h4>") (cg [] "<h3>x</h3>"),
     check "gap code info" (cg ["md:code-info"] "<pre><code class=\"language-x\">c</code></pre>")
       (cg [] "<pre><code>c</code></pre>")]
  for c in gs do
    if let some m := c then bad := bad.push m
  if cg ["md:link-title"] "<a href=\"u\">x</a>" == cg ["md:link-title"] "<a href=\"v\">x</a>" then
    bad := bad.push "gap link title: it hid the destination too"
  if cg ["md:thematic-break"] "<p>a</p>" == cg ["md:thematic-break"] "<p>b</p>" then
    bad := bad.push "gap hr: it hid a paragraph's text too"
  -- Silence: a gap construct dropped with no route naming it is a fault,
  -- and naming it is exactly what clears it — each rule broken once.
  let ink (base : Nat) (s : String) : GapInk := gapInkList base {} (hParse s).toList
  let sg (want got : String) (routes : Array String) : Array String :=
    silentGaps (ink 1 want) (ink 2 got) routes
  let ss : List (Option String) :=
    [check "silence: a dropped rule, unnamed"
       (toString (sg "<p>a</p><hr /><p>b</p>" "<p>a</p><p>b</p>" #[]).toList)
       "[md:thematic-break]",
     check "silence: a dropped rule, named"
       (toString (sg "<p>a</p><hr /><p>b</p>" "<p>a</p><p>b</p>" #["md:thematic-break"]).toList) "[]",
     check "silence: a start of 1 is not a start"
       (toString (sg "<ol start=\"1\"><li>a</li></ol>" "<ol><li>a</li></ol>" #[]).toList) "[]",
     check "silence: a dropped start, unnamed"
       (toString (sg "<ol start=\"3\"><li>a</li></ol>" "<ol><li>a</li></ol>" #[]).toList)
       "[md:list-start]",
     check "silence: a link title and an image title are two gaps"
       (toString (sg "<a href=\"u\" title=\"t\">x</a><img src=\"s\" title=\"t\">"
         "<a href=\"u\">x</a><img src=\"s\">" #["md:link-title"]).toList) "[md:image-title]",
     check "silence: a title lost with its link is the link's defect, not the title's"
       (toString (sg "<p><a href=\"u\" title=\"t\">x</a></p>" "<p>[x]</p>" #[]).toList) "[]",
     check "silence: a lost language named by W0110 is named"
       (toString (sg "<pre><code class=\"language-x\">c</code></pre>" "<pre><code>c</code></pre>"
         #["W0110"]).toList) "[]",
     check "silence: a lost language, unnamed"
       (toString (sg "<pre><code class=\"language-x\">c</code></pre>" "<pre><code>c</code></pre>"
         #[]).toList) "[md:code-info]",
     check "silence: a fourth-level heading set at the third, unnamed"
       (toString (sg "<h4>x</h4>" "<h4>x</h4>" #[]).toList) "[md:heading-depth]",
     check "silence: a fourth-level heading the engine sets as its own fourth is not a loss"
       (toString (sg "<h4>x</h4>" "<h5>x</h5>" #[]).toList) "[]"]
  for c in ss do
    if let some m := c then bad := bad.push m
  -- The tier rows, in the scoreboard's own format: sorted, unique, two per
  -- section, and every value an integer the shared ratchet reads. The old
  -- rows were written in spec order, which the format faults.
  let fakeEx : Array Example :=
    #[{ id := 1, section_ := "B sec", md := "", html := "" },
      { id := 2, section_ := "A sec", md := "", html := "" },
      { id := 3, section_ := "B sec", md := "", html := "" }]
  let fakeRows : Array Row :=
    #[{ id := 1, section_ := "B sec", verdict := .match_, note := "" },
      { id := 2, section_ := "A sec", verdict := .owed, note := "" },
      { id := 3, section_ := "B sec", verdict := .rejected, note := "" }]
  let rendered := Scoreboard.render #["# encoding: pairs match/cases"] (tierRows fakeEx fakeRows)
  match Scoreboard.parse rendered with
  | .error e => bad := bad.push s!"tier: the rendered rows do not parse: {e}"
  | .ok t =>
    unless (Scoreboard.validate t).isEmpty do
      bad := bad.push s!"tier: the rendered rows are malformed: {Scoreboard.validate t}"
    unless t.find? "B sec.match" == some 1 && t.find? "B sec.cases" == some 2
        && t.find? "A sec.match" == some 0 && t.find? "A sec.cases" == some 1 do
      bad := bad.push "tier: a section's match/cases pair is wrong"
    unless (t.rows.map (·.item)).toList ==
        ["A sec.cases", "A sec.match", "B sec.cases", "B sec.match"] do
      bad := bad.push "tier: rows are not sorted by item"
  -- A verdict name round-trips, and an unknown one is refused.
  for v in [Verdict.match_, .rejected, .divergence, .owed] do
    unless Verdict.ofName? v.name == some v do
      bad := bad.push s!"verdict '{v.name}' does not round-trip"
  unless (Verdict.ofName? "nearly").isNone do
    bad := bad.push "an unknown verdict name was accepted"
  -- Each verdict rule, broken once, against the pure judge. A normalization
  -- that hides a real loss is how three cases read as `match` while the run
  -- named the lost language, so the rules are mutated rather than trusted.
  let lossy := Diag.of .W0392 "m" (subject := some "md:list-start")
  let pending := Diag.of .W0307 "m" (subject := some "md:thematic-break")
  let optionLeak := Diag.of .W0110 "m"
  let unrelated := #[Diag.of .W0392 "m" (subject := some "tex:something"),
    Diag.of .W0601 "m" (subject := some "md:image")]
  unless routesOf #[lossy] == #["md:list-start"] do
    bad := bad.push "a degraded md route was not read as a loss"
  unless routesOf #[pending] == #["md:thematic-break"] do
    bad := bad.push "a pending md route was not read as a loss"
  unless routesOf #[optionLeak] == #["W0110"] do
    bad := bad.push "an option the elaborator refused was not read as a loss"
  unless (routesOf unrelated).isEmpty do
    bad := bad.push "a diagnostic outside the md routes was read as a loss"
  let r0 : Refusal := ⟨"md:raw-html", 1, 1⟩
  let jv (want got wantG gotG : String) (rs : Array (Refusal × Bool)) (routes : Array String) :=
    judge want got wantG gotG rs routes none
  unless jv "a" "a" "a" "a" #[] #[] == (.match_, "") do
    bad := bad.push "judge: agreeing trees with no loss are not a match"
  unless jv "a" "a" "a" "a" #[] #["md:list-start"] == (.owed, "blocked-by:md:list-start") do
    bad := bad.push "judge: agreeing trees under a named loss are not owed with the gap"
  unless jv "a" "b" "a" "a" #[] #["md:link-title"] == (.owed, "blocked-by:md:link-title") do
    bad := bad.push "judge: a case the gap alone blocks is not attributed to it"
  unless jv "a" "b" "a" "c" #[] #["md:link-title"] == (.owed, "") do
    bad := bad.push "judge: a case the gap does not explain was attributed to it"
  unless jv "a" "b" "a" "b" #[] #[] == (.owed, "") do
    bad := bad.push "judge: a gap normalization applied with no route named"
  unless jv "x" "y" "x" "y" #[(r0, true)] #[] == (.rejected, "refused:md:raw-html") do
    bad := bad.push "judge: a corroborated refusal is not rejected"
  unless jv "x" "y" "x" "y" #[(r0, true), (⟨"md:indented-code", 2, 1⟩, false)] #[]
      == (.owed, "uncorroborated:md:indented-code") do
    bad := bad.push "judge: one uncorroborated refusal still read as rejected"
  unless jv "x" "x" "x" "x" #[(r0, false)] #[] == (.owed, "uncorroborated:md:raw-html") do
    bad := bad.push "judge: an uncorroborated refusal on agreeing trees was not owed"
  unless jv "\"q\"" "\u201cq\u201d" "" "" #[] #[] == (.owed, smartNote) do
    bad := bad.push "judge: a smart-punctuation-only difference lost its note"
  -- Corroboration comes from the spec's expected HTML, never from the reader:
  -- the refused text passes through verbatim, or it was not raw HTML.
  let ex (md html : String) : Example := { id := 9, section_ := "S", md, html }
  unless refusedPrefix "a <b>x</b> c\n" 1 3 == "<b>" do
    bad := bad.push s!"prefix: '{refusedPrefix "a <b>x</b> c\n" 1 3}'"
  unless refusedPrefix "<div id=\"x\"\n*hi*\n" 1 1 == "<div id=\"x\"" do
    bad := bad.push "prefix: a tag with no > on its line does not stop at the line end"
  unless refusedPrefix "<a\nhref=\"u\">x\n" 1 1 == "<a\nhref=\"u\">" do
    bad := bad.push "prefix: a tag continued onto the next line is not read to its >"
  unless corroborated #[] (ex "a <b>x</b>\n" "<p>a <b>x</b></p>\n") ⟨"md:raw-html", 1, 3⟩ do
    bad := bad.push "corroboration: a tag the spec passes through was not corroborated"
  if corroborated #[] (ex "[x]:\n<my url>\n" "<p><a href=\"my%20url\">x</a></p>\n")
      ⟨"md:raw-html", 2, 1⟩ then
    bad := bad.push "corroboration: a link destination the spec reads as a URL corroborated a refusal"
  if corroborated #[] (ex "x <y z\n" "<p>x &lt;y z</p>\n") ⟨"md:raw-html", 1, 3⟩ then
    bad := bad.push "corroboration: text the spec escapes corroborated a refusal"
  unless corroborated #[(9, "md:indented-code")] (ex "    x\n" "") ⟨"md:indented-code", 1, 1⟩ do
    bad := bad.push "corroboration: a reviewed indented-code row was not read"
  if corroborated #[(8, "md:indented-code")] (ex "    x\n" "") ⟨"md:indented-code", 1, 1⟩ then
    bad := bad.push "corroboration: another case's reviewed row corroborated this one"
  if corroborated #[(9, "md:indented-code")] (ex "x\n" "") ⟨"md:lazy-continuation", 1, 1⟩ then
    bad := bad.push "corroboration: a reviewed row for one class corroborated another"
  -- The reviewed list: a malformed row is refused rather than skipped.
  match parseReviewed "7\tmd:indented-code\tthe item's content is indented code\n" with
  | .ok rs => unless rs == #[(7, "md:indented-code")] do bad := bad.push "reviewed: row misread"
  | .error e => bad := bad.push s!"reviewed: {e}"
  if (parseReviewed "7\tmd:raw-html\tx\n").toOption.isSome then
    bad := bad.push "reviewed: a raw-HTML row was accepted, but the expected HTML corroborates those"
  if (parseReviewed "7\tmd:indented-code\t\n").toOption.isSome then
    bad := bad.push "reviewed: a row with no reason was accepted"
  if (parseReviewed "7\tmd:indented-code\ta\n7\tmd:indented-code\tb\n").toOption.isSome then
    bad := bad.push "reviewed: a duplicate row was accepted"
  unless strictSubjects.length == 3 do
    bad := bad.push s!"strict classes: {strictSubjects.length}, want 3"
  for s in strictSubjects do
    unless s.startsWith "md:" do bad := bad.push s!"strict subject '{s}' is not an md subject"
  -- The smart-punctuation map, in the direction the classifier uses it.
  let sm : List (Option String) :=
    [check "unsmarten dash" (unsmarten "a\u2013b") "a--b",
     check "unsmarten em dash" (unsmarten "a\u2014b") "a---b",
     check "unsmarten ellipsis" (unsmarten "a\u2026") "a...",
     check "unsmarten quotes" (unsmarten "\u201cq\u201d") "\"q\"",
     check "unsmarten apostrophe" (unsmarten "it\u2019s") "it's",
     check "unsmarten leaves plain text" (unsmarten "plain --- text") "plain --- text"]
  for c in sm do
    if let some m := c then bad := bad.push m
  -- The tables parse, and a malformed row is refused rather than skipped.
  match parseVerdicts "1\tSec\tmatch\n2\tSec\towed\tnote\n" with
  | .error e => bad := bad.push s!"verdict table: {e}"
  | .ok rs =>
    unless rs.size == 2 do bad := bad.push s!"verdict table: {rs.size} rows, want 2"
  if (parseVerdicts "1\tSec\tnearly\n").toOption.isSome then
    bad := bad.push "verdict table: an unknown verdict parsed"
  if bad.isEmpty then
    IO.println "commonmark --selftest: ok"
    return 0
  for b in bad do IO.eprintln s!"commonmark --selftest: {b}"
  return 1

def report (exs : Array Example) (rows : Array Row) : IO Unit := do
  let (m, r, d, o) := counts rows
  IO.println s!"cases {exs.size}: match {m}, rejected {r}, divergence {d}, owed {o}"
  let pend := (rows.filter (·.note == smartNote)).size
  let blocked := (rows.filter (·.note.startsWith "blocked-by:")).size
  let uncorr := (rows.filter (·.note.startsWith "uncorroborated:")).size
  IO.println s!"  pending decision (smart punctuation): {pend} cases, all owed"
  IO.println s!"  blocked by a named IR gap: {blocked} cases, all owed"
  IO.println s!"  refused without corroboration (reader defects): {uncorr} cases, all owed"
  for (g, ids) in gapReport rows do
    IO.println s!"  gap {g} blocks {ids.size}: {ids.toList}"
  for sec in sectionsOf exs do
    let ss := rows.filter (·.section_ == sec)
    let (m, r, d, o) := counts ss
    IO.println s!"  {sec}: {ss.size} cases — match {m}, rejected {r}, divergence {d}, owed {o}"

def printStrict (js : Array Judged) : IO Unit := do
  for (s, n, c) in strictTouch js do
    IO.println s!"  strict class {s}: {n} cases, {c} with every such refusal corroborated"

/-- The committed inputs every mode reads: the vendored spec, gated on its
content key, and the reviewed list. -/
def loadInputs : IO (Except String (Array Example × Array (Nat × String))) := do
  unless ← System.FilePath.pathExists specPath do
    return .error s!"commonmark: {specPath} is missing"
  let got ← keyOf specPath
  unless got == specKey do
    return .error s!"commonmark: {specPath} has content key {got}, expected {specKey}"
  let exs := readExamples (← IO.FS.readFile specPath)
  unless exs.size == 652 do
    return .error s!"commonmark: read {exs.size} examples, expected 652"
  match ← readReviewed with
  | .ok rv => return .ok (exs, rv)
  | .error e => return .error s!"commonmark: {e}"

/-- The three tier modes, shared with every other tier through
`Scoreboard.tierMain`, plus the verdict table this tier owns. Regeneration
writes the verdict table only after the tier was written: when the tier
refuses a fall no `# lowered:` line authorises, neither file changes. -/
def run (args : List String) : IO UInt32 := do
  let (exs, reviewed) ← match ← loadInputs with
    | .ok v => pure v
    | .error e => return ← die 1 e
  let t0 ← IO.monoMsNow
  let (rows, js) := classifyAll exs reviewed
  let ms := (← IO.monoMsNow) - t0
  -- The reviewed list in its other direction, in every mode: a stale row is
  -- a fault, never a note.
  let stale := staleReviewed exs js reviewed
  for s in stale do IO.eprintln s!"commonmark: {s}"
  -- Silence, in every mode: a gap construct the expected page carries and
  -- the engine's page drops unnamed is a reader defect, never a verdict.
  -- Reported beside the stale rows rather than after them, so one run
  -- names every fault.
  let silent := (exs.zip js).filter (!·.2.silent.isEmpty)
  for (e, j) in silent do
    IO.eprintln s!"commonmark: case {e.id} ({e.section_}) drops {j.silent.toList} and names nothing"
  unless stale.isEmpty && silent.isEmpty do
    return ← die 1 s!"commonmark: {stale.size} stale reviewed rows, \
{silent.size} cases drop a gap construct in silence"
  let tier (a : List String) : IO UInt32 :=
    Scoreboard.tierMain "commonmark" (.pairs "match" "cases")
      (pure (tierProvenance exs rows, tierRows exs rows)) selftest a
  if args.contains "--check" then
    unless ← System.FilePath.pathExists verdictPath do
      return ← die 1 s!"commonmark: {verdictPath} is missing; regenerate it"
    let committed ← match parseVerdicts (← IO.FS.readFile verdictPath) with
      | .ok rs => pure rs
      | .error e => return ← die 1 s!"commonmark: {verdictPath}: {e}"
    let mut bad : Array String := #[]
    for r in rows do
      match committed.find? (·.id == r.id) with
      | none => bad := bad.push s!"case {r.id} has no committed verdict"
      | some c =>
        unless c.verdict == r.verdict do
          bad := bad.push
            s!"case {r.id} ({r.section_}): {r.verdict.name}, committed {c.verdict.name}"
        -- The note is part of the verdict, checked in both directions: a
        -- case parked on a pending dialect decision or on a named loss must
        -- not quietly become a `match`, and a case must not acquire a note
        -- nobody reviewed.
        unless c.note == r.note do
          bad := bad.push
            s!"case {r.id} ({r.section_}): note '{r.note}', committed '{c.note}'"
    for c in committed do
      unless rows.any (·.id == c.id) do
        bad := bad.push s!"committed case {c.id} is not in the spec"
    for b in bad do IO.eprintln s!"commonmark: {b}"
    report exs rows
    printStrict js
    let rc ← tier ["--check"]
    unless bad.isEmpty do
      return ← die 1 s!"commonmark: {bad.size} verdict findings"
    if rc != 0 then return rc
    IO.println s!"commonmark --check: ok ({ms} ms)"
    return 0
  let rc ← tier []
  if rc != 0 then
    return ← die rc s!"commonmark: the tier was not written, so neither is {verdictPath}"
  IO.FS.writeFile verdictPath (verdictText rows)
  report exs rows
  printStrict js
  IO.println s!"commonmark: wrote {verdictPath} and {tierPath} ({ms} ms)"
  return 0

/-- One case's judgement in full: the two canonical forms, the refusals with
where the reader put them and whether anything outside the reader agrees,
the routes, and the diagnostics. -/
def explainOne (ex : Example) (j : Judged) : IO Unit := do
  IO.println s!"case {ex.id} ({ex.section_}): {j.verdict.name}\
{if j.note.isEmpty then "" else "  [" ++ j.note ++ "]"}"
  IO.println s!"  md   {ex.md.replace "\n" "\\n"}"
  IO.println s!"  want {j.want}"
  IO.println s!"  got  {j.got}"
  for (r, ok) in j.refusals do
    let p := (refusedPrefix ex.md r.line r.col).replace "\n" "\\n"
    IO.println s!"  refusal {r.subject} at {r.line}:{r.col} \
{if ok then "corroborated" else "NOT corroborated"}{if r.subject == "md:raw-html" then " by '" ++ p ++ "'" else ""}"
  unless j.routes.isEmpty do IO.println s!"  routes {j.routes.toList}"

/-- **Scaling as a gate.** Every shape runs at 1×, 2× and 4× of a base size,
and a doubling of the input may not more than `scalingBound` the time. The
inline phase was quadratic — 3.8× per doubling, 31.8 s for one 64 KB
paragraph of `*a*` against 0.9 s for the same content as tex — and nothing
noticed, because the spec's one-construct examples are all a few bytes
long. The first version of this gate then measured only matched shapes at
4–16 KB, and seven quadratic scans sat outside it: unclosed `<!--` took
133 s at 78 KB.

So the shapes start from cmark's own pathological suite
(`test/pathological_tests.py`), plus block-phase shapes, at sizes where a
quadratic term outweighs the constant. The reader phase is timed twice per
size and the minimum kept; the whole path once. Two phases: the reader and
its desugaring alone (`Md.read`), which this gate owns and fails on, and the
whole path through the elaborator and the HTML backend, which it reports —
a whole-path non-linearity with a linear reader belongs to another module.

Not in `lake test`: it measures wall-clock on a shared host, so it is a deep
oracle run when the reader is touched, like `kp-fuzz` for line breaking. -/
def scalingBound : Float := 2.6

/-- The base size, in bytes, of every shape's 1× document. -/
def scalingBase : Nat := 8192

/-- `unit` repeated until the document reaches `bytes`. -/
def repeatTo (unit : String) (bytes : Nat) : String := Id.run do
  let u := max unit.length 1
  let mut s := ""
  for _ in [0:bytes / u + 1] do s := s ++ unit
  return s ++ "\n"

/-- `pre` repeated, `mid`, then `post` repeated, the whole reaching `bytes`. -/
def nestTo (pre mid post : String) (bytes : Nat) : String := Id.run do
  let n := bytes / (max (pre.length + post.length) 1)
  let mut a := ""
  let mut b := ""
  for _ in [0:n] do
    a := a ++ pre
    b := b ++ post
  return a ++ mid ++ b ++ "\n"

/-- Backtick strings of rising length, `e` between them, until `bytes`. -/
def ticksTo (bytes : Nat) : String := Id.run do
  let mut s := ""
  let mut len := 0
  let mut k := 1
  for _ in [0:bytes] do
    if len ≥ bytes then break
    s := s ++ "e" ++ String.ofList (List.replicate k '`')
    len := len + k + 1
    k := k + 1
  return s ++ "\n"

/-- List items indented one level deeper each line, until `bytes`. -/
def deepListTo (bytes : Nat) : String := Id.run do
  let mut s := ""
  let mut len := 0
  let mut k := 0
  for _ in [0:bytes] do
    if len ≥ bytes then break
    s := s ++ String.ofList (List.replicate (2 * k) ' ') ++ "* a\n"
    len := len + 2 * k + 4
    k := k + 1
  return s

/-- The shapes, each a function of the target size in bytes. The inline
shapes are one paragraph each; the pathological ones are cmark's. -/
def scalingShapes : List (String × (Nat → String)) :=
  [("emphasis", repeatTo "*a* "), ("code spans", repeatTo "`a` "),
   ("links", repeatTo "[a](b) "), ("nested brackets", repeatTo "[[a]] "),
   ("open brackets", repeatTo "[a "), ("delimiter runs", repeatTo "*a_b* "),
   ("plain words", repeatTo "word "),
   -- cmark's pathological suite
   ("emph closers, no openers", repeatTo "a_ "),
   ("emph openers, no closers", repeatTo "_a "),
   ("link closers, no openers", repeatTo "a]"),
   ("link openers, no closers", repeatTo "[a"),
   ("mismatched openers and closers", repeatTo "*a_ "),
   ("openers and closers multiple of 3", fun n => "a**b" ++ repeatTo "c* " n),
   ("link openers and emph closers", repeatTo "[ a_"),
   ("[ (]( repeated", repeatTo "[ (]("),
   ("![[]() repeated", repeatTo "![[]()"),
   ("nested brackets, one deep run", nestTo "[" "a" "]"),
   ("nested strong emphasis", nestTo "*a **a " "b" " a** a*"),
   ("backticks of rising length", ticksTo),
   ("unclosed links A", repeatTo "[a](<b"),
   ("unclosed links B", repeatTo "[a](b"),
   ("unclosed paren titles", repeatTo "[a](b ("),
   ("unclosed <!--", fun n => "</" ++ repeatTo "<!--" n),
   ("unclosed <?", repeatTo "a <?"),
   ("unclosed <!X", repeatTo "a <!A "),
   ("unclosed <![CDATA[", repeatTo "a <![CDATA["),
   ("unclosed autolinks", repeatTo "<a"),
   -- block phase
   ("nested block quotes", nestTo "> " "a" ""),
   ("deeply nested lists", deepListTo),
   ("many list items", repeatTo "- a\n"),
   ("many quote lines", repeatTo "> a\n"),
   ("many headings", fun n => Id.run do
      -- Distinct titles: identical ones measure the HTML backend's anchor
      -- claim, which probes `a`, `a-2`, … per heading.
      let mut s := ""
      for k in [0:n / 8 + 1] do s := s ++ s!"# a{k}\n"
      return s),
   ("many fences", repeatTo "```\na\n```\n"),
   ("many paragraphs", repeatTo "a\n\n")]

/-- The minimum of `runs` timings of `f` on the document an `IO.Ref` holds,
in nanoseconds. Read through the ref after the clock starts, so the work
cannot be hoisted out of the timed region. -/
def timeMin (src : String) (f : String → Nat) (runs : Nat := 2) : IO Nat := do
  let ref ← IO.mkRef src
  let mut best : Nat := 0
  for k in [0:runs] do
    let t0 ← IO.monoNanosNow
    let s ← ref.get
    let r := f s
    if r == 0xFFFFFFFFFFFF then IO.println ""
    let t1 ← IO.monoNanosNow
    if k == 0 || t1 - t0 < best then best := t1 - t0
  return best

def scaling (only : String) : IO UInt32 := do
  let mut bad : Array String := #[]
  let reader : String → Nat := fun s => (Md.read "case.md" s).1.size
  let whole : String → Nat := fun s => (engineFragment s).1.size
  for (name, doc) in scalingShapes do
    unless only.isEmpty || containsSub name only do continue
    let mut rt : Array Nat := #[]
    let mut wt : Array Nat := #[]
    for mult in [1, 2, 4] do
      let src := doc (scalingBase * mult)
      rt := rt.push (← timeMin src reader)
      wt := wt.push (← timeMin src whole 1)
    let ratios (t : Array Nat) : Float × Float :=
      ((Float.ofNat ((t[1]?).getD 1)) / (Float.ofNat (max ((t[0]?).getD 1) 1)),
       (Float.ofNat ((t[2]?).getD 1)) / (Float.ofNat (max ((t[1]?).getD 1) 1)))
    let (r12, r24) := ratios rt
    let (w12, w24) := ratios wt
    let ms (t : Array Nat) (k : Nat) : Nat := ((t[k]?).getD 0) / 1000000
    IO.println s!"  {name}: reader {ms rt 0}/{ms rt 1}/{ms rt 2} ms ({r12}, {r24}); \
whole {ms wt 0}/{ms wt 1}/{ms wt 2} ms ({w12}, {w24})"
    (← IO.getStdout).flush
    -- A sub-2 ms denominator is noise, not a measurement: only judge a
    -- ratio whose denominator is large enough to mean something.
    let judge (phase : String) (t : Array Nat) (a b : Float) : Array String := Id.run do
      let mut out : Array String := #[]
      if (t[0]?).getD 0 ≥ 2000000 && a > scalingBound then
        out := out.push s!"{name} ({phase}): 1x→2x is {a}×, over {scalingBound}×"
      if (t[1]?).getD 0 ≥ 2000000 && b > scalingBound then
        out := out.push s!"{name} ({phase}): 2x→4x is {b}×, over {scalingBound}×"
      return out
    bad := bad ++ judge "reader" rt r12 r24
    for w in judge "whole path" wt w12 w24 do
      IO.println s!"  report, not gated: {w}"
  if bad.isEmpty then
    IO.println "commonmark --scaling: ok"
    return 0
  for b in bad do IO.eprintln s!"commonmark --scaling: {b}"
  return 1

def main (argv : List String) : IO UInt32 := do
  match argv with
  | ["--selftest"] => selftest
  | ["--scaling"] => scaling ""
  | ["--scaling", only] => scaling only
  | ["--check"] => run ["--check"]
  | ["--explain", idS] =>
    -- Why one case earned its verdict. A report mode, not a gate — it
    -- writes nothing.
    let some id := idS.toNat? | return ← die 2 "commonmark: --explain needs a case number"
    let (exs, reviewed) ← match ← loadInputs with
      | .ok v => pure v
      | .error e => return ← die 1 e
    let some ex := exs.find? (·.id == id) | return ← die 2 s!"commonmark: no case {id}"
    explainOne ex (classify measuredBase reviewed ex)
    let (_, ds) := engineFragment ex.md
    for d in ds do
      IO.println s!"  {d.code} {d.message}{match d.span with
        | some sp => s!" @{sp.pos.line}:{sp.pos.col}" | none => ""}"
    return 0
  | ["--audit"] =>
    -- Every case a strict refusal or a route touches, explained: what a
    -- human reviewing the strict list reads. A report mode; writes nothing.
    let (exs, reviewed) ← match ← loadInputs with
      | .ok v => pure v
      | .error e => return ← die 1 e
    let (_, js) := classifyAll exs reviewed
    for (ex, j) in exs.zip js do
      unless j.refusals.isEmpty && j.routes.isEmpty do explainOne ex j
    return 0
  | [] => run []
  | _ =>
    IO.eprintln "usage: commonmark [--check | --selftest | --scaling [shape] | --explain <case> | --audit]"
    return 2
