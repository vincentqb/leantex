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
  modulo the normalizations declared in `normalizations` below.
* `rejected` — the strict dialect refuses the construct by design (an
  `E0390`), which is this dialect's answer to that case and not a defect.
* `divergence` — a deliberate difference, listed in `divergences` with its
  reason. Adding a row here is a dialect decision, never a code change's
  side effect.
* `owed` — the engine does not do this yet. Not a pass and not an excuse:
  the ratchet lets this number fall and never rise.

The ratchet is the tier file `tests/scoreboard/commonmark.tsv`: one row per
spec section, value = cases matching. A value may not drop and a baselined
section may not disappear (`# retired:` is the only exit). Hermetic —
`--check` reads the vendored spec and the committed tables, nothing else.

Comparison is over *trees*, not strings: the engine's HTML is a typed tree
already, and the spec's expected HTML is read by the tolerant reader below
into the same shape, then both are canonicalized by `canon`. A string
comparison would report the two emitters' indentation as content.
-/
import LeanTex

open LeanTex.Core

def specPath : String := "tests/commonmark/spec-0.31.2.txt"
def verdictPath : String := "tests/commonmark/verdicts.tsv"
def tierPath : String := "tests/scoreboard/commonmark.tsv"

/-- The sha256 the provenance file records, restated here so a swapped
input file fails the run rather than silently reclassifying every case. -/
def specSha : String :=
  "257c41ad946f7a1414a499aca402a1aa8fdac3678532266611348c1cf54f4b80"

-- ## The declared normalizations
--
-- Each one is a difference the comparison is blind to, with the reason it
-- is not a difference in what the construct means. A loose normalization
-- hides a real defect, so the list is short and every entry names what it
-- would hide.

def normalizations : List (String × String) :=
  [("document chrome",
    "a spec example is a fragment; the engine emits a document. The \
comparison reads the content of <main> and unwraps the <section> elements \
the sectioning walk builds. Hides: nothing about a construct — but it would \
hide a construct that failed to reach <main> at all, which is why an empty \
engine tree never counts as a match."),
   ("class and id attributes",
    "the engine generates ids from heading text and classes from its token \
system; the spec's expected HTML carries class=\"language-x\" on a fenced \
block. Both are anchoring and styling. Hides: the fenced block's info \
string, which has its own routed diagnostic (md:code-info) so the loss is \
named rather than forgotten."),
   ("style attributes",
    "the engine sets style=\"color: inherit\" on a link from its palette. \
Styling, not content. Hides: nothing a spec example states."),
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
-- is over trees and the failure report is readable. Attributes are kept
-- only where a spec example states them as content.

def keptAttrs : List String := ["href", "src", "alt", "title", "start", "type"]

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
whether whitespace is significant here. -/
def canon (base : Nat) (pre : Bool) (n : Html.Node) : String :=
  match n with
  | .text s => if pre then dropOneTrailingNewline s else squeeze s
  | .style _ => ""
  | .script _ _ => ""
  | .elem tag attrs kids =>
    let tag' :=
      match hLevelTag? tag with
      | some l => "h#" ++ toString (if l ≥ base then l - base + 1 else 1)
      | none => tag
    let keep := (attrs.filter (fun a => keptAttrs.contains a.1)).qsort (·.1 < ·.1)
    let as := keep.foldl (fun s a => s ++ " " ++ a.1 ++ "=" ++ a.2) ""
    let pre' := pre || Html.preserveTags.contains tag
    if Html.voidTags.contains tag then "<" ++ tag' ++ as ++ ">"
    else "<" ++ tag' ++ as ++ ">" ++ canonList base pre' "" kids.toList
      ++ "</" ++ tag' ++ ">"

def canonList (base : Nat) (pre : Bool) (acc : String) : List Html.Node → String
  | [] => acc
  | k :: rest => canonList base pre (acc ++ canon base pre k) rest

end

-- The engine's page reduced to the fragment a spec example is about: the
-- content of `<main>`, with the sectioning walk's `<section>` wrappers
-- unwrapped. Each walk is a one-node function plus its `List` companion
-- with an accumulator, which is what makes the recursion structural over a
-- tree whose children are an `Array`.

mutual

def unwrapOne (out : Array Html.Node) (n : Html.Node) : Array Html.Node :=
  match n with
  | .elem "section" _ kids => unwrapList out kids.toList
  | _ => out.push n

def unwrapList (out : Array Html.Node) : List Html.Node → Array Html.Node
  | [] => out
  | n :: rest => unwrapList (unwrapOne out n) rest

end

mutual

def mainOf? (n : Html.Node) : Option (Array Html.Node) :=
  match n with
  | .elem "main" _ kids => some kids
  | .elem _ _ kids => mainList? kids.toList
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

/-- One markdown source through the reader, the desugaring, the one
elaborator and the HTML backend: the fragment tree and the diagnostics. -/
def engineFragment (src : String) : Array Html.Node × Array Diag :=
  let (raws, readDiags) := Md.read "case.md" src
  let (doc, diags) := Elab.runRaws "case.md" raws readDiags
  let (_, body, htmlDiags) := HtmlDoc.emitTree {} doc
  let content := (mainList? body.toList).getD body
  (unwrapList #[] content.toList, diags ++ htmlDiags)

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

/-- The verdict one case earns, and the two canonical forms behind it. A
refusal outranks a comparison: where the dialect says no, that *is* the
answer, and comparing trees afterwards would report the refusal as a
defect. -/
def classify (base : Nat) (ex : Example) : Verdict × String × String :=
  -- The spec's own base is 1 (`#` is `<h1>`); the engine's is measured.
  -- Subtracting one number from both sides collapsed h1 and h2 to the same
  -- ordinal and reported every two-level heading document as owed.
  let want := canonList 1 false "" (hParse ex.html).toList
  let (ns, diags) := engineFragment ex.md
  let got := canonList base false "" ns.toList
  if diags.any (·.kind == .E0390) then (.rejected, want, got)
  else if (divergences.find? (·.1 == ex.id)).isSome then (.divergence, want, got)
  else if want == got then (.match_, want, got)
  else (.owed, want, got)


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

def parseTier (text : String) : Except String (Array (String × Nat) × Array String) := do
  let mut out : Array (String × Nat) := #[]
  let mut retired : Array String := #[]
  for raw in text.splitOn "\n" do
    let line := raw.trimAsciiEnd.toString
    if line.isEmpty then continue
    if line.startsWith "# retired:" then
      retired := retired.push ((line.toList.drop "# retired:".length |> String.ofList).trimAscii.toString)
      continue
    if line.startsWith "#" then continue
    let fs := fields line
    let some k := fs[0]? | throw s!"tier row with no item: {line}"
    let some vS := fs[1]? | throw s!"tier row with no value: {line}"
    let some v := vS.toNat? | throw s!"tier value is not a number: {line}"
    out := out.push (k, v)
  return (out, retired)

/-- Section order as the spec states it, so the tier file and the report
read in document order rather than alphabetically. -/
def sectionsOf (exs : Array Example) : Array String := Id.run do
  let mut out : Array String := #[]
  for e in exs do
    unless out.contains e.section_ do out := out.push e.section_
  return out

def tierText (exs : Array Example) (rows : Array Row) (sha : String) : String := Id.run do
  let mut s := "# CommonMark spec cases matching, one row per spec section.\n"
  s := s ++ "# Higher is better; a value may not drop and a row may not disappear.\n"
  s := s ++ s!"# spec: 0.31.2 sha256 {sha}\n"
  s := s ++ s!"# cases: {exs.size}\n"
  for sec in sectionsOf exs do
    let n := (rows.filter (fun r => r.section_ == sec && r.verdict == .match_)).size
    s := s ++ sec ++ "\t" ++ toString n ++ "\n"
  return s

def verdictText (rows : Array Row) : String := Id.run do
  let mut s := "# One row per CommonMark 0.31.2 spec example: id, section, verdict, note.\n"
  s := s ++ "# verdicts: match | rejected | divergence | owed.\n"
  s := s ++ "# `rejected` is the strict dialect refusing the construct by design (E0390);\n"
  s := s ++ "# `divergence` needs a row in `divergences` in scripts/commonmark.lean;\n"
  s := s ++ "# `owed` is not implemented yet and the ratchet lets it only fall.\n"
  s := s ++ "# This file is written only by scripts/commonmark.lean.\n"
  for r in rows do
    s := s ++ toString r.id ++ "\t" ++ r.section_ ++ "\t" ++ r.verdict.name
      ++ (if r.note.isEmpty then "" else "\t" ++ r.note) ++ "\n"
  return s

-- ## The modes

def sha256Of (path : String) : IO String := do
  let out ← IO.Process.output { cmd := "sha256sum", args := #[path] }
  return ((out.stdout.splitOn " ").headD "").trimAscii.toString

def counts (rows : Array Row) : Nat × Nat × Nat × Nat :=
  ((rows.filter (·.verdict == .match_)).size,
   (rows.filter (·.verdict == .rejected)).size,
   (rows.filter (·.verdict == .divergence)).size,
   (rows.filter (·.verdict == .owed)).size)

def classifyAll (exs : Array Example) : Array Row × Array (Nat × String × String) :=
  Id.run do
  let base := measuredBase
  let mut rows : Array Row := #[]
  let mut diffs : Array (Nat × String × String) := #[]
  for e in exs do
    let (v, want, got) := classify base e
    let note := match v with
      | .divergence => ((divergences.find? (·.1 == e.id)).map (·.2)).getD ""
      | _ => ""
    rows := rows.push { id := e.id, section_ := e.section_, verdict := v, note }
    unless v == .match_ do diffs := diffs.push (e.id, want, got)
  return (rows, diffs)

def die (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln msg
  return code

/-- The three strict classes, and how many spec cases each one touches:
measured by running every case and reading the subject its refusal carried,
not asserted. -/
def strictTouch (exs : Array Example) : Array (String × Nat) := Id.run do
  let subjects := ["md:raw-html", "md:indented-code", "md:lazy-continuation"]
  let mut counts : Array Nat := Array.replicate subjects.length 0
  for e in exs do
    let (_, diags) := engineFragment e.md
    for (s, k) in subjects.zipIdx do
      if diags.any (fun d => d.kind == .E0390 && d.subject == some s) then
        counts := counts.set! k ((counts[k]?).getD 0 + 1)
  return (subjects.zipIdx.map (fun (s, k) => (s, (counts[k]?).getD 0))).toArray

def checkRatchet (old new : Array (String × Nat)) (retired : Array String) :
    Array String := Id.run do
  let mut bad : Array String := #[]
  for (k, v) in old do
    match new.find? (·.1 == k) with
    | none =>
      unless retired.contains k do
        bad := bad.push s!"section '{k}' disappeared from the tier (baseline {v})"
    | some (_, v') =>
      if v' < v then bad := bad.push s!"section '{k}': {v'} matching, baseline {v}"
  return bad

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
  -- The HTML reader and the canonical form.
  let cs : List (Option String) :=
    [check "canon p" (canonList 1 false "" (hParse "<p>a <em>b</em></p>").toList)
       "<p>a <em>b</em></p>",
     check "canon void" (canonList 1 false "" (hParse "<p>a<br />b</p>").toList)
       "<p>a<br>b</p>",
     check "canon entity" (canonList 1 false "" (hParse "<p>&amp;&#65;</p>").toList)
       "<p>&A</p>",
     check "canon attrs"
       (canonList 1 false "" (hParse "<a class=\"x\" href=\"u\">t</a>").toList)
       "<a href=u>t</a>",
     check "canon pre"
       (canonList 1 false "" (hParse "<pre><code>a\n b\n</code></pre>").toList)
       "<pre><code>a\n b</code></pre>",
     check "canon pre keeps an inner blank line"
       (canonList 1 false "" (hParse "<pre><code>a\n\n</code></pre>").toList)
       "<pre><code>a\n</code></pre>",
     check "canon heading" (canonList 2 false "" (hParse "<h2>t</h2>").toList)
       "<h#1>t</h#1>",
     check "canon void container"
       (canonList 1 false "" (hParse "<p>a<br>b</p>").toList) "<p>a<br>b</p>"]
  for c in cs do
    if let some m := c then bad := bad.push m
  -- The ratchet, broken once in each direction.
  let old : Array (String × Nat) := #[("A", 3), ("B", 1)]
  unless (checkRatchet old #[("A", 2), ("B", 1)] #[]).size == 1 do
    bad := bad.push "ratchet: a drop was not caught"
  unless (checkRatchet old #[("A", 3)] #[]).size == 1 do
    bad := bad.push "ratchet: a disappearance was not caught"
  unless (checkRatchet old #[("A", 3)] #["B"]).isEmpty do
    bad := bad.push "ratchet: a retired row was still reported"
  unless (checkRatchet old #[("A", 9), ("B", 1)] #[]).isEmpty do
    bad := bad.push "ratchet: a rise was reported as a regression"
  -- A verdict name round-trips, and an unknown one is refused.
  for v in [Verdict.match_, .rejected, .divergence, .owed] do
    unless Verdict.ofName? v.name == some v do
      bad := bad.push s!"verdict '{v.name}' does not round-trip"
  unless (Verdict.ofName? "nearly").isNone do
    bad := bad.push "an unknown verdict name was accepted"
  -- The tables parse, and a malformed row is refused rather than skipped.
  match parseVerdicts "1\tSec\tmatch\n2\tSec\towed\tnote\n" with
  | .error e => bad := bad.push s!"verdict table: {e}"
  | .ok rs =>
    unless rs.size == 2 do bad := bad.push s!"verdict table: {rs.size} rows, want 2"
  if (parseVerdicts "1\tSec\tnearly\n").toOption.isSome then
    bad := bad.push "verdict table: an unknown verdict parsed"
  if (parseTier "A\tnotanumber\n").toOption.isSome then
    bad := bad.push "tier table: a non-numeric value parsed"
  if bad.isEmpty then
    IO.println "commonmark --selftest: ok"
    return 0
  for b in bad do IO.eprintln s!"commonmark --selftest: {b}"
  return 1

def report (exs : Array Example) (rows : Array Row) : IO Unit := do
  let (m, r, d, o) := counts rows
  IO.println s!"cases {exs.size}: match {m}, rejected {r}, divergence {d}, owed {o}"
  for sec in sectionsOf exs do
    let ss := rows.filter (·.section_ == sec)
    let (m, r, d, o) := counts ss
    IO.println s!"  {sec}: {ss.size} cases — match {m}, rejected {r}, divergence {d}, owed {o}"

def run (check : Bool) : IO UInt32 := do
  unless ← System.FilePath.pathExists specPath do
    return ← die 1 s!"commonmark: {specPath} is missing"
  let got ← sha256Of specPath
  unless got == specSha do
    return ← die 1 s!"commonmark: {specPath} is sha256 {got}, expected {specSha}"
  let text ← IO.FS.readFile specPath
  let exs := readExamples text
  unless exs.size == 652 do
    return ← die 1 s!"commonmark: read {exs.size} examples, expected 652"
  let t0 ← IO.monoMsNow
  let (rows, _) := classifyAll exs
  let ms := (← IO.monoMsNow) - t0
  if check then
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
    for c in committed do
      unless rows.any (·.id == c.id) do
        bad := bad.push s!"committed case {c.id} is not in the spec"
    unless ← System.FilePath.pathExists tierPath do
      return ← die 1 s!"commonmark: {tierPath} is missing; regenerate it"
    let (oldTier, retired) ← match parseTier (← IO.FS.readFile tierPath) with
      | .ok t => pure t
      | .error e => return ← die 1 s!"commonmark: {tierPath}: {e}"
    let newTier := (sectionsOf exs).map fun sec =>
      (sec, (rows.filter (fun r => r.section_ == sec && r.verdict == .match_)).size)
    bad := bad ++ checkRatchet oldTier newTier retired
    unless bad.isEmpty do
      for b in bad do IO.eprintln s!"commonmark: {b}"
      return ← die 1 s!"commonmark: {bad.size} findings"
    report exs rows
    IO.println s!"commonmark --check: ok ({ms} ms)"
    return 0
  IO.FS.writeFile verdictPath (verdictText rows)
  IO.FS.writeFile tierPath (tierText exs rows got)
  report exs rows
  let touch := strictTouch exs
  for (s, n) in touch do
    IO.println s!"  strict class {s}: {n} cases"
  IO.println s!"commonmark: wrote {verdictPath} and {tierPath} ({ms} ms)"
  return 0

def main (argv : List String) : IO UInt32 := do
  match argv with
  | ["--selftest"] => selftest
  | ["--check"] => run true
  | ["--explain", idS] =>
    -- Why one case earned its verdict: the two canonical forms side by
    -- side. A report mode, not a gate — it writes nothing.
    let some id := idS.toNat? | return ← die 2 "commonmark: --explain needs a case number"
    let text ← IO.FS.readFile specPath
    let exs := readExamples text
    let some ex := exs.find? (·.id == id) | return ← die 2 s!"commonmark: no case {id}"
    let base := measuredBase
    let (v, want, got) := classify base ex
    IO.println s!"case {id} ({ex.section_}): {v.name}"
    IO.println s!"  md   {ex.md.replace "\n" "\\n"}"
    IO.println s!"  want {want}"
    IO.println s!"  got  {got}"
    let (_, ds) := engineFragment ex.md
    for d in ds do IO.println s!"  {d.code} {d.message}"
    return 0
  | [] => run false
  | _ =>
    IO.eprintln "usage: commonmark [--check | --selftest | --explain <case>]"
    return 2
