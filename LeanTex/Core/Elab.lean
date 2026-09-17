import LeanTex.Core.Lex
import LeanTex.Core.Parse
import LeanTex.Core.Ir
import LeanTex.Core.Dim
import LeanTex.Core.Decl
import LeanTex.Core.Compat

namespace LeanTex.Core.Elab

open LeanTex.Core LeanTex.Core.Parse LeanTex.Core.Ir LeanTex.Core.Dim

inductive ParamType where
  | text
  | content
  deriving Repr, BEq

structure Param where
  name : String
  type : ParamType
  optional : Bool
  deriving Repr, BEq

structure UserCmd where
  name : String
  params : Array Param
  body : Array Raw
  deriving Repr, BEq

/-- A user command sees only commands defined before it: `limit` bounds the
visible prefix of `user`. That rule is what makes expansion terminate. -/
structure Ctx where
  file : String
  user : Array UserCmd := #[]
  limit : Nat := 0
  args : Array (String × Option (Array Inline)) := #[]
  /-- Palette names usable as colour commands, from `\palette`. -/
  palette : Palette := {}
  /-- Named lengths from `\tokens`. -/
  tokens : Tokens := {}
  /-- Inside mono/verbatim content, where punctuation stays literal. -/
  literalText : Bool := false
  /-- The document class is `slides`: `\maketitle` makes a title frame. -/
  slides : Bool := false

structure ESt where
  diags : Array Diag := #[]
  /-- Warn-once keys already fired: a macro used forty times is one problem,
  not forty. Keys are namespaced (`env:`, `ctrl:`, `palette:`) so an
  environment and a command sharing a name cannot silence each other. -/
  warnedUnknown : Array String := #[]
  /-- `\title` / `\subtitle` / `\author` / `\institute` / `\date`, wherever
  they appear — beamer documents declare them in the body — read back by
  `\maketitle` and, as plain text, by the PDF metadata fallback. -/
  title : Option (Array Inline) := none
  subtitle : Option (Array Inline) := none
  author : Option (Array Inline) := none
  institute : Option (Array Inline) := none
  date : Option (Array Inline) := none

abbrev EM := StateM ESt

private def diag (ctx : Ctx) (code msg : String) (pos : Option Pos)
    (help : Option String := none) (sev : Severity := .error) : EM Unit :=
  modify fun st => { st with diags := st.diags.push {
    severity := sev
    code := code
    message := msg
    span := pos.map (⟨ctx.file, ·⟩)
    help := help
  } }

/-- A warning deduplicated by `key`: the same unsupported construct in forty
frames is one problem, not forty. -/
private def warnOnce (ctx : Ctx) (key code msg : String) (pos : Pos)
    (help : Option String := none) : EM Unit := do
  unless (← get).warnedUnknown.contains key do
    modify fun st => { st with warnedUnknown := st.warnedUnknown.push key }
    diag ctx code msg (some pos) help .warning

def reservedCtrl : List (String × String) :=
  [("vspace", "M3"), ("noindent", "M3"),
   ("fontfallback", "M8"), ("figure", "M8"), ("note", "M5")]

/-- Declarations that take a `{...}` block and are handled in the preamble. -/
def declCtrl : List String :=
  ["page", "pdfmeta", "assert", "fonts", "palette", "tokens", "style", "output"]

/-- Preamble declarations that take one group of *inline content* rather than
a key/value block: running head and foot. -/
def runningCtrl : List String := ["runninghead", "runningfoot"]

def pageKeys : List String :=
  ["size", "width", "height", "margin", "vmargin", "hmargin", "leading", "parskip"]

def metaKeys : List String := ["title", "author", "subject", "keywords"]

def fontKeys : List String := ["body", "sans", "mono", "rm", "sf", "tt", "dir"]

/-- Named page sizes, in sp. -/
def pageSizes : List (String × (Sp × Sp)) :=
  [("letter", (pt 612, pt 792)),
   ("legal", (pt 612, pt 1008)),
   ("a4", (Dim.pt 595, Dim.pt 842)),
   ("a5", (Dim.pt 420, Dim.pt 595))]

def reservedEnv : List (String × String) :=
  [("external", "M8"), ("tikzpicture", "M8")]

/-- Math environments: their body is math source, carried whole. The engine
emits math as source until M6, and elaborating `&` and `\\` as text would
shred exactly the alignment the author wrote. -/
def mathEnvs : List String :=
  ["align", "align*", "equation", "equation*", "gather", "gather*", "displaymath"]

/-- Title-page declarations, storable from the preamble or the body. -/
def titleCtrls : List String :=
  ["title", "subtitle", "author", "institute", "date"]

/-- Preamble file markers, spliced around an `\input`'s declarations so the
flat preamble walk knows which file it is reading. `@` never lexes into a
control word, so no document can forge one. -/
private def fileMarker (f : String) : String := "@file:" ++ f

private def fileMarkerFile? (name : String) : Option String :=
  if name.startsWith "@file:" then some ((name.drop "@file:".length).toString)
  else none

def argStyles : List (String × Style) :=
  [("textbf", .bold), ("textit", .italic), ("texttt", .mono), ("emph", .emph)]

def declStyles : List (String × Style) :=
  [("bfseries", .bold), ("itshape", .italic), ("ttfamily", .mono),
   ("scshape", .smallcaps), ("sffamily", .sans), ("sans", .sans),
   ("normalfont", .normal)] ++
  (["tiny", "scriptsize", "footnotesize", "small", "normalsize", "large",
    "Large", "LARGE", "huge", "Huge"].map fun n => (n, Style.size n))

def escapes : List (String × String) :=
  [("%", "%"), ("{", "{"), ("}", "}"), ("$", "$"), ("&", "&"), ("#", "#"),
   ("_", "_"), ("~", "~"), (" ", " "),
   -- Control-symbol spaces, TeX's spelling. Fixed widths, so they are text.
   (",", "\u2009"), (":", "\u2005"), (";", "\u2004")]

def blockOnly : List String :=
  ["section", "subsection", "subsubsection", "item", "documentclass", "define",
   "block"]

def builtinNames : List String :=
  ["begin", "end", "par", "define", "ifgiven", "documentclass", "textcolor",
   -- Underline is native; a document's own \varul (soul-style) is ignored.
   "underline", "uline", "ul", "varul"] ++
  blockOnly ++ (escapes.map (·.1)) ++ (argStyles.map (·.1)) ++
  (declStyles.map (·.1)) ++ (reservedCtrl.map (·.1)) ++ declCtrl ++
  (Lex.textSymbols.map (·.1))

private def lookupUser (ctx : Ctx) (name : String) : Option (Nat × UserCmd) := Id.run do
  let mut k := ctx.limit
  for _ in [0:ctx.limit] do
    k := k - 1
    if h : k < ctx.user.size then
      if ctx.user[k].name == name then
        return some (k, ctx.user[k])
  return none

-- Best-effort source text of raw content (math bodies, class options).
-- Structural recursion through `List`; the outer call trims, and so does each
-- nested group, matching what the elaborator has always emitted.

private def isSpace : Raw → Bool
  | .space => true
  | _ => false

private def isSpaceOrPar : Raw → Bool
  | .space => true
  | .par _ => true
  | _ => false

/-- The one forward walk over sibling raws: the index past the run
satisfying `p`. Every scan here — spaces, the junk after a malformed
argument, an edge trim — is this walk; a caller's intent is its predicate,
never a hand-rolled loop of its own. -/
private def spanRaws (raws : Array Raw) (i : Nat) (p : Raw → Bool) : Nat := Id.run do
  let mut j := i
  for _ in [i:raws.size] do
    if h : j < raws.size then
      if p raws[j] then j := j + 1 else break
    else break
  return j

/-- The backward companion: the index before the trailing run satisfying `p`. -/
private def spanRawsEnd (raws : Array Raw) (p : Raw → Bool) : Nat := Id.run do
  let mut b := raws.size
  for _ in [0:raws.size] do
    match raws[b - 1]? with
    | some r => if b > 0 && p r then b := b - 1 else break
    | none => break
  return b

private def skipSpaces (raws : Array Raw) (i : Nat) : Nat :=
  spanRaws raws i isSpace

/-- The array between its edge runs of `p`. -/
private def trimBy (raws : Array Raw) (p : Raw → Bool) : Array Raw :=
  raws.extract (spanRaws raws 0 p) (spanRawsEnd raws p)

/-- Drop whitespace at both edges: a define body's braces delimit, the
padding inside them is not content. -/
private def trimRaws (raws : Array Raw) : Array Raw :=
  trimBy raws isSpaceOrPar

/-- The run an unclosed `[` still owns: tokens on its command's own line —
the stop-at-the-anchor's-line rule, stated once. A raw on a later line, or
any construct (a control word, an environment, verbatim, a paragraph
break), is the author's next thing, never consumed with the junk. A group
or math on the anchor's line counts as junk only where no group can be the
argument the author wrote (`groups := true`, a skipped configuration
command); elsewhere a group ends the run, because it may be that argument. -/
private def malformedRun (raws : Array Raw) (i : Nat) (anchor : Pos)
    (groups : Bool) : Nat :=
  spanRaws raws i fun r =>
    match r with
    | .space => true
    | .word _ p | .sym _ p => p.line == anchor.line
    | .group _ p | .math _ _ p => groups && p.line == anchor.line
    | _ => false


private def allText (xs : Array Inline) : Bool :=
  xs.all fun x => match x with
    | .text _ => true
    | _ => false

/-- Typographic punctuation, applied to ordinary text. `--` and `---` are the
dashes an author means when they type them; `...` is an ellipsis; straight
quotes become the directional pair, chosen by what precedes them (so an
apostrophe in "don't" closes). Literal text (mono, verbatim) is exempt — that
is where a straight quote is the point. -/
def smartPunct (s : String) : String :=
  String.ofList (go s.toList [])
where
  /-- `prev` is the output so far, reversed: its head is the character just
  emitted, which is what decides quote direction. -/
  go : List Char → List Char → List Char
    | [], prev => prev.reverse
    | '-' :: '-' :: '-' :: rest, prev => go rest ('—' :: prev)
    | '-' :: '-' :: rest, prev => go rest ('–' :: prev)
    | '.' :: '.' :: '.' :: rest, prev => go rest ('…' :: prev)
    | '"' :: rest, prev =>
      let opening := match prev with
        | [] => true
        | c :: _ => c == ' ' || c == '(' || c == '[' || c == '—' || c == '–'
      go rest ((if opening then '“' else '”') :: prev)
    | '\'' :: rest, prev =>
      let opening := match prev with
        | [] => true
        | c :: _ => c == ' ' || c == '(' || c == '[' || c == '“'
      go rest ((if opening then '‘' else '’') :: prev)
    | c :: rest, prev => go rest (c :: prev)

private def flushText (acc : Array Inline) (sb : String) : Array Inline :=
  if sb == "" then acc else acc.push (.text sb)

private def mergeText (xs : Array Inline) : Array Inline := Id.run do
  let mut out : Array Inline := #[]
  for x in xs do
    match x, out.back? with
    | .text s, some (.text t) =>
      out := out.pop.push (.text (t ++ s))
    | _, _ => out := out.push x
  return out

/-- What one `[...]` argument scan found. -/
inductive ArgScan where
  | took (next : Nat)
  | unclosed (bpos : Pos)
  | content

/-- The one bracket-argument scan, shared by every consumer of an optional
`[...]`. An argument's `[` opens on `anchor`'s line — a bracket on a later
line is content, where LaTeX's own argument scanning stops looking too — and
it has a matching `]`. One that never closes is malformed content, never an
argument: consuming to the end of the scan would silently drop everything
after it, a frame body or the rest of a preamble included. `.took` carries
the index past the `]`; `.unclosed` consumes nothing and carries the `[`'s
position for the caller to warn about. -/
private def scanBracketArg (raws : Array Raw) (i : Nat) (anchor : Pos) : ArgScan := Id.run do
  let j := skipSpaces raws i
  match raws[j]? with
  | some (.sym '[' bpos) =>
    if bpos.line != anchor.line then return .content
    let mut k := j + 1
    for _ in [k:raws.size] do
      if let some (.sym ']' _) := raws[k]? then
        return .took (k + 1)
      k := k + 1
    return .unclosed bpos
  | _ => return .content

/-- An unclosed `[` stays as content; this says why it was not an argument. -/
private def warnUnclosed (ctx : Ctx) (after : String) (bpos : Pos) : EM Unit :=
  diag ctx "W0310" s!"'[' after {after} never closes; it is not an argument" (some bpos)
    (help := "add the matching ']'") .warning

/-- The index of a command's `{...}` group past its optional argument, best
effort. A well-formed `[...]` is skipped whole. An unclosed one warns; its
run — the rest of the command's own line — is returned to the caller,
because W0310 just called it content: a body position renders it, and only
the preamble, where no content can live, drops it with the warning already
pointing there. The group the author wrote is then found wherever the line
break falls — this line, the next, or past a blank line — but never past
another construct. Returns the candidate index, whether it recovered from
an unclosed bracket (a recovered command with no group left is skipped with
a warning by its caller, never a fatal error), and the malformed run. -/
private def skipOptArg (ctx : Ctx) (name : String) (raws : Array Raw)
    (start : Nat) (pos : Pos) : EM (Nat × Bool × Array Raw) := do
  let j := skipSpaces raws start
  match scanBracketArg raws start pos with
  | .took k => return (skipSpaces raws k, false, #[])
  | .content => return (j, false, #[])
  | .unclosed bpos =>
    warnUnclosed ctx s!"'\\{name}'" bpos
    let e := malformedRun raws j pos (groups := false)
    let k := spanRaws raws e isSpaceOrPar
    if let some (.group _ _) := raws[k]? then
      return (k, true, raws.extract j e)
    return (e, true, raws.extract j e)

/-- The body of an unknown environment without its arguments: leading `[...]`
runs and `{...}` groups on the `\begin` line are the environment's own
arguments (`\begin{banner}{Logo}`), not content. A group or bracket on a
later line is content — LaTeX's own argument scanning stops looking there
too. Also returns the position of an unclosed `[`, for the caller to warn
about (its run is kept as content), and how many groups went with the
wrapper, for the caller to name what W0302's "body is kept" does not cover. -/
private def dropEnvArgs (body : Array Raw) (beginPos : Pos) :
    Array Raw × Option Pos × Nat := Id.run do
  let mut i := 0
  let mut dropped := 0
  for _ in [0:body.size] do
    match scanBracketArg body i beginPos with
    | .took k => i := k
    | .unclosed bpos => return (body.extract i body.size, some bpos, dropped)
    | .content =>
      let j := skipSpaces body i
      match body[j]? with
      | some (.group _ gpos) =>
        if gpos.line == beginPos.line then
          i := j + 1
          dropped := dropped + 1
        else break
      | _ => break
  return (body.extract i body.size, none, dropped)

/-- Exactly what went with an unknown wrapper: the count W0302's "its body
is kept" cannot carry. -/
private def warnDroppedArgs (ctx : Ctx) (name : String) (dropped : Nat)
    (pos : Pos) : EM Unit := do
  if dropped > 0 then
    let noun := if dropped == 1 then "group" else "groups"
    diag ctx "W0313"
      s!"{dropped} \{...} {noun} on the '\\begin\{{name}}' line went with the unknown wrapper" (some pos)
      (help := "content, not an argument? put it after the '\\begin' line") .warning

/-- A command whose group never materialised after an unclosed `[` is
dropped whole: W0310 already named the typo, and one skipped declaration
must not fail the build or bleed into the next construct as stray content. -/
private def warnSkippedDecl (ctx : Ctx) (name : String) (pos : Pos) : EM Unit :=
  diag ctx "W0312" s!"no \{...} group after '\\{name}'; it is skipped" (some pos)
    (help := s!"write \\{name}\{...}") .warning

/-- The index of the next construct after a skipped preamble command's
malformed arguments. The junk ends with the command's line, and a control
word, an environment, or a verbatim block ends it early: the author's next
declaration is never consumed with the junk, whether it follows the line or
shares it. -/
private def skipMalformedArgs (raws : Array Raw) (i : Nat) (anchor : Pos) : Nat :=
  malformedRun raws i anchor (groups := true)

/-- Skip a `[...]` run and at most one group: argument recovery after a
reserved (not yet implemented) or unknown command. Returns the next index
and, when an unclosed `[` stopped the scan, its position. -/
private def skipReservedArgs (raws : Array Raw) (i : Nat) (anchor : Pos) :
    Nat × Option Pos := Id.run do
  let mut j := i
  match scanBracketArg raws i anchor with
  | .took k => j := k
  | .unclosed bpos => return (i, some bpos)
  | .content => pure ()
  let k := skipSpaces raws j
  if let some (.group _ _) := raws[k]? then
    return (k + 1, none)
  return (j, none)

-- Inline elaboration and argument binding are mutually recursive: a call
-- site's arguments are themselves inline content. Nontermination is
-- impossible by design (a body sees only earlier definitions), but the
-- checker cannot see that yet: de-partialing is scheduled proof work.
/-- An argument read as text — a URL, a palette key — with the command's
parameters substituted: inside `\define \link(url, text) {\href{\url}...}`,
`\url` is the caller's text, not the two characters `\url`. `rawSrc` alone
would print the parameter's name. -/
private def argText (ctx : Ctx) (raws : Array Raw) : String :=
  let one (r : Raw) : String :=
    match r with
    | .ctrl n _ =>
      match ctx.args.find? (·.1 == n) with
      | some (_, some inlines) => Ir.plainText inlines
      | some (_, none) => ""
      | none => Parse.rawSrcOne r
    | _ => Parse.rawSrcOne r
  -- The same substitution one group deep: a URL is never nested further.
  let flat (r : Raw) : String :=
    match r with
    | .group body _ => "{" ++ String.join (body.toList.map one) ++ "}"
    | _ => one r
  (String.join (raws.toList.map flat)).trimAscii.toString

/-- Whether a whitespace token separates here: yes, unless the space is
already there. A group body keeps a deliberate leading space (`{ (x)}`);
a paragraph's own edges are trimmed by `mkPara`, not here. -/
private def needsSep (acc : Array Inline) (sb : String) : Bool :=
  if sb.isEmpty then
    match acc.back? with
    | some (.text t) => !t.endsWith " "
    | _ => true
  else !sb.endsWith " "

mutual

/-- Bind a user command's declared parameters from the call site. Returns the
bindings and the index just past the consumed arguments. Shared by inline and
block expansion so both bind identically. -/
partial def takeArgs (ctx : Ctx) (cmd : UserCmd) (name : String)
    (raws : Array Raw) (start : Nat) (pos : Pos) :
    EM (Array (String × Option (Array Inline)) × Nat) := do
  let mut bindings : Array (String × Option (Array Inline)) := #[]
  let mut i := start
  for p in cmd.params do
    if p.optional then
      let j := skipSpaces raws i
      match raws[j]? with
      | some (.sym '[' _) =>
        let mut body : Array Raw := #[]
        let mut k' := j + 1
        let mut closed := false
        for _ in [j:raws.size] do
          match raws[k']? with
          | some (.sym ']' _) =>
            closed := true
            k' := k' + 1
            break
          | some r' =>
            body := body.push r'
            k' := k' + 1
          | none => break
        unless closed do
          diag ctx "E0316" s!"unclosed optional argument for '\\{name}'" pos
        i := k'
        let v ← elabInlines ctx body
        if p.type == .text && !allText v then
          diag ctx "E0305" s!"parameter '{p.name}' of '\\{name}' expects text" pos
        bindings := bindings.push (p.name, some v)
      | _ =>
        bindings := bindings.push (p.name, none)
    else
      let j := skipSpaces raws i
      match raws[j]? with
      | some (.group body _) =>
        i := j + 1
        let v ← elabInlines ctx body
        if p.type == .text && !allText v then
          diag ctx "E0305" s!"parameter '{p.name}' of '\\{name}' expects text" pos
        bindings := bindings.push (p.name, some v)
      | some (.word s _) =>
        i := j + 1
        bindings := bindings.push (p.name, some #[.text s])
      | _ =>
        diag ctx "E0304" s!"missing argument '{p.name}' for '\\{name}'" pos
        bindings := bindings.push (p.name, some #[])
  return (bindings, i)

/-- Elaborate raw items as inline content. -/
partial def elabInlines (ctx : Ctx) (raws : Array Raw) : EM (Array Inline) := do
  let mut raws := raws
  let mut acc : Array Inline := #[]
  let mut sb : String := ""
  let mut i := 0
  repeat
    if h : i < raws.size then
      let r := raws[i]
      match r with
      | .word s _ =>
        sb := sb ++ s
        i := i + 1
      | .space | .par _ =>
        -- Whitespace is one separator however many tokens a splice put side
        -- by side (a run was a single token at the lexer), and a paragraph
        -- never opens with one: a leading space glue would indent the line.
        if needsSep acc sb then sb := sb.push ' '
        i := i + 1
      | .sym '[' _ =>
        sb := sb.push '['
        i := i + 1
      | .sym ']' _ =>
        sb := sb.push ']'
        i := i + 1
      | .sym '~' _ =>
        -- Every LaTeX author means a non-breaking space by `~`, and reserving
        -- it buys nothing: there is no catcode machinery here to reserve it for.
        sb := sb.push '\u00a0'
        i := i + 1
      | .sym c pos =>
        diag ctx "E0311" s!"reserved character '{c}'" pos (help := s!"escape it as '\\{c}'")
        i := i + 1
      | .math d body _ =>
        acc := flushText acc sb
        sb := ""
        acc := acc.push (.math d (rawSrc body))
        i := i + 1
      | .group body _ =>
        acc := flushText acc sb
        sb := ""
        acc := acc ++ (← elabInlines ctx body)
        i := i + 1
      | .env name body pos =>
        if let some f := Parse.inputEnvFile? name then
          i := i + 1
          acc := flushText acc sb
          sb := ""
          acc := acc ++ (← elabInlines { ctx with file := f } body)
        else if mathEnvs.contains name then
          i := i + 1
          acc := flushText acc sb
          sb := ""
          acc := acc.push (.math true (rawSrc body))
        else
        match reservedEnv.lookup name with
        | some milestone =>
          i := i + 1
          warnOnce ctx ("env:" ++ name) "W0307"
            s!"'\{{name}}' is not implemented yet; its content is not rendered" pos
            (help := s!"planned for {milestone}; see PLAN.md")
        | none =>
          warnOnce ctx ("env:" ++ name) "W0302" s!"unknown environment '\{{name}}'; its body is kept" pos
            (help := "see PLAN.md for planned environments")
          -- The arguments on the `\begin` line go with the wrapper here
          -- too: an inline unknown environment obeys the same scanner as a
          -- block one. The body splices into this very scan, so its edge
          -- spaces are ordinary separators — collapsed against the
          -- neighbours by the whitespace arm, never dropped (gluing
          -- `before` to `inner`) and never doubled.
          let (kept, unclosed, dropped) := dropEnvArgs body pos
          if let some bpos := unclosed then
            warnUnclosed ctx s!"'\\begin\{{name}}'" bpos
          warnDroppedArgs ctx name dropped pos
          raws := raws.extract 0 i ++ kept ++ raws.extract (i + 1) raws.size
      | .verb s _ =>
        -- Verbatim inside inline content: kept as mono text, spaces held as
        -- no-break spaces, lines separated by forced breaks.
        acc := flushText acc sb
        sb := ""
        acc := acc.push (.styled .mono (Ir.verbatimInlines s))
        i := i + 1
      | .ctrl name pos =>
        i := i + 1
        -- The document's own names come first: a parameter, then a defined
        -- command. Built-ins the document cannot redefine are exactly
        -- `builtinNames`, refused with W0303 at the definition; every other
        -- built-in yields to a definition, silently, as in LaTeX. Order here
        -- is the whole mechanism — a built-in tested earlier would shadow
        -- the definition without a word.
        if let some (_, binding) := ctx.args.find? (·.1 == name) then
          acc := flushText acc sb
          sb := ""
          if let some inlines := binding then
            acc := acc ++ inlines
        else if let some (k, cmd) := lookupUser ctx name then
          acc := flushText acc sb
          sb := ""
          let (bindings, j) ← takeArgs ctx cmd name raws i pos
          i := j
          let callCtx : Ctx := { ctx with limit := k, args := bindings }
          acc := acc ++ (← elabInlines callCtx cmd.body)
        else if name == "hfill" then
          acc := flushText acc sb
          sb := ""
          acc := acc.push .fill
        else if name == "\\" || name == "par" then
          -- `\\[len]` adds space after the break. The bracket must be
          -- adjacent: LaTeX skips spaces here and so swallows the `[` of a
          -- line that legitimately starts with one.
          let mut extra : SymGlue := {}
          if name == "\\" then
            if let some (.sym '[' _) := raws[i]? then
              let mut optSrc : Array Raw := #[]
              let mut k := i + 1
              for _ in [k:raws.size + 1] do
                match raws[k]? with
                | some (.sym ']' _) =>
                  k := k + 1
                  break
                | some r' =>
                  optSrc := optSrc.push r'
                  k := k + 1
                | none => break
              i := k
              let src := rawSrc optSrc
              match Decl.parseValue src ctx.tokens.entries with
              | some (.glue g) => extra := g
              | some (.dim d) => extra := { width := Dim.Length.ofSp d }
              | _ =>
                diag ctx "E0331" s!"cannot read a length from '{src}'" pos
                  (help := "lengths look like 10pt or 1.5ex, or name a token")
          acc := flushText acc sb
          sb := ""
          acc := acc.push (.linebreak extra)
          -- Whitespace after a break is the source's line ending, not content;
          -- keeping it would open the next line with a stray space.
          for _ in [i:raws.size] do
            if let some .space := raws[i]? then i := i + 1 else break
        else if let some lit := escapes.lookup name then
          sb := sb ++ lit
        else if (Lex.textSymbols.lookup name).isSome then
          -- A document may define a symbol's name for itself; its definition
          -- wins, so the symbol only fires when nothing shadows it.
          sb := sb ++ (Lex.textSymbols.lookup name).getD ""
        else if let some style := argStyles.lookup name then
          let argCtx := if style == Style.mono then { ctx with literalText := true } else ctx
          let j := skipSpaces raws i
          match raws[j]? with
          | some (.group body _) =>
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.styled style (← elabInlines argCtx body))
            i := j + 1
          | some (.word s _) =>
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.styled style #[.text s])
            i := j + 1
          | _ =>
            diag ctx "E0304" s!"'\\{name}' needs an argument" pos
        else if name == "underline" || name == "uline" then
          -- Drawn, not a face change, so not a Style: one group, like \textbf.
          let j := skipSpaces raws i
          match raws[j]? with
          | some (.group body _) =>
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.underline (← elabInlines ctx body))
            i := j + 1
          | some (.word s _) =>
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.underline #[.text s])
            i := j + 1
          | _ =>
            diag ctx "E0304" s!"'\\{name}' needs an argument" pos
        else if name == "href" || name == "link" then
          let j := skipSpaces raws i
          let j2 := skipSpaces raws (j + 1)
          match raws[j]?, raws[j2]? with
          | some (.group urlRaw _), some (.group body _) =>
            i := j2 + 1
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.link (argText ctx urlRaw) (← elabInlines ctx body))
          | some (.group urlRaw _), _ =>
            -- One argument: the URL is also the text, which is the common case
            -- for a bare link and saves writing it twice.
            i := j + 1
            let url := argText ctx urlRaw
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.link url #[.text url])
          | _, _ =>
            diag ctx "E0304" s!"'\\{name}' needs a URL group, optionally followed by text" pos
        else if name == "pagenumber" then
          acc := flushText acc sb
          sb := ""
          acc := acc.push .pageNumber
        else if name == "pagecount" then
          acc := flushText acc sb
          sb := ""
          acc := acc.push .pageCount
        else if name == "textcolor" then
          let j := skipSpaces raws i
          let j2 := skipSpaces raws (j + 1)
          match raws[j]?, raws[j2]? with
          | some (.group cname _), some (.group body _) =>
            i := j2 + 1
            let key := argText ctx cname
            match ctx.palette.find? key with
            | some c =>
              acc := flushText acc sb
              sb := ""
              acc := acc.push (.colored c (some key) (← elabInlines ctx body))
            | none =>
              -- The colour is unresolvable; the content is not. Keeping it
              -- uncoloured is the best-effort contract: a wrong colour beats
              -- a missing word.
              warnOnce ctx ("palette:" ++ key) "W0304"
                s!"'{key}' is not in the palette; content kept uncoloured" pos
                (help := if ctx.palette.entries.isEmpty then
                    "declare colours with \\palette{ name = #RRGGBB }"
                  else s!"declared: {String.intercalate ", "
                    (ctx.palette.entries.toList.map (·.1))}")
              acc := flushText acc sb
              sb := ""
              acc := acc ++ (← elabInlines ctx body)
          | _, _ =>
            diag ctx "E0304" "'\\textcolor' needs {name} and {content}" pos
        else if let some c := ctx.palette.find? name then
          -- With a group, that group is the argument: `\primary{Alex}` means
          -- colour Alex, which is what it looks like. Without one it is a
          -- declaration colouring the rest of the group, as `\bfseries` does.
          let j := skipSpaces raws i
          match raws[j]? with
          | some (.group body _) =>
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.colored c (some name) (← elabInlines ctx body))
            i := j + 1
          | _ =>
            let rest ← elabInlines ctx (raws.extract i raws.size)
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.colored c (some name) rest)
            i := raws.size
        else if let some style := declStyles.lookup name then
          let declCtx := if style == Style.mono then { ctx with literalText := true } else ctx
          let rest ← elabInlines declCtx (raws.extract i raws.size)
          acc := flushText acc sb
          sb := ""
          acc := acc.push (.styled style rest)
          i := raws.size
        else if name == "ifgiven" then
          let j := skipSpaces raws i
          let j2 := skipSpaces raws (j + 1)
          match raws[j]?, raws[j2]? with
          | some (.group cond _), some (.group tmpl _) =>
            i := j2 + 1
            let refs := cond.filter (!isSpace ·)
            match refs.toList with
            | [.ctrl pname _] =>
              match ctx.args.find? (·.1 == pname) with
              | some (_, some _) => acc := acc ++ (← elabInlines ctx tmpl)
              | some (_, none) => pure ()
              | none => diag ctx "E0306" s!"unknown parameter '\\{pname}'" pos
            | _ =>
              diag ctx "E0306" "expected a parameter reference like {\\team}" pos
          | _, _ =>
            diag ctx "E0304" "'\\ifgiven' needs {\\param} and {content}" pos
        else if let some milestone := reservedCtrl.lookup name then
          warnOnce ctx ("ctrl:" ++ name) "W0307" s!"'\\{name}' is not implemented yet; skipped" pos
            (help := s!"planned for {milestone}; see PLAN.md")
          let (j, unclosed) := skipReservedArgs raws i pos
          if let some bpos := unclosed then
            warnUnclosed ctx s!"'\\{name}'" bpos
          i := j
        else if blockOnly.contains name then
          diag ctx "E0312" s!"'\\{name}' is not allowed here" pos
            (help := "it is a block-level command: use it between paragraphs, " ++
              "not inside inline content or a command body")
        else
          -- Best effort: the arguments are content, and content is never
          -- dropped for want of a command. Only the formatting is lost.
          warnOnce ctx ("ctrl:" ++ name) "W0301"
            s!"unknown command '\\{name}'; its arguments were kept as text" pos
            (help := "define it with \\define, or see PLAN.md for planned commands")
          let mut j := skipSpaces raws i
          let mut kept := 0
          for _ in [0:9] do
            match raws[j]? with
            | some (.group body _) =>
              acc := flushText acc sb
              -- Whatever separated the arguments visually is gone with the
              -- command, so a space stands in; without one, `{a}{b}` runs
              -- together as `ab`.
              sb := if kept > 0 then " " else ""
              acc := flushText acc sb
              sb := ""
              acc := acc ++ (← elabInlines ctx body)
              kept := kept + 1
              j := skipSpaces raws (j + 1)
            | _ => break
          -- The control word swallowed the space after it; give one back so
          -- the kept text does not fuse with what follows.
          if kept > 0 && j < raws.size then
            sb := " "
          i := j
    else
      break
  let out := mergeText (flushText acc sb)
  return if ctx.literalText then out else out.map mapText
where
  /-- Applied to this level's own text only; nested bodies were processed by
  their own call, with their own literal-text setting. -/
  mapText (x : Inline) : Inline :=
    match x with
    | .text t => .text (smartPunct t)
    | other => other

end

/-- Block environments: those whose content is a block sequence. -/
def blockEnvs : List String := ["itemize", "enumerate", "center", "document", "frame"]

mutual

/-- One raw's verdict for `bodyIsBlock`; the `List` companion below carries
the walk, as everywhere a tree with `Array` children is recursed. The arms
mirror the boundary rule in `elabBlocks` — verbatim included, since it is a
first-class block on this branch — and descend into scope groups and
environment bodies: block content one group deeper is still block content.
A body that ends its own paragraph (`...\par`, the LaTeX habit for a
one-line entry) produces one, so it is a block too. -/
def bodyIsBlockOne : Raw → Bool
  | .ctrl n _ =>
    n == "block" || n == "par" || ["section", "subsection", "subsubsection"].contains n
  | .par _ => true
  | .verb _ _ => true
  | .env n body _ =>
    if (Parse.inputEnvFile? n).isSome then bodyIsBlockList body.toList
    else
      blockEnvs.contains n || mathEnvs.contains n
        || n == "tabular" || n == "tabular*"
        || (reservedEnv.lookup n).isSome || bodyIsBlockList body.toList
  | .group body _ => bodyIsBlockList body.toList
  | _ => false

def bodyIsBlockList : List Raw → Bool
  | [] => false
  | r :: rest => bodyIsBlockOne r || bodyIsBlockList rest

end

/-- Does this body produce block-level content? Decides whether a user command
called between paragraphs expands as blocks or as inline content. A purely
inline macro must stay inline, or `\role{Ada} and more text` would split the
paragraph. -/
def bodyIsBlock (raws : Array Raw) : Bool :=
  bodyIsBlockList raws.toList

private def sectionLevel : String → Option Nat
  | "section" => some 1
  | "subsection" => some 2
  | "subsubsection" => some 3
  | _ => none

/-- A declaration standing in a group applies to the rest of the group:
`\Huge`, `\bfseries`, a palette name used bare. -/
private def isDeclaration (ctx : Ctx) : Raw → Bool
  | .ctrl n _ => (declStyles.lookup n).isSome || (ctx.palette.find? n).isSome
  | _ => false

private def isParRaw : Raw → Bool
  | .par _ => true
  | .ctrl "par" _ => true
  | _ => false

/-- Is a group here an argument? It is when, looking back over spaces and
earlier argument groups, a control word or an `[option]` precedes it; a group
standing on its own is a scope. -/
private def isArgument (cur : Array Raw) : Bool := Id.run do
  let mut k := cur.size
  for _ in [0:cur.size] do
    match cur[k - 1]? with
    | some .space => k := k - 1
    | some (.group _ _) => k := k - 1
    | some (.ctrl _ _) => return true
    | some (.sym ']' _) => return true
    | _ => return false
  return false

/-- `\par` ends a paragraph wherever it stands, a scope group included:
`{A \par B}` is `{A}\par{decls B}`, the declarations active at the break
re-applied to what follows. So `{\Huge Title \par}` sets one line and stops,
where a forced break would have set an empty Huge line after it. A part that
holds only declarations and space sets nothing and is dropped. -/
private def splitAtPars (ctx : Ctx) (body : Array Raw) (pos : Pos) : Array Raw := Id.run do
  let hasContent (rs : Array Raw) : Bool :=
    rs.any fun r => !(isSpaceOrPar r || isDeclaration ctx r)
  let mut out : Array Raw := #[]
  let mut decls : Array Raw := #[]
  let mut pre : Array Raw := #[]
  for r in body do
    if isParRaw r then
      if hasContent pre then
        out := out.push (.group pre pos)
      out := out.push r
      pre := decls
    else
      if isDeclaration ctx r then
        decls := decls.push r
      pre := pre.push r
  if hasContent pre then
    out := out.push (.group pre pos)
  return out

private def mkPara (ctx : Ctx) (cur : Array Raw) : EM (Option Block) := do
  let mut cur := cur
  repeat
    match cur.back? with
    | some .space => cur := cur.pop
    | some (.par _) => cur := cur.pop
    | _ => break
  if cur.isEmpty then
    return none
  let mut inlines ← elabInlines ctx cur
  -- A spliced body can leave a leading space no raw-level skip saw; a
  -- paragraph never opens with a space glue.
  if let some (Inline.text s) := inlines[0]? then
    if s.startsWith " " then
      let t := String.ofList (s.toList.dropWhile (· == ' '))
      if t.isEmpty then
        inlines := inlines.extract 1 inlines.size
      else
        inlines := inlines.modify 0 fun _ => .text t
  -- A forced break at the very end says what the paragraph end already
  -- says; kept, it is an empty line in the PDF and an empty row in HTML.
  repeat
    match inlines.back? with
    | some (.linebreak _) => inlines := inlines.pop
    | some (.text s) =>
      if s.trimAscii.isEmpty then inlines := inlines.pop
      else
        -- ...and a spliced body's trailing space is the same edge case as
        -- the leading one above.
        if s.endsWith " " then
          let t := String.ofList ((s.toList.reverse.dropWhile (· == ' ')).reverse)
          inlines := inlines.pop.push (.text t)
        break
    | _ => break
  return if inlines.isEmpty then none else some (.para inlines)

/-- Store one `\title`-family declaration; `\maketitle` reads them back.
Returns the index just past the consumed arguments, and the malformed run
of an unclosed optional argument for the caller to keep where content can
live. -/
private def takeTitleDecl (ctx : Ctx) (name : String) (raws : Array Raw)
    (start : Nat) (pos : Pos) : EM (Nat × Array Raw) := do
  -- `\title[short]{long}`: the short form feeds furniture we do not render.
  -- Past an unclosed `[`, the group the author wrote is still there —
  -- wherever the line break falls — and best effort takes it as the
  -- argument rather than failing the build.
  let (j, recovered, junk) ← skipOptArg ctx name raws start pos
  match raws[j]? with
  | some (.group body _) =>
    let content ← elabInlines ctx body
    modify fun st => match name with
      | "title" => { st with title := some content }
      | "subtitle" => { st with subtitle := some content }
      | "author" => { st with author := some content }
      | "institute" => { st with institute := some content }
      | _ => { st with date := some content }
    return (j + 1, junk)
  | _ =>
    if recovered then
      warnSkippedDecl ctx name pos
      return (j, junk)
    diag ctx "E0304" s!"'\\{name}' needs a \{...} group" pos
    return (start, #[])

/-- The title content `\maketitle` sets, from what was declared. A declared
but empty part (`\date{}`) is deliberately blank and sets nothing. -/
private def titleBlocks (st : ESt) : Array Block :=
  let add (inner : Array Block) (v : Option (Array Inline))
      (wrap : Array Inline → Array Inline) : Array Block :=
    match v with
    | some xs => if xs.isEmpty then inner else inner.push (.para (wrap xs))
    | none => inner
  let inner := add #[] st.title fun t => #[.styled (.size "LARGE") #[.styled .bold t]]
  let inner := add inner st.subtitle fun s => #[.styled (.size "large") s]
  let inner := add inner st.author id
  let inner := add inner st.institute fun i => #[.styled (.size "small") i]
  add inner st.date id

/-- Elaborate raw items as a block sequence. -/
partial def elabBlocks (ctx : Ctx) (raws : Array Raw) : EM (Array Block) := do
  let mut blocks : Array Block := #[]
  let mut cur : Array Raw := #[]
  let mut raws := raws
  let mut i := 0
  repeat
    if h : i < raws.size then
      let r := raws[i]
      -- A scope group holding a paragraph end is spliced open first, so the
      -- `\par` inside it is the boundary it is everywhere else.
      if let .group body pos := r then
        if body.any isParRaw && !isArgument cur then
          raws := raws.extract 0 i ++ splitAtPars ctx body pos ++ raws.extract (i + 1) raws.size
          continue
      let isBoundary : Bool :=
        match r with
        | .par _ => true
        | .ctrl "par" _ => true
        | .ctrl "block" _ => true
        | .ctrl n _ =>
          (sectionLevel n).isSome ||
          -- A user command whose body produces blocks is itself a boundary.
          (match lookupUser ctx n with
           | some (_, cmd) => bodyIsBlock cmd.body
           | none =>
             titleCtrls.contains n || n == "maketitle" || n == "titlepage")
        | .env n body _ =>
          -- The synthetic \input wrapper is provenance, not structure: an
          -- inline fragment splices into the paragraph that includes it,
          -- and only a file holding block content breaks one. An unknown
          -- environment is judged the same way — its wrapper is unknowable,
          -- so its body's shape decides, and an inline body stays in its
          -- sentence.
          if (Parse.inputEnvFile? n).isSome then bodyIsBlock body
          else
            blockEnvs.contains n || mathEnvs.contains n
              || n == "tabular" || n == "tabular*"
              || (reservedEnv.lookup n).isSome || bodyIsBlock body
        | .verb _ _ => true
        | _ => false
      if !isBoundary then
        unless cur.isEmpty && isSpaceOrPar r do
          cur := cur.push r
        i := i + 1
      else
        if !cur.isEmpty then
          if let some p ← mkPara ctx cur then
            blocks := blocks.push p
          cur := #[]
        match r with
        | .par _ =>
          i := i + 1
        | .ctrl "par" _ =>
          i := i + 1
        | .ctrl "block" pos =>
          i := i + 1
          -- \block[before = <len>]{content}
          let mut before : SymGlue := {}
          let mut j := skipSpaces raws i
          if let some (.sym '[' _) := raws[j]? then
            let mut optSrc : Array Raw := #[]
            j := j + 1
            for _ in [j:raws.size] do
              match raws[j]? with
              | some (.sym ']' _) =>
                j := j + 1
                break
              | some r' =>
                optSrc := optSrc.push r'
                j := j + 1
              | none => break
            let (opts, ds) := Decl.parseBlock ctx.file (rawSrc optSrc) pos "block"
              ctx.tokens.entries
            modify fun st => { st with diags := st.diags ++ ds }
            for e in opts do
              match e.key, e.value with
              | "before", .glue g => before := g
              | "before", .dim d => before := { width := Dim.Length.ofSp d }
              | key, v =>
                if key == "before" then
                  modify fun st => { st with
                    diags := st.diags.push (Decl.wrongType ctx.file "block" key
                      "a length" v pos) }
                else
                  modify fun st => { st with
                    diags := st.diags.push (Decl.unknownKey ctx.file "block" key
                      ["before"] pos) }
            j := skipSpaces raws j
          match raws[j]? with
          | some (.group body _) =>
            i := j + 1
            blocks := blocks.push (.spaced before (← elabBlocks ctx body))
          | _ =>
            diag ctx "E0304" "'\\block' needs a {body}" pos
        | .ctrl n pos =>
          i := i + 1
          match lookupUser ctx n with
          | some (k, cmd) =>
            -- Block-producing user command: bind its arguments, then
            -- elaborate the body as blocks so `\block` inside a definition
            -- works instead of reporting E0312.
            let (bindings, j) ← takeArgs ctx cmd n raws i pos
            i := j
            let callCtx : Ctx := { ctx with limit := k, args := bindings }
            blocks := blocks ++ (← elabBlocks callCtx cmd.body)
          | none =>
          if titleCtrls.contains n then
            let (j, junk) ← takeTitleDecl ctx n raws i pos
            i := j
            -- The malformed run of an unclosed bracket is content here.
            if let some p ← mkPara ctx junk then
              blocks := blocks.push p
          else if n == "maketitle" || n == "titlepage" then
            let inner := titleBlocks (← get)
            if inner.isEmpty then
              warnOnce ctx "ctrl:maketitle" "W0309"
                s!"'\\{n}' with nothing declared; no title is set" pos
                (help := "declare \\title{...} (and \\author, \\date, ...) before it")
            else if ctx.slides then
              blocks := blocks.push (.frame #[] #[.center inner])
            else
              blocks := blocks.push (.center inner)
          else
            let level := (sectionLevel n).getD 1
            let mut starred := false
            if let some (.word "*" _) := raws[i]? then
              starred := true
              i := i + 1
            -- `\section[short]{long}`: the short form feeds furniture we do
            -- not render, and its bracket obeys the shared scanner. The
            -- malformed run of an unclosed bracket is content here
            -- (Principle 8), exactly as in the scanner's sibling paths.
            let (j, recovered, junk) ← skipOptArg ctx n raws i pos
            if let some p ← mkPara ctx junk then
              blocks := blocks.push p
            match raws[j]? with
            | some (.group title _) =>
              i := j + 1
              blocks := blocks.push (.section level starred (← elabInlines ctx title))
            | _ =>
              if recovered then
                warnSkippedDecl ctx n pos
                i := j
              else
                diag ctx "E0304" s!"'\\{n}' needs a \{title}" pos
        | .env n body pos =>
          i := i + 1
          if let some f := Parse.inputEnvFile? n then
            -- An \input file's blocks, elaborated under its own name so a
            -- diagnostic points at the file that holds the construct.
            blocks := blocks ++ (← elabBlocks { ctx with file := f } body)
          else if mathEnvs.contains n then
            blocks := blocks.push (.para #[.math true (rawSrc body)])
          else if n == "tabular" || n == "tabular*" then
            -- Rows survive as lines, cells as fixed-space-separated content:
            -- honest degradation until real table layout, and `&` never
            -- reaches inline elaboration as a stray reserved character.
            warnOnce ctx "env:tabular" "W0308"
              "tables are not laid out yet; rows are set as plain lines" pos
              (help := "planned for M8; see PLAN.md")
            let mut k := skipSpaces body 0
            if n == "tabular*" then
              if let some (.group _ _) := body[k]? then
                k := skipSpaces body (k + 1)
            if let some (.group _ _) := body[k]? then
              k := k + 1
            let mut rows : Array (Array (Array Inline)) := #[]
            let mut cells : Array (Array Inline) := #[]
            let mut cellRaws : Array Raw := #[]
            for j in [k:body.size] do
              if h' : j < body.size then
                match body[j] with
                | .ctrl "\\" _ =>
                  cells := cells.push (← elabInlines ctx cellRaws)
                  cellRaws := #[]
                  rows := rows.push cells
                  cells := #[]
                | .sym '&' _ =>
                  cells := cells.push (← elabInlines ctx cellRaws)
                  cellRaws := #[]
                | r' => cellRaws := cellRaws.push r'
            if cellRaws.any (!isSpaceOrPar ·) || !cells.isEmpty then
              cells := cells.push (← elabInlines ctx cellRaws)
              rows := rows.push cells
            let mut content : Array Inline := #[]
            for row in rows do
              if row.any (!·.isEmpty) then
                unless content.isEmpty do
                  content := content.push (.linebreak {})
                let mut first := true
                for cell in row do
                  unless cell.isEmpty do
                    unless first do
                      content := content.push (.text "\u00a0\u00a0")
                    content := content ++ cell
                    first := false
            unless content.isEmpty do
              blocks := blocks.push (.para content)
          else if n == "frame" then
            -- \begin{frame}[options]{title}: options are burned (fragile,
            -- plain, standout say how beamer should cope, not what to say);
            -- the title group counts only when it follows directly — a
            -- paragraph break before a group makes it content, which is
            -- where LaTeX's own argument scanning stops looking too.
            let mut k := 0
            for _ in [0:body.size] do
              match scanBracketArg body k pos with
              | .took k' => k := k'
              | .unclosed bpos =>
                warnUnclosed ctx "'\\begin{frame}'" bpos
                break
              | .content => break
            k := skipSpaces body k
            let mut title : Array Inline := #[]
            if let some (.group t _) := body[k]? then
              title ← elabInlines ctx t
              k := k + 1
            -- \frametitle{...} anywhere in the frame names it too.
            let mut rest : Array Raw := #[]
            let mut j := k
            for _ in [k:body.size] do
              if h' : j < body.size then
                match body[j], body[j + 1]? with
                | .ctrl "frametitle" fpos, some (.group t _) =>
                  -- The last title wins, as in beamer, but never silently:
                  -- the author wrote two and only one can show.
                  unless title.isEmpty do
                    diag ctx "W0311" "this '\\frametitle' replaces the frame's earlier title"
                      (some fpos) (help := "the last one wins; remove the other") .warning
                  title ← elabInlines ctx t
                  j := j + 2
                | r', _ =>
                  rest := rest.push r'
                  j := j + 1
              else break
            blocks := blocks.push (.frame title (← elabBlocks ctx rest))
          else if n == "itemize" || n == "enumerate" then
            let mut items : Array (Array Raw) := #[]
            let mut curItem : Array Raw := #[]
            let mut seen := false
            let mut strayDiagged := false
            for item in body do
              match item with
              | .ctrl "item" _ =>
                if seen then
                  items := items.push curItem
                curItem := #[]
                seen := true
              | _ =>
                if seen then
                  curItem := curItem.push item
                else if !isSpaceOrPar item && !strayDiagged then
                  diag ctx "E0310" s!"content before the first '\\item'" pos
                  strayDiagged := true
            if seen then
              items := items.push curItem
            let mut elabItems : Array (Array Block) := #[]
            for it in items do
              elabItems := elabItems.push (← elabBlocks ctx it)
            blocks := blocks.push (.list (n == "enumerate") elabItems)
          else if n == "center" then
            blocks := blocks.push (.center (← elabBlocks ctx body))
          else if let some milestone := reservedEnv.lookup n then
            warnOnce ctx ("env:" ++ n) "W0307"
              s!"'\{{n}}' is not implemented yet; its content is not rendered" pos
              (help := s!"planned for {milestone}; see PLAN.md")
          else
            -- An unknown wrapper's decoration is unknowable; its body is
            -- not. The arguments on the `\begin` line go with the wrapper.
            warnOnce ctx ("env:" ++ n) "W0302" s!"unknown environment '\{{n}}'; its body is kept" pos
              (help := "see PLAN.md for planned environments")
            let (kept, unclosed, dropped) := dropEnvArgs body pos
            if let some bpos := unclosed then
              warnUnclosed ctx s!"'\\begin\{{n}}'" bpos
            warnDroppedArgs ctx n dropped pos
            blocks := blocks ++ (← elabBlocks ctx kept)
        | .verb s _ =>
          i := i + 1
          blocks := blocks.push (.verbatim s)
        | _ =>
          i := i + 1
    else
      break
  if !cur.isEmpty then
    if let some p ← mkPara ctx cur then
      blocks := blocks.push p
  return blocks

private def parseSig (ctx : Ctx) (s : String) (pos : Pos) : EM (Array Param) := do
  let s := s.trimAscii.toString
  if s == "" || s == "()" then
    return #[]
  if !(s.startsWith "(" && s.endsWith ")") then
    diag ctx "E0303" s!"malformed signature '{s}'" pos
      (help := "expected (name: type, ..., opt?: type)")
    return #[]
  let inner := (String.ofList (s.toList.drop 1).dropLast).trimAscii.toString
  if inner == "" then
    return #[]
  let mut params : Array Param := #[]
  for entry in inner.splitOn "," do
    match entry.splitOn ":" with
    | [name, ty] =>
      let name := name.trimAscii.toString
      let ty := ty.trimAscii.toString
      let optional := name.endsWith "?"
      let name := if optional then (String.ofList name.toList.dropLast).trimAscii.toString else name
      let type? : Option ParamType :=
        if ty == "text" then some .text
        else if ty == "content" then some .content
        else none
      let wellFormed := match name.toList with
        | c :: rest => c.isAlpha && rest.all Char.isAlphanum
        | [] => false
      if !wellFormed then
        diag ctx "E0303" s!"invalid parameter name '{name}'" pos
          (help := "parameter names start with a letter")
      else
        match type? with
        | some t => params := params.push ⟨name, t, optional⟩
        | none =>
          diag ctx "E0303" s!"unknown parameter type '{ty}' for '{name}'" pos
            (help := "types: text | content")
    | _ =>
      diag ctx "E0303" s!"malformed parameter '{entry.trimAscii.toString}'" pos
        (help := "expected name: type")
  return params

/-- `\page{...}`: geometry. `size` names a standard page; `width`/`height`
override it; `margin` sets both axes, `vmargin`/`hmargin` one each. -/
private def applyPage (ctx : Ctx) (spec : PageSpec) (entries : Array Decl.Entry)
    (pos : Pos) : EM PageSpec := do
  let mut spec := spec
  for e in entries do
    match e.key, e.value with
    | "size", .ident name =>
      match pageSizes.lookup name.toLower with
      | some (w, h) => spec := { spec with width := w, height := h }
      | none =>
        diag ctx "E0324" s!"unknown page size '{name}'" pos
          (help := s!"known sizes: {String.intercalate ", " (pageSizes.map (·.1))}")
    | "width", .dim d => spec := { spec with width := d }
    | "height", .dim d => spec := { spec with height := d }
    | "margin", .dim d => spec := { spec with vmargin := d, hmargin := d }
    | "vmargin", .dim d => spec := { spec with vmargin := d }
    | "hmargin", .dim d => spec := { spec with hmargin := d }
    | "leading", .int n => spec := { spec with leading := n.toNat * 1000 }
    | "leading", .dim d =>
      -- A bare decimal like 1.04 reads as a dimension in points; the factor
      -- is what was meant.
      spec := { spec with leading := (d * 1000 / pt 1).toNat }
    | "leading", .ident f =>
      -- ...and one without a unit reaches here as a name.
      match Decl.parseDecimal f with
      | some (m, s) => spec := { spec with leading := (m * 1000 / s).toNat }
      | none => diag ctx "E0323" s!"'leading' in \\page expects a factor like 1.04, got '{f}'" pos
    | "parskip", .glue g => spec := { spec with parskip := some g }
    | "parskip", .dim d => spec := { spec with parskip := some { width := Dim.Length.ofSp d } }
    | key, v =>
      if key == "header" || key == "footer" then
        -- The feature exists, just not as a page key: running content is
        -- inline content, which a key/value block cannot carry.
        let cmd := if key == "header" then "\\runninghead" else "\\runningfoot"
        diag ctx "E0327" s!"'{key}' is not a \\page key" pos
          (help := s!"declare it as {cmd}\{...} — it takes inline content, " ++
            "so use \\hfill to push part of it to the right")
      else if pageKeys.contains key then
        let expected := if key == "size" then "a page size name" else "a dimension"
        modify fun st => { st with
          diags := st.diags.push (Decl.wrongType ctx.file "page" key expected v pos) }
      else
        modify fun st => { st with
          diags := st.diags.push (Decl.unknownKey ctx.file "page" key pageKeys pos) }
  return spec

/-- `\fonts{...}`: family names per slot, and `dir`, a directory of font
files shipped beside the document. `rm`/`sf`/`tt` are accepted as aliases so
a LaTeX habit does not become an error. -/
private def applyFonts (ctx : Ctx) (spec : FontSpec) (entries : Array Decl.Entry)
    (pos : Pos) : EM FontSpec := do
  let mut spec := spec
  for e in entries do
    match e.key, e.value with
    | "body", .str f => spec := { spec with body := some f }
    | "rm", .str f => spec := { spec with body := some f }
    | "sans", .str f => spec := { spec with sans := some f }
    | "sf", .str f => spec := { spec with sans := some f }
    | "mono", .str f => spec := { spec with mono := some f }
    | "tt", .str f => spec := { spec with mono := some f }
    | "dir", .str d =>
      spec := if spec.dirs.contains d then spec else { spec with dirs := spec.dirs.push d }
    | key, v =>
      if fontKeys.contains key then
        let expected := if key == "dir" then "a quoted directory" else "a quoted family name"
        modify fun st => { st with
          diags := st.diags.push (Decl.wrongType ctx.file "fonts" key expected v pos) }
      else
        modify fun st => { st with
          diags := st.diags.push (Decl.unknownKey ctx.file "fonts" key fontKeys pos) }
  return spec

/-- `\tokens{...}`: named lengths. Entries are walked one at a time so a
token may be defined by scaling an earlier one (`sep = 0.6 * rhythm`);
parsing the block in one shot would leave those references unresolved. -/
private def applyTokens (ctx : Ctx) (toks : Tokens) (src : String) (pos : Pos) :
    EM Tokens := do
  let mut acc : Array (String × SymGlue) := toks.entries
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | none =>
      diag ctx "E0320" s!"invalid entry in \\tokens: {entry.quote}" pos
        (help := "entries look like: name = length")
    | some (key, valueSrc) =>
      match Decl.parseValue valueSrc acc with
      | some (.glue g) => acc := acc.push (key, g)
      | some (.dim d) => acc := acc.push (key, { width := Dim.Length.ofSp d })
      | some v =>
        modify fun st => { st with
          diags := st.diags.push (Decl.wrongType ctx.file "tokens" key
            "a length (10pt, 1.5ex, 0.6 * other)" v pos) }
      | none =>
        diag ctx "E0321" s!"cannot read length for '{key}': {valueSrc.quote}" pos
          (help := "lengths look like 10pt, 1.5ex, 2em, or 0.6 * other-token")
  return { entries := acc }

def styleKeys : List String :=
  ["font", "before", "after", "rule", "marker", "indent", "gap"]

/-- `\style{element}{...}`: how an element kind looks. `font` and `marker`
are inline content and elaborate as such; the rest are lengths and a palette
colour. A length may name a token, so the entries are read one at a time
against the tokens declared so far. -/
private def applyStyle (ctx : Ctx) (styles : Styles) (element src : String) (pos : Pos) :
    EM Styles := do
  unless styleableElements.contains element do
    diag ctx "E0328" s!"'{element}' is not a styleable element" pos
      (help := s!"elements: {String.intercalate ", " styleableElements}")
    return styles
  let mut st : ElementStyle := (styles.find? element).getD {}
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | none =>
      diag ctx "E0320" s!"invalid entry in \\style: {entry.quote}" pos
        (help := "entries look like: key = value")
    | some (key, valueSrc) =>
      let asInline : EM (Option (Array Inline)) := do
        let inner := if valueSrc.startsWith "{" && valueSrc.endsWith "}" && valueSrc.length ≥ 2
          then (valueSrc.drop 1).dropEnd 1 |>.toString else valueSrc
        let (toks, _) := Lex.lex ctx.file inner
        let (raws, _) := Parse.parse ctx.file toks
        -- Value text re-enters through the same door as the document, idiom
        -- translation included, or a \color inside a font spec would leak.
        let (raws, ds) := Compat.rewrite ctx.file raws
        modify fun st => { st with diags := st.diags ++ ds.filter (·.severity != .note) }
        return some (← elabInlines ctx raws)
      let asLength : EM (Option SymGlue) := do
        match Decl.parseValue valueSrc ctx.tokens.entries with
        | some (.glue g) => return some g
        | some (.dim d) => return some { width := Dim.Length.ofSp d }
        | _ =>
          diag ctx "E0321" s!"cannot read length for '{key}' in \\style: {valueSrc.quote}" pos
            (help := "lengths look like 10pt, 1.5ex, or a token name")
          return none
      match key with
      | "font" => st := { st with font := ← asInline }
      | "marker" => st := { st with marker := ← asInline }
      | "before" => st := { st with before := ← asLength }
      | "after" => st := { st with after := ← asLength }
      | "indent" => st := { st with indent := ← asLength }
      | "gap" => st := { st with gap := ← asLength }
      | "rule" =>
        match ctx.palette.find? valueSrc with
        | some c => st := { st with rule := some (c, some valueSrc) }
        | none =>
          match Decl.parseValue valueSrc with
          | some (.color r g b) => st := { st with rule := some (⟨r, g, b⟩, none) }
          | _ => diag ctx "E0326" s!"'{valueSrc}' is not in the palette" pos
      | _ =>
        modify fun st' => { st' with
          diags := st'.diags.push (Decl.unknownKey ctx.file "style" key styleKeys pos) }
  let rest := styles.entries.filter (·.1 != element)
  return { entries := rest.push (element, st) }

/-- `\palette{...}`: named colours. Every entry becomes usable both as
`\textcolor{name}{...}` and as a bare `\name` declaration. -/
private def applyPalette (ctx : Ctx) (pal : Palette) (entries : Array Decl.Entry)
    (pos : Pos) : EM Palette := do
  let mut pal := pal
  for e in entries do
    match e.value with
    | .color r g b =>
      if builtinNames.contains e.key then
        diag ctx "E0303" s!"palette name '{e.key}' collides with a built-in command" pos
      else
        pal := { pal with entries := pal.entries.push (e.key, ⟨r, g, b⟩) }
    | .ident other =>
      -- An alias, so two names that must never drift apart share one value.
      match pal.find? other with
      | some c => pal := { pal with entries := pal.entries.push (e.key, c) }
      | none =>
        diag ctx "E0326" s!"'{other}' is not in the palette" pos
          (help := "declare it first; aliases read earlier entries")
    | v =>
      modify fun st => { st with
        diags := st.diags.push (Decl.wrongType ctx.file "palette" e.key
          "a color like #7C3AED" v pos) }
  return pal

/-- `\output{...}`: what to build, so a document needs no CLI options.
`formats` takes a bare comma list (`formats = pdf, html`), so entries are
walked by hand: an entry without `=` continues the list. -/
private def applyOutput (ctx : Ctx) (o0 : OutputSpec) (src : String) (pos : Pos) :
    EM OutputSpec := do
  let mut o := o0
  let mut inFormats := false
  let addFormat (o : OutputSpec) (f : String) : EM OutputSpec := do
    if ["pdf", "html"].contains f then
      return { o with
        formats := if o.formats.contains f then o.formats else o.formats.push f }
    diag ctx "E0321" s!"'{f}' is not an output format" pos
      (help := some "formats: pdf, html")
    return o
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | some ("formats", v) =>
      inFormats := true
      o ← addFormat o v
    | some ("css", v) =>
      inFormats := false
      if ["own", "bulma", "none"].contains v then
        o := { o with css := some v }
      else
        diag ctx "E0321" s!"'{v}' is not a stylesheet mode" pos
          (help := some "css: own | bulma | none")
    | some (key, _) =>
      inFormats := false
      modify fun st => { st with
        diags := st.diags.push (Decl.unknownKey ctx.file "output" key
          ["formats", "css"] pos) }
    | none =>
      if inFormats then
        o ← addFormat o entry
      else
        diag ctx "E0320" s!"invalid entry in \\output: {entry.quote}" pos
          (help := some "entries look like: formats = pdf, html")
  return o

/-- `\pdfmeta{...}`: PDF document information. -/
private def applyMeta (ctx : Ctx) (m0 : Meta) (entries : Array Decl.Entry)
    (pos : Pos) : EM Meta := do
  let mut m := m0
  for e in entries do
    match e.key, e.value with
    | "title", .str s => m := { m with title := some s }
    | "author", .str s => m := { m with author := some s }
    | "subject", .str s => m := { m with subject := some s }
    | "keywords", .str s => m := { m with keywords := some s }
    | key, v =>
      if metaKeys.contains key then
        modify fun st => { st with
          diags := st.diags.push (Decl.wrongType ctx.file "pdfmeta" key "a string" v pos) }
      else
        modify fun st => { st with
          diags := st.diags.push (Decl.unknownKey ctx.file "pdfmeta" key metaKeys pos) }
  return m

private def cmpOp : String → Option CmpOp
  | "==" => some .eq
  | "=" => some .eq
  | "!=" => some .ne
  | "<=" => some .le
  | "<" => some .lt
  | ">=" => some .ge
  | ">" => some .gt
  | _ => none

/-- `\assert{ ... }`: a layout invariant, checked against the shipped page
tree. Grammar is deliberately tiny: `pages <op> N`, or `fonts.all_embedded`. -/
private def parseAssert (ctx : Ctx) (src : String) (pos : Pos) : EM (Option Assertion) := do
  let words := (src.splitOn " ").filterMap fun w =>
    let t := w.trimAscii.toString
    if t.isEmpty then none else some t
  let fail (why : String) : EM (Option Assertion) := do
    diag ctx "E0325" s!"cannot read assertion: {src.trimAscii.toString.quote}" pos
      (help := some why)
    return none
  match words with
  | ["fonts.all_embedded"] => return some ⟨.fontsAllEmbedded, some ⟨ctx.file, pos⟩⟩
  | ["pages", op, n] =>
    match cmpOp op, n.toInt? with
    | some o, some v => return some ⟨.pages o v, some ⟨ctx.file, pos⟩⟩
    | none, _ => fail s!"'{op}' is not a comparison (== != <= < >= >)"
    | _, none => fail s!"'{n}' is not a whole number"
  | _ => fail "supported forms: pages <op> N, fonts.all_embedded"

/-- Elaborate the whole document: split preamble and body around the
`document` environment, process declarations, then the body. -/
def elabDoc (file : String) (raws : Array Raw) : EM Doc := do
  let docIdx := raws.findIdx? fun r =>
    match r with
    | .env "document" _ _ => true
    | _ => false
  let (preamble, body, trailing) :=
    match docIdx with
    | some idx =>
      let bodyRaws := match raws[idx]! with
        | .env _ b _ => b
        | _ => #[]
      (raws.extract 0 idx, bodyRaws, raws.extract (idx + 1) raws.size)
    | none => (#[], raws, #[])
  let mut preamble := preamble
  let mut ctx : Ctx := { file := file }
  let mut docClass := "article"
  let mut classOptions := ""
  let mut page : PageSpec := {}
  let mut fonts : FontSpec := {}
  let mut palette : Palette := {}
  let mut tokens : Tokens := {}
  let mut head : Option (Array Inline) := none
  let mut foot : Option (Array Inline) := none
  let mut runningFrom : Nat := 1
  let mut styles : Styles := {}
  let mut info : Meta := {}
  let mut output : OutputSpec := {}
  let mut asserts : Array Assertion := #[]
  let mut textDiagged := false
  let mut i := 0
  repeat
    if h : i < preamble.size then
      let r := preamble[i]
      -- An \input wrapper in the preamble splices open between file markers,
      -- so its declarations process in place and its diagnostics name the
      -- file that holds them.
      if let .env n wrapped pos := r then
        if let some f := Parse.inputEnvFile? n then
          preamble := preamble.extract 0 i ++
            #[Raw.ctrl (fileMarker f) pos] ++ wrapped ++
            #[Raw.ctrl (fileMarker ctx.file) pos] ++
            preamble.extract (i + 1) preamble.size
          continue
      match r with
      | .space => i := i + 1
      | .par _ => i := i + 1
      | .ctrl "documentclass" pos =>
        i := i + 1
        let mut j := skipSpaces preamble i
        if let some (.sym '[' _) := preamble[j]? then
          let mut opts : Array Raw := #[]
          j := j + 1
          for _ in [j:preamble.size] do
            match preamble[j]? with
            | some (.sym ']' _) =>
              j := j + 1
              break
            | some r' =>
              opts := opts.push r'
              j := j + 1
            | none => break
          classOptions := rawSrc opts
          j := skipSpaces preamble j
        match preamble[j]? with
        | some (.group nameRaws _) =>
          i := j + 1
          docClass := (rawSrc nameRaws).trimAscii.toString
          if docClass != "article" && docClass != "slides" then
            diag ctx "E0309" s!"unknown document class '{docClass}'" pos
              (help := "classes: article | slides")
        | _ =>
          diag ctx "E0304" "'\\documentclass' needs a {class}" pos
      | .ctrl "define" pos =>
        i := i + 1
        let j := skipSpaces preamble i
        match preamble[j]? with
        | some (.ctrl newName npos) =>
          let mut sigRaws : Array Raw := #[]
          let mut k := j + 1
          let mut bodyRaws : Option (Array Raw) := none
          for _ in [k:preamble.size] do
            match preamble[k]? with
            | some (.group b _) =>
              bodyRaws := some b
              k := k + 1
              break
            | some r' =>
              sigRaws := sigRaws.push r'
              k := k + 1
            | none => break
          i := k
          if builtinNames.contains newName && (Lex.textSymbols.lookup newName).isNone then
            modify fun st => { st with diags := st.diags.push {
              severity := .warning, code := "W0303"
              message := s!"'\\{newName}' is built in; this definition is ignored"
              span := some ⟨ctx.file, npos⟩
              help := some "the built-in does what most definitions of this name do" } }
          else
            match bodyRaws with
            | some b =>
              let params ← parseSig ctx (rawSrc sigRaws) pos
              ctx := { ctx with
                user := ctx.user.push ⟨newName, params, trimRaws b⟩
                limit := ctx.user.size + 1 }
            | none =>
              diag ctx "E0303" s!"'\\define \\{newName}' is missing its \{body}" pos
        | _ =>
          diag ctx "E0303" "expected '\\define \\name(...)  {body}'" pos
          i := j + 1
      | .ctrl name pos =>
        i := i + 1
        if let some f := fileMarkerFile? name then
          ctx := { ctx with file := f }
        else if runningCtrl.contains name then
          -- `[from = 2]` keeps the opening page clean, as a title page is.
          let mut j := skipSpaces preamble i
          if let some (.sym '[' _) := preamble[j]? then
            let mut opt : Array Raw := #[]
            let mut k := j + 1
            for _ in [k:preamble.size + 1] do
              match preamble[k]? with
              | some (.sym ']' _) => k := k + 1; break
              | some r => opt := opt.push r; k := k + 1
              | none => break
            for e in Decl.splitEntries (rawSrc opt) do
              match Decl.splitEntry e with
              | some ("from", v) =>
                match v.trimAscii.toString.toNat? with
                | some n => runningFrom := n
                | none => diag ctx "E0321" s!"'from' needs a page number, got {v.quote}" pos
              | _ =>
                diag ctx "E0320" s!"unknown option in \\{name}: {e.quote}" pos
                  (help := "options: from = <page>")
            j := skipSpaces preamble k
          match preamble[j]? with
          | some (.group body _) =>
            i := j + 1
            let content ← elabInlines ctx body
            if name == "runninghead" then
              head := some content
            else
              foot := some content
          | _ =>
            diag ctx "E0304" s!"'\\{name}' needs one group of inline content" pos
        else if name == "style" then
          let j := skipSpaces preamble i
          let j2 := skipSpaces preamble (j + 1)
          match preamble[j]?, preamble[j2]? with
          | some (.group elem _), some (.group body _) =>
            i := j2 + 1
            styles ← applyStyle ctx styles (rawSrc elem) (rawSrc body) pos
          | _, _ =>
            diag ctx "E0304" "'\\style' needs {element} and a {...} block" pos
        else if declCtrl.contains name then
          let j := skipSpaces preamble i
          match preamble[j]? with
          | some (.group body _) =>
            i := j + 1
            let src := rawSrc body
            if name == "assert" then
              if let some a ← parseAssert ctx src pos then
                asserts := asserts.push a
            else if name == "output" then
              -- Parses its own entries: `formats` is a bare comma list, which
              -- a generic key/value pre-parse would break apart.
              output ← applyOutput ctx output src pos
            else if name == "tokens" then
              -- Parses its own entries one at a time; a generic pre-parse
              -- would reject `0.6 * rhythm` before the reference resolves.
              let tk ← applyTokens ctx tokens src pos
              tokens := tk
              ctx := { ctx with tokens := tk }
            else
              let (entries, ds) := Decl.parseBlock ctx.file src pos name
              modify fun st => { st with diags := st.diags ++ ds }
              if name == "page" then
                page ← applyPage ctx page entries pos
              else if name == "fonts" then
                fonts ← applyFonts ctx fonts entries pos
              else if name == "palette" then
                let pal ← applyPalette ctx palette entries pos
                palette := pal
                ctx := { ctx with palette := pal }
              else
                info ← applyMeta ctx info entries pos
          | _ =>
            diag ctx "E0304" s!"'\\{name}' needs a \{...} block" pos
        else if titleCtrls.contains name then
          -- A declaration-only position: the malformed run is dropped with
          -- W0310 already pointing at it — the preamble has no content.
          let (j, _) ← takeTitleDecl ctx name preamble i pos
          i := j
        else if let some milestone := reservedCtrl.lookup name then
          warnOnce ctx ("ctrl:" ++ name) "W0307" s!"'\\{name}' is not implemented yet; skipped" pos
            (help := s!"planned for {milestone}; see PLAN.md")
          let (j, unclosed) := skipReservedArgs preamble i pos
          match unclosed with
          | some bpos =>
            -- The malformed arguments end with the command's line or at the
            -- next construct on it: the author's next declaration is never
            -- consumed here.
            warnUnclosed ctx s!"'\\{name}'" bpos
            i := skipMalformedArgs preamble i pos
          | none => i := j
        else
          -- Unknown preamble commands are configuration, not content: their
          -- arguments are skipped with them, never elaborated as stray text.
          warnOnce ctx ("ctrl:" ++ name) "W0301" s!"unknown command '\\{name}' in the preamble; skipped" pos
            (help := "define it with \\define, or see PLAN.md for planned commands")
          let (j, unclosed) := skipReservedArgs preamble i pos
          match unclosed with
          | some bpos =>
            warnUnclosed ctx s!"'\\{name}'" bpos
            i := skipMalformedArgs preamble i pos
          | none => i := j
      | _ =>
        i := i + 1
        unless textDiagged do
          diag ctx "E0313" "only declarations may appear before '\\begin{document}'" none
          textDiagged := true
    else
      break
  -- Slides fill beamer's stage unless the document declared its own
  -- geometry: a handout on letter portrait is not best effort, it is wrong.
  if docClass == "slides" then
    let dflt : PageSpec := {}
    if page.width == dflt.width && page.height == dflt.height then
      let ratio169 := (classOptions.splitOn ",").any
        fun o => o.trimAscii.toString == "aspectratio=169"
      let (w, h) := if ratio169 then (Dim.mm 160, Dim.mm 90) else (Dim.mm 128, Dim.mm 96)
      page := { page with width := w, height := h }
    if page.hmargin == dflt.hmargin then
      page := { page with hmargin := Dim.mm 10 }
    if page.vmargin == dflt.vmargin then
      page := { page with vmargin := Dim.mm 9 }
  ctx := { ctx with slides := docClass == "slides" }
  let blocks ← elabBlocks ctx body
  if trailing.any (!isSpaceOrPar ·) then
    diag ctx "W0001" "content after '\\end{document}' is ignored" none (sev := .warning)
  -- PDF metadata falls back to the title declarations: a deck that says
  -- \title deserves an Info dictionary without saying it twice.
  let st ← get
  let fallback (cur : Option String) (src : Option (Array Inline)) : Option String :=
    match cur with
    | some s => some s
    | none =>
      match src with
      | some xs =>
        let t := Ir.plainText xs
        if t.isEmpty then none else some t
      | none => none
  info := { info with
    title := fallback info.title st.title
    author := fallback info.author st.author }
  return {
    docClass := docClass
    classOptions := classOptions
    page := page
    fonts := fonts
    palette := palette
    tokens := tokens
    head := head
    foot := foot
    runningFrom := runningFrom
    styles := styles
    info := info
    output := output
    asserts := asserts
    body := blocks
  }

/-- Elaborate parsed input. LaTeX idioms are rewritten first, so a document
written for another engine compiles as written. -/
def runRaws (file : String) (raws : Array Raw) (earlier : Array Diag := #[]) :
    Doc × Array Diag :=
  let (raws, compatDiags) := Compat.rewrite file raws
  let (doc, st) := (elabDoc file raws).run {}
  (doc, earlier ++ compatDiags ++ st.diags)

def run (file input : String) : Doc × Array Diag :=
  let (toks, lexDiags) := Lex.lex file input
  let (raws, parseDiags) := Parse.parse file toks
  runRaws file raws (lexDiags ++ parseDiags)

end LeanTex.Core.Elab
