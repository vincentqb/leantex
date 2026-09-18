import LeanTex.Core.Lex
import LeanTex.Core.Parse
import LeanTex.Core.MathParse
import LeanTex.Core.Ir
import LeanTex.Core.Dim
import LeanTex.Core.Decl
import LeanTex.Core.Theme
import LeanTex.Core.Compat
import LeanTex.Core.Contrast
import LeanTex.Core.Picture
import LeanTex.Core.FaIcons

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

/-- A document-defined environment (`\defineenv`, the native spelling of
`\newenvironment`): its begin and end halves wrap the environment's content,
and its parameters bind from the groups after `\begin{name}`. -/
structure UserEnv where
  name : String
  params : Array Param
  beginBody : Array Raw
  endBody : Array Raw
  /-- Commands the halves may use: those defined before this environment.
  That bound is what makes expansion terminate, as `limit` does for
  commands. -/
  cmdLimit : Nat
  deriving Repr, BEq

/-- A user command sees only commands defined before it: `limit` bounds the
visible prefix of `user`. That rule is what makes expansion terminate. -/
structure Ctx where
  file : String
  user : Array UserCmd := #[]
  limit : Nat := 0
  /-- Document-defined environments; `envLimit` bounds the visible prefix,
  as `limit` does for commands. -/
  userEnvs : Array UserEnv := #[]
  envLimit : Nat := 0
  args : Array (String × Option (Array Inline)) := #[]
  /-- Palette names usable as colour commands, from `\palette`. -/
  palette : Palette := {}
  /-- Named lengths from `\tokens`. -/
  tokens : Tokens := {}
  /-- Element styles declared so far (`\style`, theme bundles): the body
  reads `titlepage` at `\maketitle`. -/
  styles : Styles := {}
  /-- Inside mono/verbatim content, where punctuation stays literal. -/
  literalText : Bool := false
  /-- Inside a speaker note, absorbed as beamer absorbs it: a reserved
  character is literal text there, never a build error. -/
  noteBody : Bool := false
  /-- Overlay steps already opened by `\pause` in enclosing scopes: the next
  pause reveals at `stepBase + 1`. -/
  stepBase : Nat := 0
  /-- The document class is `slides`: `\maketitle` makes a title frame. -/
  slides : Bool := false
  /-- The effective backend target set of the enclosing `{ifbackend}`
  nesting: every backend at the top, intersected at each conditional on the
  way in, so a nested conditional that empties the set is diagnosed where
  it stands (E0334) — the same walk `Ir.orphanFree` performs. -/
  backendTargets : List String := Ir.backendNames

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
  /-- A `\maketitle` already set the title: LaTeX typesets a title once
  (classes.dtx: `\maketitle` ends with `\global\let\maketitle\relax`), and
  keeping to that is what makes the level-0 heading unique by
  construction — a second call warns and produces nothing. -/
  titleDone : Bool := false
  /-- Speaker-note bodies met inside inline content, where a block cannot
  stand: the enclosing frame drains them to its end, so a mid-sentence
  `\note` neither splits its paragraph nor loses its words. -/
  pendingNotes : Array (Array Raw) := #[]
  /-- beamer's `\logo`, a declaration legal in the preamble and the body
  alike; the last one wins, as in beamer. -/
  logo : Option (Array Inline) := none
  /-- The palette after body declarations: `\palette` (usually a rewritten
  `\colorlet`) is legal in the body as in LaTeX, applying to what follows;
  the document palette both backends read is the last state, so a
  body-declared colour resolves in HTML variables and contrast checks like
  any other. `none` while the body declared nothing. -/
  bodyPalette : Option Palette := none
  /-- Body-declared tokens (`\setlength` mid-document), same door. -/
  bodyTokens : Option Tokens := none

abbrev EM := StateM ESt

private def diag (ctx : Ctx) (code : DiagCode) (msg : String) (pos : Option Pos)
    (help : Option String := none) : EM Unit :=
  modify fun st => { st with
    diags := st.diags.push (Diag.of code msg (pos.map (⟨ctx.file, ·⟩)) help) }

/-- A warning deduplicated by `key`: the same unsupported construct in forty
frames is one problem, not forty. -/
private def warnOnce (ctx : Ctx) (key : String) (code : DiagCode) (msg : String) (pos : Pos)
    (help : Option String := none) : EM Unit := do
  unless (← get).warnedUnknown.contains key do
    modify fun st => { st with warnedUnknown := st.warnedUnknown.push key }
    diag ctx code msg (some pos) help

/-- One formula: parsed into math atoms when this slice can model it, kept
as source text with a warning naming the construct when it cannot — out of
scope is a named warning, never a silent drop. A ragged alignment row
inside the formula (an `array`) is W0014: padded with empty cells, named. -/
private def elabMathInline (ctx : Ctx) (display : Bool) (body : Array Parse.Raw)
    (pos : Pos) : EM Ir.Inline := do
  match MathParse.parseMath body with
  | .ok (l, notes) =>
    for note in notes do
      warnOnce ctx ("math:ragged:" ++ note) .W0014
        s!"alignment {note}" pos
    return .formula display (Parse.rawSrc body) l
  | .error what =>
    warnOnce ctx ("math:" ++ what) .W0012
      s!"math with {what} is not rendered yet; the formula is set as source text" pos
    return .math display (Parse.rawSrc body)

/-- One alignment environment (`align`/`gather` and their starred forms):
its rows parsed into one display grid formula. A construct the parser
cannot model keeps the whole environment as source, named (W0012); a
ragged row is W0014, padded; a numbered form warns W0015 once — the
equation numbers are owed, the mathematics is not. -/
private def elabMathEnv (ctx : Ctx) (name : String) (kind : Math.GridKind)
    (numbered : Bool) (body : Array Parse.Raw) (pos : Pos) : EM Ir.Inline := do
  match MathParse.parseMathRows kind body with
  | .ok (l, notes) =>
    for note in notes do
      warnOnce ctx ("math:ragged:" ++ note) .W0014
        s!"'\{{name}}': {note}" pos
    if numbered then
      warnOnce ctx "math:eqnum" .W0015
        s!"equation numbers are not rendered yet; '\{{name}}' sets unnumbered" pos
        (help := s!"'\{{name}*}' spells the unnumbered form, which renders the same")
    return .formula true (Parse.rawSrc body) l
  | .error what =>
    warnOnce ctx ("math:" ++ what) .W0012
      s!"math with {what} is not rendered yet; '\{{name}}' is set as source text" pos
    return .math true (Parse.rawSrc body)

/-- Reserved control words, and the code each skip earns — W0307 (pending,
a warning: a milestone owns the construct) when the skipped arguments carry
content, W0329 (config) when only layout or selection is lost. -/
def reservedCtrl : List (String × DiagCode) :=
  [("vspace", .W0329), ("noindent", .W0329),
   ("fontfallback", .W0329), ("figure", .W0307)]

/-- Declarations that take a `{...}` block and are handled in the preamble. -/
def declCtrl : List String :=
  ["page", "pdfmeta", "assert", "fonts", "palette", "tokens", "style", "output",
   "theme", "chrome"]

/-- Preamble declarations that take one group of *inline content* rather than
a key/value block: running head and foot. -/
def runningCtrl : List String := ["runninghead", "runningfoot"]

def pageKeys : List String :=
  ["size", "width", "height", "margin", "vmargin", "hmargin", "leading", "parskip",
   "measure", "fontsize", "bleed", "hyphenate", "justify"]

def metaKeys : List String :=
  ["title", "author", "subject", "keywords", "url", "image", "favicon"]

def fontKeys : List String := ["body", "sans", "mono", "math", "rm", "sf", "tt", "dir"]

/-- Named page sizes, in sp. -/
def pageSizes : List (String × (Sp × Sp)) :=
  [("letter", (pt 612, pt 792)),
   ("legal", (pt 612, pt 1008)),
   ("a4", (Dim.pt 595, Dim.pt 842)),
   ("a5", (Dim.pt 420, Dim.pt 595))]

def reservedEnv : List String :=
  ["external", "tikzpicture"]

/-- The alignment environments this slice renders as grids: the column
model, and whether LaTeX numbers the rows (numbers are owed, W0014).
`array` is not here — it lives inside math and the math parser owns it. -/
def alignEnvs : List (String × Math.GridKind × Bool) :=
  [("align", .align, true), ("align*", .align, false),
   ("gather", .gather, true), ("gather*", .gather, false)]

/-- The display-math environments rendered as one centred formula, and
whether LaTeX numbers them (`equation` renders unnumbered under W0014). -/
def displayMathEnvs : List (String × Bool) :=
  [("equation*", false), ("displaymath", false), ("equation", true)]

/-- Is this environment display mathematics — its own centred block? -/
def isMathEnv (name : String) : Bool :=
  (displayMathEnvs.lookup name).isSome || (alignEnvs.lookup name).isSome

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
   "defineenv", "block", "framefoot", "pagebreak"]

/-- The overlay commands, dim-not-hide (PLAN M5). `\alt` is not here: it
takes two groups and is handled beside them. -/
def overlayCtrls : List String :=
  ["uncover", "visible", "only", "onslide"]

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

/-- The latest visible definition wins, so `\renewenvironment` is one more
push, exactly as `lookupUser` treats commands. -/
private def lookupUserEnv (ctx : Ctx) (name : String) : Option (Nat × UserEnv) := Id.run do
  let mut k := ctx.envLimit
  for _ in [0:ctx.envLimit] do
    k := k - 1
    if h : k < ctx.userEnvs.size then
      if ctx.userEnvs[k].name == name then
        return some (k, ctx.userEnvs[k])
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

/-- An overlay specification's range: `<2->` is (2, none) — crisp from 2 on;
`<2>` is (2, some 2) and `<2-3>` is (2, some 3) — crisp within the range,
dimmed outside it, never hidden. `none` for a spec the model cannot number
(`<+->`, `<.->`), which keeps the honest W0105. -/
private def overlayFrom (w : String) : Option (Nat × Option Nat) :=
  if w.startsWith "<" && w.endsWith ">" && w.length ≥ 3 then
    let inner := ((w.drop 1).dropEnd 1).toString.toList
    let digits := inner.takeWhile Char.isDigit
    if digits.isEmpty then none else
    match (String.ofList digits).toNat? with
    | none => none
    | some n =>
      match inner.drop digits.length with
      | [] => some (n, some n)
      | '-' :: rest =>
        let toDigits := rest.takeWhile Char.isDigit
        if rest.isEmpty then some (n, none)
        else if toDigits.length == rest.length && !toDigits.isEmpty then
          (String.ofList toDigits).toNat?.map fun u => (n, some u)
        else none
      | _ => none
  else none

/-- Is this raw an overlay spec word? The lexer keeps `<2->` one word. -/
private def specWord? : Raw → Option String
  | .word w _ => if w.startsWith "<" && w.endsWith ">" then some w else none
  | _ => none

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
  diag ctx .W0310 s!"'[' after {after} never closes; it is not an argument" (some bpos)
    (help := "add the matching ']'")

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
    diag ctx .E0336
      s!"{dropped} \{...} {noun} on the '\\begin\{{name}}' line went with the unknown wrapper" (some pos)
      (help := "content, not an argument? put it after the '\\begin' line")

/-- A command whose group never materialised after an unclosed `[` is
dropped whole: W0310 already named the typo, and one skipped declaration
must not fail the build or bleed into the next construct as stray content. -/
private def warnSkippedDecl (ctx : Ctx) (name : String) (pos : Pos) : EM Unit :=
  diag ctx .W0312 s!"no \{...} group after '\\{name}'; it is skipped" (some pos)
    (help := s!"write \\{name}\{...}")

/-- The index of the next construct after a skipped preamble command's
malformed arguments. The junk ends with the command's line, and a control
word, an environment, or a verbatim block ends it early: the author's next
declaration is never consumed with the junk, whether it follows the line or
shares it. -/
private def skipMalformedArgs (raws : Array Raw) (i : Nat) (anchor : Pos) : Nat :=
  malformedRun raws i anchor (groups := true)

/-- Skip an argument run: argument recovery after a reserved (not yet
implemented) or unknown command. A starred form's `*`, a `[...]` options
run, and up to `maxGroups` `{...}` groups are consumed with the command
they belong to — recovery never turns a warning into an error, and a stray
`*` or second group in the preamble is exactly how one skipped command
used to become E0313. In the body `maxGroups` stays 1, so a scope group
standing after a reserved command is still content; in the preamble there
is no content, so the caller passes TeX's own argument limit of nine. The
scan stops at anything else, so the author's next construct is never
consumed. Returns the next index and, when an unclosed `[` stopped the
scan, its position. -/
private def skipReservedArgs (raws : Array Raw) (i : Nat) (anchor : Pos)
    (maxGroups : Nat := 1) : Nat × Option Pos := Id.run do
  let mut j := i
  if let some (.word "*" _) := raws[j]? then
    j := j + 1
  for _ in [0:maxGroups] do
    match scanBracketArg raws j anchor with
    | .took k => j := k
    | .unclosed bpos => return (j, some bpos)
    | .content => pure ()
    let k := skipSpaces raws j
    if let some (.group _ _) := raws[k]? then
      j := k + 1
    else
      break
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

/-- One `\includegraphics` dimension: a factor of `\textwidth` (or its
`\linewidth`/`\columnwidth` spellings) or `\textheight`, or an absolute
length. Font-relative units are refused — an image has no font size. -/
private def imageLen (src : String) : Option Image.Len := Id.run do
  let s := src.trimAscii.toString
  let factor (f : String) : Option (Int × Nat) :=
    let f := f.trimAscii.toString
    if f.isEmpty then some (1, 1) else Decl.parseDecimal f
  for suffix in ["\\textwidth", "\\linewidth", "\\columnwidth"] do
    if s.endsWith suffix then
      return (factor ((s.dropEnd suffix.length).toString)).map
        fun (m, sc) => { tw := m * 1000 / sc }
  if s.endsWith "\\textheight" then
    return (factor ((s.dropEnd "\\textheight".length).toString)).map
      fun (m, sc) => { th := m * 1000 / sc }
  match Decl.parseLength s with
  | some l => return if l.em == 0 && l.ex == 0 then some { sp := l.sp } else none
  | none => return none

/-- One `p{...}` column width: a fraction of `\linewidth` (or its
`\textwidth`/`\columnwidth` spellings) in permille, or an absolute length.
`none` is unreadable. -/
private def colWidth (src : String) : Option Ir.ColWidth := Id.run do
  let s := src.trimAscii.toString
  for suffix in ["\\linewidth", "\\textwidth", "\\columnwidth"] do
    if s.endsWith suffix then
      let f := (s.dropEnd suffix.length).toString.trimAscii.toString
      if f.isEmpty then return some (.frac 1000)
      return (Decl.parseDecimal f).map fun (m, sc) => .frac (m * 1000 / sc).toNat
  match Decl.parseLength s with
  | some l =>
    return if l.em == 0 && l.ex == 0 then some (.abs l.sp) else none
  | none => return none

/-- The `tabular` column spec: `l`/`c`/`r` natural columns, `p{width}`
(and `m`/`b`, set as `p`: the engine has no per-cell vertical alignment),
`@{}` deleting the outer pad on its edge, `|` warned and never drawn —
"Never, ever use vertical rules" (booktabs.dtx §The layout of formal
tables). Returns the columns, the outer-pad flags, and warnings as
(key, message, help) for the caller's `warnOnce`. -/
private def parseColSpec (spec : Array Raw) :
    Array Ir.ColSpec × Bool × Bool × Array (String × String × String) := Id.run do
  let mut cols : Array Ir.ColSpec := #[]
  let mut padL := true
  let mut padR := true
  let mut warns : Array (String × String × String) := #[]
  let mut i := 0
  for _ in [0:spec.size] do
    if h : i < spec.size then
      match spec[i] with
      | .sym '|' _ =>
        warns := warns.push ("vrule",
          "'|' asks for a vertical rule; formal tables never draw one \
(booktabs), so it is not drawn",
          "widen the column gap instead: vertical rules mark a gap that is \
too small")
        i := i + 1
      | .sym '@' _ =>
        match spec[i + 1]? with
        | some (.group g _) =>
          if g.all isSpaceOrPar then
            if cols.isEmpty then padL := false else padR := false
          else
            warns := warns.push ("atgroup",
              "'@{...}' with content between columns is not supported; \
only the empty '@{}' deleting an outer pad is",
              "")
          i := i + 2
        | _ => i := i + 1
      | .word w _ =>
        let last := w.toList.length - 1
        let mut ci := 0
        let mut tookGroup := false
        for c in w.toList do
          match c with
          | 'l' => cols := cols.push { width := .natural, align := .left }
          | 'c' => cols := cols.push { width := .natural, align := .center }
          | 'r' => cols := cols.push { width := .natural, align := .right }
          | 'p' | 'm' | 'b' =>
            let widthGroup := if ci == last then
              match spec[i + 1]? with
              | some (.group g _) => some (Parse.rawSrc g)
              | _ => none
            else none
            let mut width : Ir.ColWidth := .natural
            if let some src := widthGroup then
              match colWidth src with
              | some cw => width := cw
              | none =>
                warns := warns.push ("pwidth",
                  s!"unreadable column width '{src}'; the column takes \
the full measure",
                  "a fraction of \\linewidth or an absolute length")
                width := .frac 1000
            tookGroup := tookGroup || widthGroup.isSome
            if c != 'p' then
              warns := warns.push ("mb",
                s!"'{c}\{...}' vertical cell alignment is not modelled; set \
as 'p'", "")
            cols := cols.push { width := width, align := .left }
          | '@' =>
            -- `@{...}` lexes as a word character with the group beside it:
            -- the empty `@{}` deletes the outer pad on its edge.
            if cols.isEmpty then padL := false else padR := false
            if ci == last then
              if let some (.group g _) := spec[i + 1]? then
                tookGroup := true
                unless g.all isSpaceOrPar do
                  warns := warns.push ("atgroup",
                    "'@{...}' with content between columns is not supported; \
only the empty '@{}' deleting an outer pad is",
                    "")
          | '|' =>
            warns := warns.push ("vrule",
              "'|' asks for a vertical rule; formal tables never draw one \
(booktabs), so it is not drawn",
              "widen the column gap instead: vertical rules mark a gap that \
is too small")
          | _ =>
            if !c.isWhitespace then
              warns := warns.push ("colspec",
                s!"unsupported column type '{c}'; set as 'l'", "")
              cols := cols.push { width := .natural, align := .left }
          ci := ci + 1
        i := i + (if tookGroup then 2 else 1)
      | _ => i := i + 1
  return (cols, padL, padR, warns)

/-- The `{a-b}` range of a `\cmidrule`/`\cline`, 1-based inclusive. -/
private def cmidRange (src : String) : Option (Nat × Nat) :=
  match (src.trimAscii.toString.splitOn "-").map (·.trimAscii.toString.toNat?) with
  | [some a, some b] => some (a, b)
  | [some a] => some (a, a)
  | _ => none

/-- A table cell's edges: LaTeX ignores the spaces around `&` and `\\`
(the template's `\ignorespaces`/`\unskip`). -/
private def trimRawEdges (raws : Array Raw) : Array Raw := Id.run do
  let mut rs := raws
  repeat
    match rs.back? with
    | some r => if isSpaceOrPar r then rs := rs.pop else break
    | none => break
  let mut k := 0
  for r in rs do
    if isSpaceOrPar r then k := k + 1 else break
  return rs.extract k rs.size

mutual

/-- Bind declared parameters from the call site — a user command's, or a
user environment's from the groups after its `\begin`. Returns the bindings
and the index just past the consumed arguments. Shared by inline and block
expansion so both bind identically. -/
partial def takeArgs (ctx : Ctx) (params : Array Param) (name : String)
    (raws : Array Raw) (start : Nat) (pos : Pos) :
    EM (Array (String × Option (Array Inline)) × Nat) := do
  let mut bindings : Array (String × Option (Array Inline)) := #[]
  let mut i := start
  for p in params do
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
          diag ctx .E0316 s!"unclosed optional argument for '\\{name}'" pos
        i := k'
        let v ← elabInlines ctx body
        if p.type == .text && !allText v then
          diag ctx .E0305 s!"parameter '{p.name}' of '\\{name}' expects text" pos
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
          diag ctx .E0305 s!"parameter '{p.name}' of '\\{name}' expects text" pos
        bindings := bindings.push (p.name, some v)
      | some (.word s _) =>
        i := j + 1
        bindings := bindings.push (p.name, some #[.text s])
      | _ =>
        diag ctx .E0304 s!"missing argument '{p.name}' for '\\{name}'" pos
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
        if ctx.noteBody then
          -- A note is absorbed, as beamer absorbs it: its reserved
          -- characters are the speaker's literal text.
          sb := sb.push c
        else
          diag ctx .E0311 s!"reserved character '{c}'" pos (help := s!"escape it as '\\{c}'")
        i := i + 1
      | .math d body mpos =>
        acc := flushText acc sb
        sb := ""
        acc := acc.push (← elabMathInline ctx d body mpos)
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
        else if let some numbered := displayMathEnvs.lookup name then
          i := i + 1
          acc := flushText acc sb
          sb := ""
          if numbered then
            warnOnce ctx "math:eqnum" .W0015
              s!"equation numbers are not rendered yet; '\{{name}}' sets unnumbered" pos
              (help := s!"the starred '\{{name}}*' says what renders today; see PLAN.md")
          acc := acc.push (← elabMathInline ctx true body pos)
        else if let some (kind, numbered) := alignEnvs.lookup name then
          i := i + 1
          acc := flushText acc sb
          sb := ""
          acc := acc.push (← elabMathEnv ctx name kind numbered body pos)
        else if let some (k, env) := lookupUserEnv ctx name then
          -- A defined wrapper: its parameters bind from the groups after
          -- `\begin{name}`, its halves elaborate around the content. The
          -- halves see the commands and environments defined before the
          -- wrapper (never itself), the content sees the caller's.
          i := i + 1
          acc := flushText acc sb
          sb := ""
          let (bindings, j) ← takeArgs ctx env.params name body 0 pos
          let envCtx : Ctx := { ctx with
            limit := env.cmdLimit, envLimit := k, args := bindings }
          acc := acc ++ (← elabInlines envCtx env.beginBody)
          acc := acc ++ (← elabInlines ctx (body.extract j body.size))
          acc := acc ++ (← elabInlines envCtx env.endBody)
        else
        if reservedEnv.contains name then
          i := i + 1
          warnOnce ctx ("env:" ++ name) .W0307
            s!"'\{{name}}' is not implemented yet; its content is not rendered" pos
        else
          warnOnce ctx ("env:" ++ name) .W0302 s!"unknown environment '\{{name}}'; its body is kept" pos
            (help := "\\defineenv{name}(...) {begin} {end} declares one")
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
          let (bindings, j) ← takeArgs ctx cmd.params name raws i pos
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
                diag ctx .E0331 s!"cannot read a length from '{src}'" pos
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
            diag ctx .E0304 s!"'\\{name}' needs an argument" pos
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
            diag ctx .E0304 s!"'\\{name}' needs an argument" pos
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
            diag ctx .E0304 s!"'\\{name}' needs a URL group, optionally followed by text" pos
        else if name == "includegraphics" then
          -- graphicx's command, native. The keys that size figures in real
          -- documents are modelled — width, height, scale, keepaspectratio —
          -- and anything else (rotation included) is named and skipped: a
          -- silently dropped key would misplace the figure without a word.
          let mut spec : Image.SizeSpec := {}
          let mut altText := ""
          let mut j := skipSpaces raws i
          if let some (.sym '[' _) := raws[j]? then
            let mut optSrc : Array Raw := #[]
            let mut k := j + 1
            for _ in [k:raws.size + 1] do
              match raws[k]? with
              | some (.sym ']' _) => k := k + 1; break
              | some r' => optSrc := optSrc.push r'; k := k + 1
              | none => break
            j := skipSpaces raws k
            for e in Decl.splitEntries (rawSrc optSrc) do
              match Decl.splitEntry e with
              | some ("width", v) =>
                match imageLen v with
                | some l => spec := { spec with width := some l }
                | none =>
                  diag ctx .E0331 s!"cannot read a length from '{v}'" pos
                    (help := "image sizes look like 3cm or 0.8\\textwidth")
              | some ("height", v) | some ("totalheight", v) =>
                -- totalheight is height plus depth, and an image has no
                -- depth, so the two keys coincide here.
                match imageLen v with
                | some l => spec := { spec with height := some l }
                | none =>
                  diag ctx .E0331 s!"cannot read a length from '{v}'" pos
                    (help := "image sizes look like 3cm or 0.3\\textheight")
              | some ("scale", v) =>
                match Decl.parseDecimal v with
                | some (m, sc) => spec := { spec with scaleNum := m, scaleDen := sc }
                | none => diag ctx .E0321 s!"'scale' needs a number, got {v.quote}" pos
              | some ("alt", v) =>
                -- graphicx's own alt key (LaTeX News 37, 2023): the text
                -- alternative WCAG 2.2 SC 1.1.1 requires, declared where the
                -- image is. Braced or quoted spellings both read as text.
                let v := if v.startsWith "{" && v.endsWith "}" && v.length ≥ 2 then
                    String.ofList (v.toList.drop 1).dropLast
                  else if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then
                    String.ofList (v.toList.drop 1).dropLast
                  else v
                altText := v.trimAscii.toString
              | _ =>
                if e.trimAscii.toString == "keepaspectratio" then
                  spec := { spec with keepAspect := true }
                else
                  warnOnce ctx ("imgopt:" ++ e) .W0110
                    s!"'\\includegraphics' option '{e}' is not modelled; ignored" pos
                    (help := "modelled keys: width, height, scale, keepaspectratio, alt")
          match raws[j]? with
          | some (.group pathRaw _) =>
            i := j + 1
            acc := flushText acc sb
            sb := ""
            acc := acc.push (.image (argText ctx pathRaw) spec altText)
          | _ =>
            diag ctx .E0304 "'\\includegraphics' needs a {file} group" pos
        else if name == "faIcon" then
          -- fontawesome5's generic spelling: `\faIcon[style]{icon-name}`,
          -- optionally starred for the `-alt` variant. The style argument
          -- selects a Pro face there; here which file covers the scalar is
          -- the per-scalar fallback chain's question, so a style is named
          -- as an ignored option rather than dropped without a word. The
          -- one extension: `label = ...` overrides the icon's default text
          -- alternative, for a context where Font Awesome's own name is
          -- not the right accessible name (`Return to top` on an arrow).
          let mut j := skipSpaces raws i
          let mut alt := false
          if let some (.word "*" _) := raws[j]? then
            alt := true
            j := skipSpaces raws (j + 1)
          let mut label : Option String := none
          if let some (.sym '[' _) := raws[j]? then
            let mut optSrc : Array Raw := #[]
            let mut k := j + 1
            for _ in [k:raws.size + 1] do
              match raws[k]? with
              | some (.sym ']' _) => k := k + 1; break
              | some r' => optSrc := optSrc.push r'; k := k + 1
              | none => break
            j := skipSpaces raws k
            for e in Decl.splitEntries (rawSrc optSrc) do
              match Decl.splitEntry e with
              | some ("label", v) => label := some v.trimAscii.toString
              | _ =>
                warnOnce ctx ("faopt:" ++ e) .W0110
                  s!"'\\faIcon' option '{e.trimAscii.toString}' is not modelled; ignored" pos
                  (help := "the face that renders an icon is whichever declared or installed face covers its scalar; 'label = ...' overrides the icon's text alternative")
          match raws[j]? with
          | some (.group nameRaw _) =>
            i := j + 1
            let iconName := (argText ctx nameRaw).trimAscii.toString
              ++ (if alt then "-alt" else "")
            match FaIcons.byName[iconName]? with
            | some e =>
              acc := flushText acc sb
              sb := ""
              acc := acc.push (.icon e.scalar (label.getD e.label))
            | none =>
              diag ctx .E0340 s!"unknown icon '{iconName}'; nothing is rendered" pos
                (help := "icon names are Font Awesome 5 Free's, like 'arrow-up' or 'github'")
          | _ =>
            diag ctx .E0304 "'\\faIcon' needs an {icon-name} group" pos
        else if let some e := FaIcons.byMacro[name]? then
          -- The per-icon fontawesome5 command (`\faGithub`, `\faArrowUp`):
          -- the package's own name-to-scalar mapping, carried as data
          -- (`FaData`, generated from fontawesome5-mapping.def).
          acc := flushText acc sb
          sb := ""
          acc := acc.push (.icon e.scalar e.label)
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
            match ctx.palette.resolve key with
            | some c =>
              acc := flushText acc sb
              sb := ""
              -- A mix expression is a computed value, not a token: only a
              -- plain palette name rides along for the HTML var(--name).
              let cssName := if (ctx.palette.find? key).isSome then some key else none
              acc := acc.push (.colored c cssName (← elabInlines ctx body))
            | none =>
              -- The colour is unresolvable; the content is not. Keeping it
              -- uncoloured is the best-effort contract: a wrong colour beats
              -- a missing word.
              warnOnce ctx ("palette:" ++ key) .W0304
                s!"'{key}' is not in the palette; content kept uncoloured" pos
                (help := if ctx.palette.entries.isEmpty then
                    "declare colours with \\palette{ name = #RRGGBB }"
                  else s!"declared: {String.intercalate ", "
                    (ctx.palette.entries.toList.map (·.1))}")
              acc := flushText acc sb
              sb := ""
              acc := acc ++ (← elabInlines ctx body)
          | _, _ =>
            diag ctx .E0304 "'\\textcolor' needs {name} and {content}" pos
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
              | none => diag ctx .E0306 s!"unknown parameter '\\{pname}'" pos
            | _ =>
              diag ctx .E0306 "expected a parameter reference like {\\team}" pos
          | _, _ =>
            diag ctx .E0304 "'\\ifgiven' needs {\\param} and {content}" pos
        else if overlayCtrls.contains name then
          -- Overlay commands, dim-not-hide (PLAN M5): the content wraps in
          -- a step and dims before its turn — \only included, one overlay
          -- semantics for both backends. Without a group the spec declares:
          -- the rest of this inline scope steps. A spec the model cannot
          -- number keeps the honest W0105 and the content stays shown.
          let j := skipSpaces raws i
          match raws[j]?.bind specWord? with
          | some w =>
            match overlayFrom w with
            | some (n, last) =>
              let j2 := skipSpaces raws (j + 1)
              match raws[j2]? with
              | some (.group gbody _) =>
                acc := flushText acc sb
                sb := ""
                acc := acc.push (.step n last (← elabInlines ctx gbody))
                i := j2 + 1
              | _ =>
                acc := flushText acc sb
                sb := ""
                acc := acc.push (.step n last (← elabInlines ctx (raws.extract (j + 1) raws.size)))
                i := raws.size
            | none =>
              warnOnce ctx "spec:overlay" .W0105
                s!"overlay specification '{w}' does not name a step; its content is \
shown on every step" pos
                (help := "write a numbered spec: <2>, <2->, or <2-3>; incremental \
specs are not modelled")
              i := j + 1
          | none => pure ()
        else if name == "alt" then
          -- `\alt<spec>{active}{otherwise}`: under dim-not-hide both
          -- alternatives are on the page — the active one crisp within its
          -- spec, the other before it — so alternation reads as emphasis
          -- moving, and nothing reflows. The complement of a mid-deck range
          -- is not one range, so the otherwise side stays dimmed past it.
          let j := skipSpaces raws i
          let (spec, j2) := match raws[j]?.bind specWord? with
            | some w => (overlayFrom w, skipSpaces raws (j + 1))
            | none => (none, j)
          let j3 := skipSpaces raws (j2 + 1)
          match raws[j2]?, raws[j3]? with
          | some (.group ga _), some (.group gb _) =>
            i := j3 + 1
            acc := flushText acc sb
            sb := ""
            match spec with
            | some (n, last) =>
              acc := acc.push (.step n last (← elabInlines ctx ga))
              acc := acc.push (.step 1 (some (n - 1)) (← elabInlines ctx gb))
            | none =>
              warnOnce ctx "spec:overlay" .W0105
                "'\\alt' without a numbered specification shows both \
alternatives on every step" pos
                (help := "write a numbered spec: <2>, <2->, or <2-3>; incremental \
specs are not modelled")
              acc := acc ++ (← elabInlines ctx ga)
              acc := acc ++ (← elabInlines ctx gb)
          | _, _ =>
            diag ctx .E0304 "'\\alt' needs <spec>{content}{content}" pos
        else if name == "pause" then
          -- Reachable only inside an argument or definition body; between
          -- blocks the boundary rule steps the rest of the scope.
          warnOnce ctx "spec:pause-inline" .W0105
            "'\\pause' inside an argument cannot step; its content is shown" pos
        else if name == "note" then
          -- A speaker note met mid-sentence: no block can stand here, so
          -- the body is stashed for the enclosing frame to drain — the
          -- paragraph flows on unbroken and the note never leaks into it.
          if let .took _ := scanBracketArg raws i pos then
            warnOnce ctx "note:options" .N0102
              "'\\note' placement and overlay options are ignored: the note is \
a side channel, never slide content" pos
          let (j, _, _) ← skipOptArg ctx "note" raws i pos
          i := j
          let js := skipSpaces raws i
          if (raws[js]?.bind specWord?).isSome then
            warnOnce ctx "note:options" .N0102
              "'\\note' placement and overlay options are ignored: the note is \
a side channel, never slide content" pos
            i := js + 1
          let j2 := skipSpaces raws i
          if let some (.group nbody _) := raws[j2]? then
            i := j2 + 1
            modify fun st => { st with pendingNotes := st.pendingNotes.push nbody }
        else if name == "centering" then
          -- Between blocks the declaration centres the rest of its scope;
          -- here, inside inline content, there is no block to centre.
          warnOnce ctx "ctrl:centering" .W0108
            "'\\centering' centres nothing inside an argument; content stays left-aligned" pos
            (help := "move '\\centering' to the start of the group or environment body")
        else if let some code := reservedCtrl.lookup name then
          warnOnce ctx ("ctrl:" ++ name) code s!"'\\{name}' is not implemented yet; skipped" pos
          let (j, unclosed) := skipReservedArgs raws i pos
          if let some bpos := unclosed then
            warnUnclosed ctx s!"'\\{name}'" bpos
          i := j
        else if blockOnly.contains name then
          diag ctx .E0312 s!"'\\{name}' is not allowed here" pos
            (help := "it is a block-level command: use it between paragraphs, " ++
              "not inside inline content or a command body")
        else
          -- Best effort: the arguments are content, and content is never
          -- dropped for want of a command. Only the formatting is lost.
          warnOnce ctx ("ctrl:" ++ name) .W0301
            s!"unknown command '\\{name}'; its arguments were kept as text" pos
            (help := "\\define \\name(...) {body} declares it")
          let mut j := skipSpaces raws i
          -- A starred form's `*` belongs to the command, not to the text.
          if let some (.word "*" _) := raws[j]? then
            j := skipSpaces raws (j + 1)
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
def blockEnvs : List String :=
  ["itemize", "enumerate", "center", "document", "frame", "columns", "figure",
   "figure*", "table", "table*", "quote", "quotation", "ifbackend", "nav",
   "minipage"]

/-- Environment names a document cannot redefine, the environment mirror of
`builtinNames`: everything the engine gives a meaning of its own. -/
def builtinEnvNames : List String :=
  blockEnvs ++ (alignEnvs.map (·.1)) ++ (displayMathEnvs.map (·.1)) ++
  ["verbatim", "tabular", "tabular*", "column", "array"] ++
  reservedEnv

/-- A column width as per mille of the text width: `0.48\textwidth`,
`.5\linewidth`, a bare factor, or `\textwidth` alone — a factor of one, as
TeX reads a coefficient-less internal dimen. An absolute length is not
modelled. -/
private def columnWidth (src : String) : Option Nat := Id.run do
  let mut s := src.trimAscii.toString
  let mut stripped := false
  for suffix in ["\\textwidth", "\\linewidth", "\\columnwidth"] do
    if s.endsWith suffix then
      s := ((s.dropEnd suffix.length).trimAscii).toString
      stripped := true
  if s.isEmpty then return if stripped then some 1000 else none
  match Decl.parseDecimal s with
  | some (m, sc) =>
    if m ≥ 0 && sc > 0 then return some ((m * 1000 / sc).toNat) else return none
  | none => return none

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
    n == "block" || n == "par" || n == "framefoot" || n == "pagebreak"
      || ["section", "subsection", "subsubsection"].contains n
  | .par _ => true
  | .verb _ _ => true
  | .math display _ _ => display
  | .env n body _ =>
    if (Parse.inputEnvFile? n).isSome then bodyIsBlockList body.toList
    else
      blockEnvs.contains n || isMathEnv n
        || n == "tabular" || n == "tabular*"
        || reservedEnv.contains n || bodyIsBlockList body.toList
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

/-- Does an overlay command standing at `i` take the block path? Grouped
content is judged by its shape, exactly as an environment body is — a list
or a paragraph break inside `\onslide{...}` is block content wherever the
command stands. The open form (a spec with no group) steps the rest of the
scope, so it is block-level only where a paragraph has not begun; begun,
it steps the rest of its sentence inline. `\alt` (two groups) takes the
block path when either alternative is block-shaped. -/
private def overlayTakesBlocks (raws : Array Raw) (i : Nat) (curEmpty : Bool)
    (twoGroups : Bool) : Bool :=
  let j := skipSpaces raws (i + 1)
  let jg := if (raws[j]?.bind specWord?).isSome then skipSpaces raws (j + 1) else j
  match raws[jg]? with
  | some (.group g1 _) =>
    bodyIsBlock g1 ||
      (twoGroups && (match raws[skipSpaces raws (jg + 1)]? with
        | some (.group g2 _) => bodyIsBlock g2
        | _ => false))
  | _ => curEmpty && !twoGroups

private def sectionLevel : String → Option Nat
  | "section" => some 1
  | "subsection" => some 2
  | "subsubsection" => some 3
  | _ => none

/-- A declaration standing in a group applies to the rest of the group:
`\Huge`, `\bfseries`, `\centering`, a palette name used bare. -/
private def isDeclaration (ctx : Ctx) : Raw → Bool
  | .ctrl n _ =>
    n == "centering" || (declStyles.lookup n).isSome || (ctx.palette.find? n).isSome
  | _ => false

private def isParRaw : Raw → Bool
  | .par _ => true
  | .ctrl "par" _ => true
  | _ => false

private def isCenteringRaw : Raw → Bool
  | .ctrl "centering" _ => true
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
    diag ctx .E0304 s!"'\\{name}' needs a \{...} group" pos
    return (start, #[])

/-- The title content `\maketitle` sets, from what was declared, per the
`titlepage` style. A declared `separator` becomes a full-measure rule
between the title block (title, subtitle) and the author block (author,
institute, date), in the declared palette colour at the `separatorheight`
token's thickness — moloch's title separator. The inter-part spacing reads
the `subtitlegap`/`separatorgap`/`authorgap`/`institutegap` tokens (the
moloch bundle carries that theme's values); an after-gap materialises only
when a later part follows. A declared but empty part (`\date{}`) is
deliberately blank and sets nothing. -/
private def titleBlocks (ctx : Ctx) (st : ESt) : Array Block := Id.run do
  let tps : ElementStyle := (ctx.styles.find? "titlepage").getD {}
  let part (v : Option (Array Inline)) : Option (Array Inline) :=
    v.bind fun xs => if xs.isEmpty then none else some xs
  let push (inner : Array Block) (before : Option SymGlue) (b : Block) : Array Block :=
    match before, inner.isEmpty with
    | some g, false => inner.push (.spaced g #[b])
    | _, _ => inner.push b
  let mut inner : Array Block := #[]
  let mut pending : Option SymGlue := none
  if let some xs := part st.title then
    -- The document title is a heading at level 0, not a decorated
    -- paragraph: the heading outline starts here (HTML §4.3.11 renders it
    -- as the one <h1>, markdown as the one #), and layout gives it the
    -- scale's LARGE step in the bold face — classes.dtx's \@maketitle sets
    -- {\LARGE \@title \par}. Starred: a title is never numbered.
    inner := push inner none (.section 0 true xs)
  if let some xs := part st.subtitle then
    inner := push inner (ctx.tokens.find? "subtitlegap") (.para #[.styled (.size "large") xs])
  if let some (c, nm) := tps.separator then
    unless inner.isEmpty && (part st.author).isNone && (part st.institute).isNone
        && (part st.date).isNone do
      -- moloch's default titleseparator linewidth, when no token names one.
      let th := (ctx.tokens.find? "separatorheight").getD
        { width := Dim.Length.ofSp (Dim.pt 1 / 2) }
      inner := push inner none (.rule c nm th)
      pending := ctx.tokens.find? "separatorgap"
  if let some xs := part st.author then
    inner := push inner pending (.para xs)
    pending := ctx.tokens.find? "authorgap"
  if let some xs := part st.institute then
    inner := push inner pending (.para #[.styled (.size "small") xs])
    pending := ctx.tokens.find? "institutegap"
  if let some xs := part st.date then
    inner := push inner pending (.para xs)
  -- A separator with nothing else declared is no title page at all.
  match inner with
  | #[.rule _ _ _] => return #[]
  | _ => return inner

/-- `\tokens{...}`: named lengths. Entries are walked one at a time so a
token may be defined by scaling an earlier one (`sep = 0.6 * rhythm`);
parsing the block in one shot would leave those references unresolved. -/
private def applyTokens (ctx : Ctx) (toks : Tokens) (src : String) (pos : Pos) :
    EM Tokens := do
  let mut acc : Tokens := toks
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | none =>
      diag ctx .E0320 s!"invalid entry in '\\tokens': {entry.quote}" pos
        (help := "entries look like: name = length")
    | some (key, valueSrc) =>
      -- A redeclared token replaces the earlier entry, so a later
      -- declaration overrides — a theme's defaults included. Entries
      -- already derived from the old value keep it: references resolve
      -- when the entry is read, in declaration order.
      match Decl.parseValue valueSrc acc.entries with
      | some (.glue g) => acc := acc.declare key g
      | some (.dim d) => acc := acc.declare key { width := Dim.Length.ofSp d }
      | some v =>
        modify fun st => { st with
          diags := st.diags.push (Decl.wrongType ctx.file "tokens" key
            "a length (10pt, 1.5ex, 0.6 * other)" v pos) }
      | none =>
        -- The expression parser's own verdict names the defect: an
        -- unknown token errors as itself, never resolving to zero.
        let detail := if Decl.looksLikeExpr valueSrc then
            match Decl.parseLengthExpr acc.entries valueSrc with
            | .error e => s!": {e}"
            | .ok _ => ""
          else ""
        diag ctx .E0321 s!"cannot read length for '{key}': {valueSrc.quote}{detail}" pos
          (help := "lengths look like 10pt, 1.5ex, 2em, a + 2b, or 0.6 * other-token")
  return acc


/-- `\palette{...}`: named colours. Every entry becomes usable both as
`\textcolor{name}{...}` and as a bare `\name` declaration. Parses its own
entries one at a time — a value may be a mix expression (`black!2`,
`accent!50!black`) over the entries declared so far, which a generic
pre-parse would reject. A redeclared name replaces the earlier entry: a
later declaration overrides, which is what lets a document override a
theme's defaults. -/
private def applyPalette (ctx : Ctx) (pal : Palette) (src : String)
    (pos : Pos) (decorative : Bool := false) : EM Palette := do
  let mut pal := pal
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | none =>
      diag ctx .E0320 s!"invalid entry in '\\palette': {entry.quote}" pos
        (help := "entries look like: name = #RRGGBB")
    | some (key, valueSrc) =>
      if !key.toList.all Decl.isIdentChar then
        diag ctx .E0320 s!"invalid key in '\\palette': {entry.quote}" pos
          (help := "entries look like: name = #RRGGBB")
      else if builtinNames.contains key then
        diag ctx .E0303 s!"palette name '{key}' collides with a built-in command" pos
      else if key == "covered" && (valueSrc.endsWith "\\%" || valueSrc.endsWith "%") then
        -- `covered = 38\%`: cover each colour to 38% of itself over the
        -- page (beamer's \setbeamercovered{transparent=38}). TeX comments
        -- make a bare % unwritable, so the escaped spelling is the
        -- declared one; the raw source shows it as `\%`. A colour value
        -- stays accepted below as the cover of uncoloured runs.
        let digits := if valueSrc.endsWith "\\%" then (valueSrc.dropEnd 2).toString
          else (valueSrc.dropEnd 1).toString
        match (digits.trimAscii.toString).toNat? with
        | some n =>
          if 1 ≤ n && n ≤ 99 then
            pal := { pal with coveredFraction := some n }
          else
            diag ctx .E0332 s!"covered fraction must be 1–99 percent, got '{valueSrc}'" pos
              (help := "the fraction of each covered colour kept over the page; the default is 38\\%")
        | none =>
          diag ctx .E0321 s!"cannot read covered fraction: {valueSrc.quote}" pos
            (help := "a percentage like: covered = 38\\%")
      else
        let put (pal : Palette) (c : Color) : Palette :=
          pal.declare key c decorative
        match Decl.parseValue valueSrc with
        | some (.color r g b) => pal := put pal { r := r, g := g, b := b }
        | some (.cmyk c m y k) => pal := put pal (Ir.Color.ofCmyk c m y k)
        | v? =>
          -- A name, an alias, or a mix: all read against what is declared
          -- so far, so two names that must never drift apart share a value.
          match pal.resolve valueSrc with
          | some c => pal := put pal c
          | none =>
            match v? with
            | some (.ident other) =>
              diag ctx .E0326 s!"'{other}' is not in the palette" pos
                (help := s!"aliases read earlier entries: declare \\palette\{ {other} = #RRGGBB } first")
            | some v =>
              modify fun st => { st with
                diags := st.diags.push (Decl.wrongType ctx.file "palette" key
                  "a color like #7C3AED" v pos) }
            | none =>
              diag ctx .E0321 s!"cannot read colour for '{key}': {valueSrc.quote}" pos
                (help := "colours are #RRGGBB, a palette name, or a mix like accent!50!black")
  return pal


/-- Elaborate raw items as a block sequence. -/
partial def elabBlocks (ctx : Ctx) (raws : Array Raw) : EM (Array Block) := do
  -- Shadowed mutable: a body declaration (`\palette`, `\tokens`) applies to
  -- the content elaborated after it in this scope and inside it, the way
  -- LaTeX's \colorlet and \setlength take effect where they stand.
  let mut ctx := ctx
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
        | .ctrl "centering" _ => true
        | .ctrl "pause" _ => true
        | .ctrl "framefoot" _ => true
        | .ctrl "pagebreak" _ => true
        -- Display math is its own centred block, as LaTeX sets a display:
        -- the paragraph splits around it. Inline `$...$` stays in its
        -- sentence.
        | .math display _ _ => display
        -- A note opening a paragraph is its own block; one met mid-sentence
        -- flows on inline, where it stashes for the enclosing frame instead
        -- of splitting the paragraph.
        | .ctrl "note" _ => cur.isEmpty
        | .ctrl n _ =>
          (sectionLevel n).isSome ||
          -- A declaration between paragraphs stands at block level.
          declCtrl.contains n ||
          -- A user command whose body produces blocks is itself a boundary.
          (match lookupUser ctx n with
           | some (_, cmd) => bodyIsBlock cmd.body
           | none =>
             ((overlayCtrls.contains n || n == "alt") &&
               overlayTakesBlocks raws i cur.isEmpty (n == "alt")) ||
             titleCtrls.contains n || n == "maketitle" || n == "titlepage"
               || n == "logo")
        | .group body _ =>
          -- A scope group carrying a `\centering` declaration is a block
          -- scope: the declaration needs blocks to centre, and the group's
          -- edge is exactly how far it reaches. An argument group is the
          -- command's, as in the par splice above.
          body.any isCenteringRaw && !isArgument cur
        | .env n body _ =>
          -- The synthetic \input wrapper is provenance, not structure: an
          -- inline fragment splices into the paragraph that includes it,
          -- and only a file holding block content breaks one. An unknown
          -- environment is judged the same way — its wrapper is unknowable,
          -- so its body's shape decides, and an inline body stays in its
          -- sentence.
          if (Parse.inputEnvFile? n).isSome then bodyIsBlock body
          else
            blockEnvs.contains n || isMathEnv n
              || n == "tabular" || n == "tabular*"
              || reservedEnv.contains n
              || (match lookupUserEnv ctx n with
                  | some (_, env) =>
                    -- A defined wrapper is judged by everything it will
                    -- produce: either half being block-shaped makes the
                    -- whole a block, as the content does.
                    bodyIsBlock env.beginBody || bodyIsBlock env.endBody
                  | none => false)
              || bodyIsBlock body
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
        | .math _ body mpos =>
          -- A display formula: one centred block of its own, so it
          -- participates in the block machinery like any other line.
          i := i + 1
          let inl ← elabMathInline ctx true body mpos
          blocks := blocks.push (.center #[.para #[inl]])
        | .ctrl "centering" _ =>
          -- The declaration form of \begin{center}: the rest of this scope
          -- centres. Text flushed just above stays uncentred — LaTeX would
          -- re-align the whole broken paragraph; this engine centres from
          -- the declaration on.
          i := i + 1
          let inner ← elabBlocks ctx (raws.extract i raws.size)
          i := raws.size
          unless inner.isEmpty do
            blocks := blocks.push (.center inner)
        | .ctrl "pause" _ =>
          -- The rest of this scope reveals one step later. Numbering is
          -- cumulative through nesting: each pause raises the base its
          -- successors count from, so pending content stays pending.
          i := i + 1
          let inner ← elabBlocks { ctx with stepBase := ctx.stepBase + 1 }
            (raws.extract i raws.size)
          i := raws.size
          unless inner.isEmpty do
            blocks := blocks.push (.step (ctx.stepBase + 2) none inner)
        | .ctrl "note" npos =>
          -- \note[placement]<spec>{...}: the placement and the spec are
          -- ignored with a note saying so; the body is the side channel,
          -- never slide content.
          i := i + 1
          if let .took _ := scanBracketArg raws i npos then
            warnOnce ctx "note:options" .N0102
              "'\\note' placement and overlay options are ignored: the note is \
a side channel, never slide content" npos
          let (j, _, _) ← skipOptArg ctx "note" raws i npos
          i := j
          let js := skipSpaces raws i
          if (raws[js]?.bind specWord?).isSome then
            warnOnce ctx "note:options" .N0102
              "'\\note' placement and overlay options are ignored: the note is \
a side channel, never slide content" npos
            i := js + 1
          let j2 := skipSpaces raws i
          match raws[j2]? with
          | some (.group nbody _) =>
            i := j2 + 1
            blocks := blocks.push (.note (← elabBlocks { ctx with noteBody := true } nbody))
          | _ =>
            warnSkippedDecl ctx "note" npos
        | .group gbody _ =>
          -- A centering scope group: its own block sequence, so the
          -- declaration stops at the closing brace.
          i := i + 1
          blocks := blocks ++ (← elabBlocks ctx gbody)
        | .ctrl "framefoot" fpos =>
          -- The per-frame footer note (beamer's `frame footer` template,
          -- through compat): sets the chrome footer's left slot for the
          -- frames that follow; an empty group clears it.
          i := i + 1
          let j := skipSpaces raws i
          match raws[j]? with
          | some (.group fbody _) =>
            i := j + 1
            blocks := blocks.push (.framefoot (← elabInlines ctx fbody))
          | _ =>
            diag ctx .E0304 "'\\framefoot' needs one group of inline content" fpos
        | .ctrl "palette" dpos =>
          -- Legal in the body as in LaTeX (`\colorlet` rewrites to it):
          -- the entries apply from here on, and the document palette both
          -- backends and the contrast checks read carries them.
          i := i + 1
          let mut decorative := false
          let mut skipBlock := false
          let mut j := skipSpaces raws i
          if let some (.sym '[' _) := raws[j]? then
            let mut opt : Array Raw := #[]
            let mut k := j + 1
            for _ in [k:raws.size + 1] do
              match raws[k]? with
              | some (.sym ']' _) => k := k + 1; break
              | some r' => opt := opt.push r'; k := k + 1
              | none => break
            for e in Decl.splitEntries (rawSrc opt) do
              if e == "decorative" then
                decorative := true
              else
                diag ctx .W0316 s!"unknown option in '\\palette': {e.quote}; block skipped" dpos
                  (help := "options: decorative")
                skipBlock := true
            j := skipSpaces raws k
          match raws[j]? with
          | some (.group gbody _) =>
            i := j + 1
            unless skipBlock do
              let pal ← applyPalette ctx ctx.palette (rawSrc gbody) dpos
                (decorative := decorative)
              ctx := { ctx with palette := pal }
              modify fun st => { st with bodyPalette := some pal }
          | _ =>
            diag ctx .E0304 "'\\palette' needs a {...} block" dpos
        | .ctrl "tokens" dpos =>
          -- `\setlength` mid-document rewrites here; same door as above.
          i := i + 1
          let j := skipSpaces raws i
          match raws[j]? with
          | some (.group gbody _) =>
            i := j + 1
            let tk ← applyTokens ctx ctx.tokens (rawSrc gbody) dpos
            ctx := { ctx with tokens := tk }
            modify fun st => { st with bodyTokens := some tk }
          | _ =>
            diag ctx .E0304 "'\\tokens' needs a {...} block" dpos
        | .ctrl "pagebreak" _ =>
          -- The declared page boundary; adjacent boundaries never make a
          -- blank page (the page builder closes only pages that hold
          -- something).
          i := i + 1
          blocks := blocks.push .pagebreak
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
            diag ctx .E0304 "'\\block' needs a {body}" pos
        | .ctrl n pos =>
          i := i + 1
          if declCtrl.contains n then
            -- A native declaration met in the body is never "unknown": it
            -- is ours, misplaced. `\palette` and `\tokens` have arms above;
            -- the rest configure the whole document and are read only in
            -- the preamble, so the declaration is skipped with its block,
            -- named as what it is.
            warnOnce ctx ("ctrl:" ++ n) .W0340
              s!"'\\{n}' is a declaration; in the body it is ignored" pos
              (help := "declare it in the preamble, before '\\begin{document}'")
            let (j, unclosed) := skipReservedArgs raws i pos (maxGroups := 2)
            if let some bpos := unclosed then
              warnUnclosed ctx s!"'\\{n}'" bpos
            i := j
          else
          match lookupUser ctx n with
          | some (k, cmd) =>
            -- Block-producing user command: bind its arguments, then
            -- elaborate the body as blocks so `\block` inside a definition
            -- works instead of reporting E0312.
            let (bindings, j) ← takeArgs ctx cmd.params n raws i pos
            i := j
            let callCtx : Ctx := { ctx with limit := k, args := bindings }
            blocks := blocks ++ (← elabBlocks callCtx cmd.body)
          | none =>
          if overlayCtrls.contains n || n == "alt" then
            -- Block-level overlay: the step wrapper survives at block
            -- level, so a list or a multi-paragraph group inside
            -- \onslide<2->{...} steps whole — elaborated as blocks, never
            -- squeezed through a paragraph. A spec the model cannot number
            -- keeps the honest W0105 and the content stays shown. `\pause`
            -- inside the wrapped content counts from the wrapper's own
            -- step, so pending stays pending.
            let j := skipSpaces raws i
            let mut spec : Option (Nat × Option Nat) := none
            let mut jg := j
            match raws[j]?.bind specWord? with
            | some w =>
              jg := skipSpaces raws (j + 1)
              match overlayFrom w with
              | some p => spec := some p
              | none =>
                warnOnce ctx "spec:overlay" .W0105
                  s!"overlay specification '{w}' does not name a step; its \
content is shown on every step" pos
                  (help := "write a numbered spec: <2>, <2->, or <2-3>; incremental \
specs are not modelled")
            | none => pure ()
            if n == "alt" then
              let j3 := skipSpaces raws (jg + 1)
              match raws[jg]?, raws[j3]? with
              | some (.group ga _), some (.group gb _) =>
                i := j3 + 1
                match spec with
                | some (s, last) =>
                  let ia ← elabBlocks
                    { ctx with stepBase := max ctx.stepBase (s - 1) } ga
                  let ib ← elabBlocks ctx gb
                  blocks := blocks.push (.step s last ia)
                  blocks := blocks.push (.step 1 (some (s - 1)) ib)
                | none =>
                  blocks := blocks ++ (← elabBlocks ctx ga)
                  blocks := blocks ++ (← elabBlocks ctx gb)
              | _, _ =>
                diag ctx .E0304 "'\\alt' needs <spec>{content}{content}" pos
            else
              match raws[jg]? with
              | some (.group gbody _) =>
                i := jg + 1
                match spec with
                | some (s, last) =>
                  let inner ← elabBlocks
                    { ctx with stepBase := max ctx.stepBase (s - 1) } gbody
                  unless inner.isEmpty do
                    blocks := blocks.push (.step s last inner)
                | none =>
                  blocks := blocks ++ (← elabBlocks ctx gbody)
              | _ =>
                -- The open form: the rest of this scope steps. Bare
                -- \onslide (no spec) ends stepping — the rest simply flows.
                i := jg
                if let some (s, last) := spec then
                  let inner ← elabBlocks
                    { ctx with stepBase := max ctx.stepBase (s - 1) }
                    (raws.extract i raws.size)
                  i := raws.size
                  unless inner.isEmpty do
                    blocks := blocks.push (.step s last inner)
          else if titleCtrls.contains n then
            let (j, junk) ← takeTitleDecl ctx n raws i pos
            i := j
            -- The malformed run of an unclosed bracket is content here.
            if let some p ← mkPara ctx junk then
              blocks := blocks.push p
          else if n == "logo" then
            -- The declaration is legal in the body too, where beamer decks
            -- scope a logo to a frame (`\logo{...}` before it, `\logo{}`
            -- after): a stateful block the layout replays per page.
            let j := skipSpaces raws i
            match raws[j]? with
            | some (.group gbody _) =>
              i := j + 1
              blocks := blocks.push (.logo (← elabInlines ctx gbody))
            | _ =>
              diag ctx .E0304 "'\\logo' needs one group of inline content" pos
          else if n == "maketitle" || n == "titlepage" then
            if (← get).titleDone then
              -- LaTeX typesets the title once: \maketitle disables itself
              -- (classes.dtx, \global\let\maketitle\relax), which is also
              -- what keeps the document to one level-0 heading. Named,
              -- never silent.
              warnOnce ctx "ctrl:maketitle2" .W0322
                s!"a second '\\{n}' is ignored; the title is typeset once" pos
                (help := "LaTeX's \\maketitle disables itself after use (classes.dtx)")
            else
            let inner := titleBlocks ctx (← get)
            if inner.isEmpty then
              warnOnce ctx "ctrl:maketitle" .W0309
                s!"'\\{n}' with nothing declared; no title is set" pos
                (help := "declare \\title{...} (and \\author, \\date, ...) before it")
            else if ctx.slides then
              -- The title frame takes the golden split (moloch's
              -- `title page` template: `0pt plus 1.618fil` + `\vfil` above
              -- against `plus 1fil` below), and its horizontal alignment is
              -- the `titlepage` style's declaration: moloch sets its title
              -- matter ragged left; undeclared, the title page centres.
              modify fun st => { st with titleDone := true }
              let tps := (ctx.styles.find? "titlepage").getD {}
              let content := if tps.align == some "left" then inner else #[.center inner]
              blocks := blocks.push (.frame #[] false .golden content)
            else
              modify fun st => { st with titleDone := true }
              blocks := blocks.push (.center inner)
          else
            let level := (sectionLevel n).getD 1
            let mut starred := false
            if let some (.word "*" _) := raws[i]? then
              starred := true
              i := i + 1
            -- `\section[short]{long}`: the short form feeds furniture no
            -- backend consumes yet, and its bracket obeys the shared
            -- scanner. The malformed run of an unclosed bracket is content
            -- here, exactly as in the scanner's sibling paths.
            if let .took _ := scanBracketArg raws i pos then
              warnOnce ctx "section:short" .N0103
                s!"'\\{n}[short]' short title is unused: nothing consumes it yet" pos
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
                diag ctx .E0304 s!"'\\{n}' needs a \{title}" pos
        | .env n body pos =>
          i := i + 1
          if let some f := Parse.inputEnvFile? n then
            -- An \input file's blocks, elaborated under its own name so a
            -- diagnostic points at the file that holds the construct.
            blocks := blocks ++ (← elabBlocks { ctx with file := f } body)
          else if let some numbered := displayMathEnvs.lookup n then
            if numbered then
              warnOnce ctx "math:eqnum" .W0015
                s!"equation numbers are not rendered yet; '\{{n}}' sets unnumbered" pos
                (help := s!"'\{{n}*}' spells the unnumbered form, which renders the same")
            let inl ← elabMathInline ctx true body pos
            blocks := blocks.push (.center #[.para #[inl]])
          else if let some (kind, numbered) := alignEnvs.lookup n then
            let inl ← elabMathEnv ctx n kind numbered body pos
            blocks := blocks.push (.center #[.para #[inl]])
          else if n == "tabular" || n == "tabular*" then
            -- A formal table, booktabs-shaped by construction: the column
            -- spec drives `.table`'s columns, `&`/`\\` split cells and
            -- rows, and the rule commands become typed rules at their
            -- index. Elaboration delivers the rectangularity the layout
            -- trusts: a short row is padded, a long one widens the grid,
            -- warning either way (W0337).
            let mut k := skipSpaces body 0
            if n == "tabular*" then
              if let some (.group _ _) := body[k]? then
                warnOnce ctx "tabular:starwidth" .N0102
                  "'tabular*' total width is ignored: columns take their \
declared widths" pos
                k := skipSpaces body (k + 1)
            if let .took k' := scanBracketArg body k pos then
              warnOnce ctx "tabular:valign" .N0102
                "'tabular' [t]/[b] alignment is ignored: the table stands \
where written" pos
              k := skipSpaces body k'
            let mut cols : Array Ir.ColSpec := #[]
            let mut padL := true
            let mut padR := true
            match body[k]? with
            | some (.group spec _) =>
              let (cs, pl, pr, warns) := parseColSpec spec
              cols := cs
              padL := pl
              padR := pr
              for (key, msg, help) in warns do
                warnOnce ctx ("tabular:" ++ key) .W0104 msg pos
                  (help := if help.isEmpty then none else some help)
              k := k + 1
            | _ => diag ctx .E0304 s!"'\{{n}}' needs a \{column spec} group" pos
            let mut rows : Array (Array (Array Inline)) := #[]
            let mut rules : Array (Nat × Ir.TableRule) := #[]
            let mut cells : Array (Array Inline) := #[]
            let mut cellRaws : Array Raw := #[]
            let mut j := k
            let ruleNames := ["toprule", "midrule", "bottomrule", "hline",
              "cmidrule", "cline", "addlinespace"]
            for _ in [k:body.size] do
              if h' : j < body.size then
                match body[j] with
                | .ctrl "\\" bpos =>
                  cells := cells.push (← elabInlines ctx (trimRawEdges cellRaws))
                  cellRaws := #[]
                  rows := rows.push cells
                  cells := #[]
                  j := j + 1
                  -- `\\[len]`: declared space after the row, booktabs'
                  -- class-2 gap.
                  let j0 := skipSpaces body j
                  match scanBracketArg body j bpos with
                  | .took j' =>
                    let src := Parse.rawSrc (body.extract (j0 + 1) (j' - 1))
                    match Decl.parseLength src with
                    | some l => do
                      rules := rules.push (rows.size, .gap { width := l })
                      j := j'
                    | none =>
                      diag ctx .E0331 s!"unreadable length '{src}' in '\\\\[...]'" (some bpos)
                      j := j'
                  | _ => pure ()
                | .sym '&' _ =>
                  cells := cells.push (← elabInlines ctx (trimRawEdges cellRaws))
                  cellRaws := #[]
                  j := j + 1
                | .ctrl name rpos =>
                  if ruleNames.contains name &&
                      cellRaws.all isSpaceOrPar && cells.isEmpty then
                    j := j + 1
                    cellRaws := #[]
                    -- booktabs' optional [width] per rule is not modelled:
                    -- the three weights are the design, one source.
                    if let .took j' := scanBracketArg body j rpos then
                      warnOnce ctx "tabular:rulewidth" .N0102
                        s!"'\\{name}' [width] is ignored: rule weights come \
from the design tokens" rpos
                      j := j'
                    match name with
                    | "toprule" => rules := rules.push (rows.size, .top)
                    | "midrule" | "hline" => rules := rules.push (rows.size, .mid)
                    | "bottomrule" => rules := rules.push (rows.size, .bottom)
                    | "addlinespace" =>
                      rules := rules.push (rows.size,
                        .gap { width := Ir.defaultAddSpace })
                    | _ =>
                      -- `\cmidrule(lr){a-b}`, `\cline{a-b}`: the trim spec
                      -- lexes as one word, "(lr)"
                      let mut trimL := false
                      let mut trimR := false
                      if let some (.word w _) := body[j]? then
                        if w.startsWith "(" then
                          trimL := w.contains 'l'
                          trimR := w.contains 'r'
                          j := j + 1
                      match body[skipSpaces body j]? with
                      | some (.group g _) =>
                        j := skipSpaces body j + 1
                        match cmidRange (Parse.rawSrc g) with
                        | some (a, b) =>
                          rules := rules.push (rows.size, .cmid a b trimL trimR)
                        | none =>
                          diag ctx .E0304
                            s!"'\\{name}' needs a \{from-to} column range" (some rpos)
                      | _ =>
                        diag ctx .E0304
                          s!"'\\{name}' needs a \{from-to} column range" (some rpos)
                  else
                    cellRaws := cellRaws.push body[j]
                    j := j + 1
                | r' =>
                  cellRaws := cellRaws.push r'
                  j := j + 1
              else break
            if cellRaws.any (!isSpaceOrPar ·) || !cells.isEmpty then
              cells := cells.push (← elabInlines ctx (trimRawEdges cellRaws))
              rows := rows.push cells
            -- Rectangularity: every walk below trusts `cols.size`.
            let widest := rows.foldl (fun m r => max m r.size) cols.size
            if cols.size < widest then
              warnOnce ctx "tabular:wide" .W0337
                s!"a row carries {widest} cells but the column spec declares \
{cols.size}; the grid widens" pos
                (help := "declare one column type per cell: l, c, r, or p{width}")
              for _ in [cols.size:widest] do
                cols := cols.push { width := .natural, align := .left }
            if rows.any (·.size < cols.size) then
              warnOnce ctx "tabular:ragged" .W0337
                "a row carries fewer cells than the column spec; it is \
padded with empty cells" pos
            rows := Ir.padTableRows rows cols.size
            blocks := blocks.push (.table cols padL padR rows rules)
          else if n == "frame" then
            -- \begin{frame}[options]{title}: options are ignored with a
            -- note (fragile, plain say how beamer should cope, not what to
            -- say) except
            -- `standout`, which says what the frame IS, and `t`/`c`/`b`,
            -- which say how it distributes its leftover vertical space
            -- (beamer user guide §8.1; `c` is beamer's default); the title
            -- group counts only when it follows directly — a paragraph
            -- break before a group makes it content, which is where LaTeX's
            -- own argument scanning stops looking too.
            let mut k := 0
            let mut standout := false
            let mut valign : VAlign := .center
            for _ in [0:body.size] do
              let j0 := skipSpaces body k
              match scanBracketArg body k pos with
              | .took k' =>
                let inner := rawSrc (body.extract (j0 + 1) (k' - 1))
                for opt in (inner.splitOn ",").map (·.trimAscii.toString) do
                  match opt with
                  | "standout" => standout := true
                  | "t" => valign := .top
                  | "c" => valign := .center
                  | "b" => valign := .bottom
                  | other =>
                    -- fragile, plain, and friends say how beamer should
                    -- cope, not what to say: registered, never silent.
                    unless other.isEmpty do
                      warnOnce ctx ("frame:opt:" ++ other) .N0102
                        s!"frame option '{other}' is not modelled; ignored" pos
                k := k'
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
                    diag ctx .W0311 "this '\\frametitle' replaces the frame's earlier title"
                      (some fpos) (help := "the last one wins; remove the other '\\frametitle'")
                  title ← elabInlines ctx t
                  j := j + 2
                | r', _ =>
                  rest := rest.push r'
                  j := j + 1
              else break
            -- Notes met inside the frame's inline content drain to the
            -- frame's end: the side channel stays with its frame.
            modify fun st => { st with pendingNotes := #[] }
            let mut inner ← elabBlocks ctx rest
            let stash := (← get).pendingNotes
            modify fun st => { st with pendingNotes := #[] }
            for nb in stash do
              inner := inner.push (.note (← elabBlocks { ctx with noteBody := true } nb))
            blocks := blocks.push (.frame title standout valign inner)
          else if n == "itemize" || n == "enumerate" then
            let mut items : Array (Array Raw) := #[]
            let mut steps : Array (Option (Nat × Option Nat)) := #[]
            -- `\pause` between items steps the rest of the LIST, not just
            -- the rest of an item's own blocks: each item records how many
            -- pauses stand before it and reveals one step after the last.
            let mut pauses := 0
            let mut itemPauses : Array Nat := #[]
            let mut curItem : Array Raw := #[]
            let mut curStep : Option (Nat × Option Nat) := none
            let mut curPauses := 0
            let mut awaitSpec := false
            let mut seen := false
            let mut strayDiagged := false
            for item in body do
              match item with
              | .ctrl "item" _ =>
                if seen then
                  items := items.push curItem
                  steps := steps.push curStep
                  itemPauses := itemPauses.push curPauses
                curItem := #[]
                curStep := none
                curPauses := pauses
                awaitSpec := true
                seen := true
              | .ctrl "pause" _ =>
                -- Counted for the items that follow; kept in the item so a
                -- mid-item pause still steps the item's own remaining
                -- blocks.
                pauses := pauses + 1
                if seen then
                  curItem := curItem.push item
              | _ =>
                -- `\item<2->`: the spec directly after the item names the
                -- step its content reveals at, dim-not-hide (PLAN M5).
                if seen && awaitSpec && !isSpace item then
                  awaitSpec := false
                  if let some w := specWord? item then
                    match overlayFrom w with
                    | some s => curStep := some s
                    | none =>
                      warnOnce ctx "spec:overlay" .W0105
                        s!"overlay specification '{w}' does not name a step; its \
content is shown on every step" pos
                        (help := "write a numbered spec: <2>, <2->, or <2-3>; incremental \
specs are not modelled")
                    continue
                if seen then
                  curItem := curItem.push item
                else if !isSpaceOrPar item && !strayDiagged then
                  diag ctx .E0310 s!"content before the first '\\item'" pos
                  strayDiagged := true
            if seen then
              items := items.push curItem
              steps := steps.push curStep
              itemPauses := itemPauses.push curPauses
            let mut elabItems : Array (Array Block) := #[]
            for ((it, st?), p) in (items.zip steps).zip itemPauses do
              let inner ← elabBlocks { ctx with stepBase := ctx.stepBase + p } it
              elabItems := elabItems.push (match st? with
                | some (s, last) => #[.step s last inner]
                | none =>
                  if p > 0 then #[.step (ctx.stepBase + p + 1) none inner]
                  else inner)
            blocks := blocks.push (.list (n == "enumerate") elabItems)
          else if n == "center" then
            blocks := blocks.push (.center (← elabBlocks ctx body))
          else if n == "minipage" then
            -- A minipage is one column of declared width: the column model
            -- reused whole, never a parallel box model. LaTeX's signature
            -- is [pos][height][inner-pos]{width} (classes.dtx §minipage);
            -- the optionals position the box against a text baseline, and
            -- at block level there is no baseline, so they are noted and
            -- ignored exactly as the columns options are. An absolute
            -- width is the same loss a column has (W0314).
            let mut k := 0
            for _ in [0:3] do
              match scanBracketArg body k pos with
              | .took k' =>
                warnOnce ctx "minipage:options" .N0102
                  "'minipage' [pos] options are ignored: the box stands as a block, top-aligned"
                  pos
                k := k'
              | .unclosed bpos =>
                warnUnclosed ctx "'\\begin{minipage}'" bpos
                break
              | .content => break
            let m := skipSpaces body k
            let mut width : Option Nat := none
            let mut m2 := m
            if let some (.group wRaws _) := body[m]? then
              m2 := m + 1
              let src := rawSrc wRaws
              width := columnWidth src
              if width.isNone then
                warnOnce ctx "env:minipage-width" .W0314
                  s!"minipage width '{src}' is not a fraction of the text width; \
the box takes the whole measure" pos
                  (help := "write a factor like {0.5\\textwidth}")
            else
              diag ctx .E0304 "'\\begin{minipage}' needs a {width} group" pos
            blocks := blocks.push
              (.columns #[(width, ← elabBlocks ctx (body.extract m2 body.size))])
          else if n == "quote" || n == "quotation" then
            -- One node for both: they differ only in \listparindent
            -- (quotation indents each paragraph's first line), and the
            -- engine sets no paragraph indent anywhere yet — see the
            -- constructor's docstring.
            blocks := blocks.push (.quote (← elabBlocks ctx body))
          else if n == "figure" || n == "figure*" || n == "table" || n == "table*" then
            -- A single-pass engine has nowhere for a float to float: the
            -- float stands where written as a `.float`, `[placement]`
            -- ignored with a note saying so. Its caption keeps its source
            -- side — before the content it stands above, the table
            -- convention — and becomes the alt text of the images it
            -- captions; float numbering is not modelled yet (PLAN M8).
            let kind : Ir.FloatKind :=
              if n == "table" || n == "table*" then .table else .figure
            let mut k := 0
            for _ in [0:body.size] do
              match scanBracketArg body k pos with
              | .took k' =>
                warnOnce ctx "figure:placement" .N0102
                  s!"'\{{n}}' [placement] is ignored: a single-pass engine \
has nowhere for a float to float" pos
                k := k'
              | .unclosed bpos =>
                warnUnclosed ctx s!"'\\begin\{{n}}'" bpos
                break
              | .content => break
            let mut rest : Array Raw := #[]
            let mut caption : Array Inline := #[]
            let mut capAbove := false
            let mut j := k
            for _ in [k:body.size] do
              if h' : j < body.size then
                match body[j] with
                | .ctrl "caption" cpos =>
                  j := j + 1
                  let (j2, _, _) ← skipOptArg ctx "caption" body j cpos
                  j := skipSpaces body j2
                  match body[j]? with
                  | some (.group t _) =>
                    unless caption.isEmpty do
                      diag ctx .W0311 s!"this '\\caption' replaces the {n}'s earlier caption"
                        (some cpos) (help := "the last one wins; remove the other '\\caption'")
                    caption ← elabInlines ctx t
                    capAbove := rest.all isSpaceOrPar
                    j := j + 1
                  | _ => diag ctx .E0304 "'\\caption' needs a {text} group" cpos
                | .ctrl "centering" _ =>
                  -- The float centres already; the declaration is satisfied.
                  j := j + 1
                | r' =>
                  rest := rest.push r'
                  j := j + 1
              else break
            let mut inner ← elabBlocks ctx rest
            unless caption.isEmpty do
              inner := Ir.setAltBlocks (Ir.plainText caption) inner
            blocks := blocks.push (.float kind capAbove inner caption)
          else if n == "columns" then
            -- `[T]`-and-friends alignment options are ignored with a note:
            -- columns are top-aligned (PLAN, M5). A column's width is its
            -- first group, a fraction of the text width; content standing
            -- outside any column keeps its place as ordinary blocks — never
            -- dropped.
            let mut k := 0
            for _ in [0:body.size] do
              match scanBracketArg body k pos with
              | .took k' =>
                warnOnce ctx "columns:options" .N0102
                  "'columns' alignment options are ignored: columns are top-aligned" pos
                k := k'
              | .unclosed bpos =>
                warnUnclosed ctx "'\\begin{columns}'" bpos
                break
              | .content => break
            let mut cols : Array (Option Nat × Array Block) := #[]
            let mut strayRaws : Array Raw := #[]
            let mut j := k
            for _ in [k:body.size] do
              if h' : j < body.size then
                match body[j] with
                | .env "column" cbody cpos =>
                  if strayRaws.any (!isSpaceOrPar ·) then
                    unless cols.isEmpty do
                      blocks := blocks.push (.columns cols)
                      cols := #[]
                    blocks := blocks ++ (← elabBlocks ctx strayRaws)
                  strayRaws := #[]
                  let m := skipSpaces cbody 0
                  let mut width : Option Nat := none
                  let mut m2 := m
                  if let some (.group wRaws _) := cbody[m]? then
                    m2 := m + 1
                    let src := rawSrc wRaws
                    width := columnWidth src
                    if width.isNone then
                      warnOnce ctx "env:column-width" .W0314
                        s!"column width '{src}' is not a fraction of the text width; \
the column shares the leftover" cpos
                        (help := "write a factor like {0.5\\textwidth}")
                  cols := cols.push (width, ← elabBlocks ctx (cbody.extract m2 cbody.size))
                | r' => strayRaws := strayRaws.push r'
                j := j + 1
              else break
            unless cols.isEmpty do
              blocks := blocks.push (.columns cols)
            if strayRaws.any (!isSpaceOrPar ·) then
              blocks := blocks ++ (← elabBlocks ctx strayRaws)
          else if n == "ifbackend" then
            -- `{ifbackend}{html,md}`: block content addressed to a subset
            -- of the backends. An unknown name is dropped from the set with
            -- W0323; a set that keeps no backend along its nesting path is
            -- E0334 — content nothing will emit. The body still elaborates
            -- and the node still carries it (the IR reflects the document);
            -- `Ir.keepFor` at each backend's entry is the one drop site,
            -- and `Ir.keepFor_covers` is why the diagnostic is sufficient.
            let j := skipSpaces body 0
            match body[j]? with
            | some (.group g gpos) =>
              let names := (((rawSrc g).splitOn ",").map (·.trimAscii.toString)).filter
                (!·.isEmpty)
              let mut targets : Array String := #[]
              for name in names do
                if Ir.backendNames.contains name then
                  targets := targets.push name
                else
                  diag ctx .W0323
                    s!"unknown backend '{name}' in '\\begin\{ifbackend}'; ignored"
                    (some gpos)
                    (help := s!"backends: {String.intercalate ", " Ir.backendNames}")
              let eff := ctx.backendTargets.filter (targets.contains ·)
              if eff.isEmpty then
                diag ctx .E0334
                  "this content is addressed to no backend; no output will carry it"
                  (some pos)
                  (help := "name at least one of pdf, html, md; a nested \
'\\begin{ifbackend}' intersects with its enclosing one; \
\\allow{E0334} accepts the loss")
              let inner ← elabBlocks { ctx with backendTargets := eff }
                (body.extract (j + 1) body.size)
              blocks := blocks.push (.only targets inner)
            | _ =>
              diag ctx .E0304 "'\\begin{ifbackend}' needs a {backends} group" pos
                (help := "write \\begin{ifbackend}{html} ... \\end{ifbackend}")
              blocks := blocks ++ (← elabBlocks ctx body)
          else if n == "nav" then
            -- `{nav}`: the navigation landmark — a group of links, content
            -- rather than a widget; the links inside are ordinary `\href`s.
            -- The optional argument declares the instance's own facts:
            -- `label` (its accessible name; ARIA Landmark Regions asks a
            -- repeated landmark for a unique label), `pin` (a viewport
            -- corner: two words, `bottom right`), `offset` (a length off
            -- both pinned edges), and `reveal` (`scroll`, or the scroll
            -- length after which the nav is fully revealed). `offset` and
            -- `reveal` ride the pin: without one they are named as ignored.
            let mut spec : Ir.NavSpec := {}
            let mut rest := body
            if let .took k := scanBracketArg body 0 pos then
              let j0 := skipSpaces body 0
              let inner := rawSrc (body.extract (j0 + 1) (k - 1))
              rest := body.extract k body.size
              let mut pinned : Option (Bool × Bool) := none
              let mut offset : Option Dim.SymGlue := none
              let mut reveal := false
              let mut revealBy : Option Dim.SymGlue := none
              for e in Decl.splitEntries inner do
                match Decl.splitEntry e with
                | some ("label", v) =>
                  spec := { spec with label := some v }
                | some ("pin", v) =>
                  let words := ((v.split Char.isWhitespace).toList.map
                    (·.toString)).filter (!·.isEmpty)
                  let vEdge := words.find? (fun w => w == "top" || w == "bottom")
                  let hEdge := words.find? (fun w => w == "left" || w == "right")
                  match vEdge, hEdge with
                  | some ve, some he =>
                    if words.length == 2 then
                      pinned := some (ve == "top", he == "left")
                    else
                      diag ctx .E0321
                        s!"cannot read a corner for 'pin' in 'nav': {v.quote}" (some pos)
                        (help := "a pin is a corner: two words, like \
pin = bottom right")
                  | _, _ =>
                    diag ctx .E0321
                      s!"cannot read a corner for 'pin' in 'nav': {v.quote}" pos
                      (help := "a pin is a corner: two words, like \
pin = bottom right")
                | some ("offset", v) =>
                  match Decl.parseGlue v with
                  | some g => offset := some g
                  | none =>
                    diag ctx .E0321
                      s!"cannot read a length for 'offset' in 'nav': {v.quote}" (some pos)
                      (help := "lengths look like 1.5em or 12pt")
                | some ("reveal", v) =>
                  if v.trimAscii.toString == "scroll" then
                    reveal := true
                  else
                    match Decl.parseGlue v with
                    | some g => reveal := true; revealBy := some g
                    | none =>
                      diag ctx .E0321
                        s!"cannot read 'reveal' in 'nav': {v.quote}" (some pos)
                        (help := "reveal = scroll shows the nav after one \
viewport of scrolling; a length (reveal = 300px) shows it after that much")
                | some (key, _) =>
                  let d := Decl.unknownKey ctx.file "nav" key
                    ["label", "pin", "offset", "reveal"] pos
                  modify fun st => { st with diags := st.diags.push d }
                | none => pure ()
              match pinned with
              | some (top, left) =>
                spec := { spec with pin := some {
                  top, left
                  offset := offset.getD {}
                  reveal
                  revealBy } }
              | none =>
                if offset.isSome || reveal then
                  let msg := "'nav' options 'offset' and 'reveal' ride a pin; \
ignored without one"
                  warnOnce ctx "nav:unpinned" .W0110 msg pos
                    (help := "declare the corner too: pin = bottom right")
            blocks := blocks.push (.nav spec (← elabBlocks ctx rest))
          else if let some (k, env) := lookupUserEnv ctx n then
            -- A defined wrapper at block level: the halves and the content
            -- each contribute their blocks, in order. An inline half becomes
            -- its own paragraph beside block content — the splice that would
            -- merge them re-elaborates raws under two argument scopes.
            let (bindings, j) ← takeArgs ctx env.params n body 0 pos
            let envCtx : Ctx := { ctx with
              limit := env.cmdLimit, envLimit := k, args := bindings }
            blocks := blocks ++ (← elabBlocks envCtx env.beginBody)
            blocks := blocks ++ (← elabBlocks ctx (body.extract j body.size))
            blocks := blocks ++ (← elabBlocks envCtx env.endBody)
          else if n == "tikzpicture" then
            -- The rendered subset: shapes evaluate here — loops unrolled,
            -- expressions reduced, colours resolved against the palette —
            -- and everything the subset cannot render is a named loss
            -- beside the shapes that did (W0334 outside the subset, E0333
            -- unreadable inside it), never one blanket W0307.
            let (pic, pdiags) := Picture.elabPicture ctx.palette body
            for (code, msg) in pdiags do
              warnOnce ctx ("picture:" ++ msg) code msg pos
                (help := "the rendered subset is \\fill...rectangle, \\node at, \
\\foreach, and \\pgfmath(truncate)setmacro")
            unless pic.shapes.isEmpty do
              blocks := blocks.push (.picture pic)
          else if reservedEnv.contains n then
            warnOnce ctx ("env:" ++ n) .W0307
              s!"'\{{n}}' is not implemented yet; its content is not rendered" pos
          else
            -- An unknown wrapper's decoration is unknowable; its body is
            -- not. The arguments on the `\begin` line go with the wrapper.
            warnOnce ctx ("env:" ++ n) .W0302 s!"unknown environment '\{{n}}'; its body is kept" pos
              (help := "\\defineenv{name}(...) {begin} {end} declares one")
            let (kept, unclosed, dropped) := dropEnvArgs body pos
            if let some bpos := unclosed then
              warnUnclosed ctx s!"'\\begin\{{n}}'" bpos
            warnDroppedArgs ctx n dropped pos
            blocks := blocks ++ (← elabBlocks ctx kept)
        | .verb s _ =>
          i := i + 1
          blocks := blocks.push (.verbatim none s)
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
    diag ctx .E0303 s!"malformed signature '{s}'" pos
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
        diag ctx .E0303 s!"invalid parameter name '{name}'" pos
          (help := "parameter names start with a letter")
      else
        match type? with
        | some t => params := params.push ⟨name, t, optional⟩
        | none =>
          diag ctx .E0303 s!"unknown parameter type '{ty}' for '{name}'" pos
            (help := "types: text | content")
    | _ =>
      diag ctx .E0303 s!"malformed parameter '{entry.trimAscii.toString}'" pos
        (help := "expected name: type")
  return params

/-- `\page{...}`: geometry. `size` names a standard page; `width`/`height`
override it; `margin` sets both axes, `vmargin`/`hmargin` one each. -/
private def applyPage (ctx : Ctx) (spec : PageSpec) (entries : Array Decl.Entry)
    (pos : Pos) : EM PageSpec := do
  -- A page dimension may be a declared token or an expression over them
  -- (`\geometry{paperheight=\bleedingheight}`), which parses as glue: it
  -- is a dimension when nothing font-relative or infinite rides in it —
  -- the page exists before any font is chosen.
  let asDim : Decl.Value → Option Sp
    | .dim d => some d
    | .glue g =>
      if g.width.em == 0 && g.width.ex == 0 && !g.fil then some g.width.sp else none
    | _ => none
  let mut spec := spec
  for e in entries do
    match e.key, e.value with
    | "size", .ident name =>
      match pageSizes.lookup name.toLower with
      | some (w, h) => spec := { spec with width := w, height := h }
      | none =>
        diag ctx .E0324 s!"unknown page size '{name}'" pos
          (help := s!"known sizes: {String.intercalate ", " (pageSizes.map (·.1))}")
    | "width", v =>
      if let some d := asDim v then spec := { spec with width := d }
      else modify fun st => { st with
        diags := st.diags.push (Decl.wrongType ctx.file "page" "width" "a dimension" v pos) }
    | "height", v =>
      if let some d := asDim v then spec := { spec with height := d }
      else modify fun st => { st with
        diags := st.diags.push (Decl.wrongType ctx.file "page" "height" "a dimension" v pos) }
    | "margin", v =>
      if let some d := asDim v then spec := { spec with vmargin := d, hmargin := d }
      else modify fun st => { st with
        diags := st.diags.push (Decl.wrongType ctx.file "page" "margin" "a dimension" v pos) }
    | "vmargin", v =>
      if let some d := asDim v then spec := { spec with vmargin := d }
      else modify fun st => { st with
        diags := st.diags.push (Decl.wrongType ctx.file "page" "vmargin" "a dimension" v pos) }
    | "hmargin", v =>
      if let some d := asDim v then spec := { spec with hmargin := d }
      else modify fun st => { st with
        diags := st.diags.push (Decl.wrongType ctx.file "page" "hmargin" "a dimension" v pos) }
    | "leading", .int n => spec := { spec with leading := n.toNat * 1000 }
    | "leading", .dim d =>
      -- A bare decimal like 1.04 reads as a dimension in points; the factor
      -- is what was meant.
      spec := { spec with leading := (d * 1000 / pt 1).toNat }
    | "leading", .ident f =>
      -- ...and one without a unit reaches here as a name.
      match Decl.parseDecimal f with
      | some (m, s) => spec := { spec with leading := (m * 1000 / s).toNat }
      | none => diag ctx .E0323 s!"'leading' in '\\page' expects a factor like 1.04, got '{f}'" pos
    | "parskip", .glue g => spec := { spec with parskip := some g }
    | "parskip", .dim d => spec := { spec with parskip := some { width := Dim.Length.ofSp d } }
    | "fontsize", .dim d =>
      -- The floor is the theorem's (`Layout.heading_hierarchy`): at every
      -- base of at least one point the heading hierarchy holds; below it
      -- the integer size arithmetic rounds the levels together, so the
      -- guard admits exactly what the guarantee covers.
      if d ≥ Dim.pt 1 then
        spec := { spec with fontSize := d }
      else
        diag ctx .E0323 "'fontsize' in '\\page' expects a dimension of at least 1pt" pos
    | "measure", .ident v =>
      -- `free`: the document takes responsibility for its line length, and
      -- the readable-band diagnostic (W0201) stays quiet.
      match v with
      | "free" => spec := { spec with measureChecked := false }
      | "checked" => spec := { spec with measureChecked := true }
      | _ =>
        diag ctx .E0323 s!"'measure' in '\\page' expects 'checked' or 'free', got '{v}'" pos
    | "bleed", .int 0 => spec := { spec with bleed := 0 }
    | "bleed", v =>
      if let some d := asDim v then spec := { spec with bleed := d }
      else modify fun st => { st with
        diags := st.diags.push (Decl.wrongType ctx.file "page" "bleed" "a dimension" v pos) }
    | "hyphenate", .ident v =>
      match v with
      | "on" | "true" => spec := { spec with hyphenate := some true }
      | "off" | "false" => spec := { spec with hyphenate := some false }
      | _ =>
        diag ctx .E0323 s!"'hyphenate' in '\\page' expects on or off, got '{v}'" pos
    | "justify", .ident v =>
      match v with
      | "on" | "true" => spec := { spec with justify := some true }
      | "off" | "false" => spec := { spec with justify := some false }
      | _ =>
        diag ctx .E0323 s!"'justify' in '\\page' expects on or off, got '{v}'" pos
    | key, v =>
      if key == "header" || key == "footer" then
        -- The feature exists, just not as a page key: running content is
        -- inline content, which a key/value block cannot carry.
        let cmd := if key == "header" then "\\runninghead" else "\\runningfoot"
        diag ctx .E0327 s!"'{key}' is not a '\\page' key" pos
          (help := s!"{cmd}\{...} declares it; \\hfill pushes content to the right")
      else if pageKeys.contains key then
        let expected := if key == "size" then "a page size name"
          else if key == "measure" then "'checked' or 'free'"
          else if key == "hyphenate" || key == "justify" then "on or off"
          else "a dimension"
        modify fun st => { st with
          diags := st.diags.push (Decl.wrongType ctx.file "page" key expected v pos) }
      else
        modify fun st => { st with
          diags := st.diags.push (Decl.unknownKey ctx.file "page" key pageKeys pos) }
  return spec

private def fontSlot? (name : String) : Option Nat :=
  match name with
  | "body" | "rm" => some 0
  | "sans" | "sf" => some 1
  | "mono" | "tt" => some 2
  | _ => none

/-- `body.bold`-style keys: `(slot, bold, italic)`. -/
private def fontVariantKey? (key : String) : Option (Nat × Bool × Bool) :=
  match key.splitOn "." with
  | [slotName, variant] => do
    let slot ← fontSlot? slotName
    match variant with
    | "upright" => some (slot, false, false)
    | "bold" => some (slot, true, false)
    | "italic" => some (slot, false, true)
    | "bolditalic" => some (slot, true, true)
    | _ => none
  | _ => none

/-- `\fonts{...}`: family names per slot, and `dir`, a directory of font
files shipped beside the document. `rm`/`sf`/`tt` are accepted as aliases so
a LaTeX habit does not become an error. A dotted key names one variant's
face (`body.bold = "X"`, fontspec's `BoldFont=`), which resolution honours
over the family's own variant. -/
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
    | "math", .str f => spec := { spec with math := some f }
    | "dir", .str d =>
      spec := if spec.dirs.contains d then spec else { spec with dirs := spec.dirs.push d }
    | key, v =>
      match fontVariantKey? key, v with
      | some variant, .str f =>
        spec := { spec with faces := spec.faces.push (variant, f) }
      | some _, _ =>
        modify fun st => { st with
          diags := st.diags.push (Decl.wrongType ctx.file "fonts" key "a quoted face name" v pos) }
      | none, _ =>
        if fontKeys.contains key then
          let expected := if key == "dir" then "a quoted directory" else "a quoted family name"
          modify fun st => { st with
            diags := st.diags.push (Decl.wrongType ctx.file "fonts" key expected v pos) }
        else
          modify fun st => { st with
            diags := st.diags.push (Decl.unknownKey ctx.file "fonts" key
              (fontKeys ++ ["<slot>.upright/.bold/.italic/.bolditalic"]) pos) }
  return spec

def styleKeys : List String :=
  ["font", "before", "after", "rule", "marker", "indent", "gap",
   "align", "separator", "hover", "focus", "motion"]

/-- `\style{element}{...}`: how an element kind looks. `font` and `marker`
are inline content and elaborate as such; the rest are lengths and a palette
colour. A length may name a token, so the entries are read one at a time
against the tokens declared so far. -/
private def applyStyle (ctx : Ctx) (styles : Styles) (element src : String) (pos : Pos) :
    EM Styles := do
  unless styleableElements.contains element do
    diag ctx .E0328 s!"'{element}' is not a styleable element" pos
      (help := s!"elements: {String.intercalate ", " styleableElements}")
    return styles
  let mut st : ElementStyle := (styles.find? element).getD {}
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | none =>
      diag ctx .E0320 s!"invalid entry in '\\style': {entry.quote}" pos
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
          diag ctx .E0321 s!"cannot read length for '{key}' in '\\style': {valueSrc.quote}" pos
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
        match ctx.palette.resolve valueSrc with
        | some c =>
          let name := if (ctx.palette.find? valueSrc).isSome then some valueSrc else none
          st := { st with rule := some (c, name) }
        | none =>
          match Decl.parseValue valueSrc with
          | some (.color r g b) => st := { st with rule := some ({ r := r, g := g, b := b }, none) }
          | some (.cmyk c m y k) =>
            st := { st with rule := some (Ir.Color.ofCmyk c m y k, none) }
          | _ => diag ctx .E0326 s!"'{valueSrc}' is not in the palette" pos
      | "separator" =>
        match ctx.palette.resolve valueSrc with
        | some c =>
          let name := if (ctx.palette.find? valueSrc).isSome then some valueSrc else none
          st := { st with separator := some (c, name) }
        | none =>
          match Decl.parseValue valueSrc with
          | some (.color r g b) => st := { st with separator := some ({ r := r, g := g, b := b }, none) }
          | some (.cmyk c m y k) =>
            st := { st with separator := some (Ir.Color.ofCmyk c m y k, none) }
          | _ => diag ctx .E0326 s!"'{valueSrc}' is not in the palette" pos
      | "align" =>
        match valueSrc.trimAscii.toString with
        | "left" => st := { st with align := some "left" }
        | "center" => st := { st with align := some "center" }
        | v =>
          diag ctx .E0323 s!"'align' in '\\style' expects left or center, got '{v}'" pos
      | "hover" =>
        match ctx.palette.resolve valueSrc with
        | some c =>
          let name := if (ctx.palette.find? valueSrc).isSome then some valueSrc else none
          st := { st with hover := some (c, name) }
        | none =>
          match Decl.parseValue valueSrc with
          | some (.color r g b) => st := { st with hover := some ({ r := r, g := g, b := b }, none) }
          | some (.cmyk c m y k) =>
            st := { st with hover := some (Ir.Color.ofCmyk c m y k, none) }
          | _ => diag ctx .E0326 s!"'{valueSrc}' is not in the palette" pos
      | "focus" =>
        match ctx.palette.resolve valueSrc with
        | some c =>
          let name := if (ctx.palette.find? valueSrc).isSome then some valueSrc else none
          st := { st with focus := some (c, name) }
        | none =>
          match Decl.parseValue valueSrc with
          | some (.color r g b) => st := { st with focus := some ({ r := r, g := g, b := b }, none) }
          | some (.cmyk c m y k) =>
            st := { st with focus := some (Ir.Color.ofCmyk c m y k, none) }
          | _ => diag ctx .E0326 s!"'{valueSrc}' is not in the palette" pos
      | "motion" =>
        -- A duration, in milliseconds: the one unit CSS transitions and
        -- the reduced-motion literature both speak in.
        let v := valueSrc.trimAscii.toString
        let digits := if v.endsWith "ms" then (v.dropEnd 2).toString.trimAscii.toString else v
        match digits.toNat? with
        | some ms => st := { st with motion := some ms }
        | none =>
          diag ctx .E0323
            s!"'motion' in '\\style' expects a duration in milliseconds, got '{v}'" pos
            (help := "write motion = 150ms")
      | _ =>
        modify fun st' => { st' with
          diags := st'.diags.push (Decl.unknownKey ctx.file "style" key styleKeys pos) }
  return styles.declare element st

/-- `\chrome{ footer = { left = \sectiontitle, right = \framenumber } }`:
page furniture as declared data. A slot names a per-page datum the engine
supplies — the current section's title, or the frame's own number — never
literal content (that is `\runningfoot`, which overrides the whole footer).
Redeclaring replaces, so a theme's chrome is a default exactly as its
palette is. -/
private def applyChrome (ctx : Ctx) (src : String) (pos : Pos) : EM Chrome := do
  let mut chrome : Chrome := {}
  let slotHelp := "slots are \\sectiontitle, \\framenumber, or \\framefraction"
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | none =>
      diag ctx .E0320 s!"invalid entry in '\\chrome': {entry.quote}" pos
        (help := "entries look like: footer = { left = \\sectiontitle, right = \\framenumber }")
    | some (key, valueSrc) =>
      if key == "footer" then
        match Decl.parseValue valueSrc with
        | some (.block inner) =>
          for slotEntry in Decl.splitEntries inner do
            match Decl.splitEntry slotEntry with
            | none =>
              diag ctx .E0320 s!"invalid entry in '\\chrome' footer: {slotEntry.quote}" pos
                (help := s!"entries look like: left = \\sectiontitle; {slotHelp}")
            | some (slotKey, slotVal) =>
              let v := slotVal.trimAscii.toString
              let v := if v.startsWith "\\" then (v.drop 1).toString else v
              let datum : Option ChromeSlot :=
                match v with
                | "sectiontitle" => some .sectionTitle
                -- The deck spelling and the beamer lineage's name one datum.
                | "framenumber" | "slidenumber" => some .frameNumber
                -- moloch's numbering=fraction: the n / N form.
                | "framefraction" => some .frameFraction
                | _ => none
              match datum with
              | none =>
                diag ctx .E0321
                  s!"cannot read the '\\chrome' footer slot '{slotKey}': {slotVal.quote}" pos
                  (help := slotHelp)
              | some d =>
                match slotKey with
                | "left" => chrome := { chrome with footerLeft := some d }
                | "right" => chrome := { chrome with footerRight := some d }
                | _ =>
                  modify fun st => { st with diags := st.diags.push (Decl.unknownKey
                    ctx.file "chrome footer" slotKey ["left", "right"] pos) }
        | some v =>
          modify fun st => { st with diags := st.diags.push (Decl.wrongType
            ctx.file "chrome" key
            "a block like { left = \\sectiontitle, right = \\framenumber }" v pos) }
        | none =>
          diag ctx .E0321 s!"cannot read value for 'footer' in '\\chrome': {valueSrc.quote}" pos
            (help := "footer = { left = \\sectiontitle, right = \\framenumber }")
      else
        modify fun st => { st with diags := st.diags.push (Decl.unknownKey
          ctx.file "chrome" key ["footer"] pos) }
  return chrome

/-- `\output{...}`: what to build, so a document needs no CLI options.
`formats` takes a bare comma list (`formats = pdf, html`), so entries are
walked by hand: an entry without `=` continues the list. -/
private def applyOutput (ctx : Ctx) (o0 : OutputSpec) (src : String) (pos : Pos) :
    EM OutputSpec := do
  let mut o := o0
  let mut inFormats := false
  let addFormat (o : OutputSpec) (f : String) : EM OutputSpec := do
    if ["pdf", "html", "md"].contains f then
      return { o with
        formats := if o.formats.contains f then o.formats else o.formats.push f }
    diag ctx .E0321 s!"'{f}' is not an output format" pos
      (help := "formats: pdf, html, md")
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
        diag ctx .E0321 s!"'{v}' is not a stylesheet mode" pos
          (help := "css: own, bulma, none")
    | some ("stylesheet", v) =>
      inFormats := false
      -- A path is a string; the quotes other declarations require are
      -- accepted but not demanded, as `formats` entries are bare too.
      let v := if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then
          String.ofList (v.toList.drop 1).dropLast
        else v
      o := { o with stylesheet := some v }
    | some ("md", v) =>
      inFormats := false
      let v := if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then
          String.ofList (v.toList.drop 1).dropLast
        else v
      o := { o with md := some v }
    | some (key, _) =>
      inFormats := false
      modify fun st => { st with
        diags := st.diags.push (Decl.unknownKey ctx.file "output" key
          ["formats", "css", "stylesheet", "md"] pos) }
    | none =>
      if inFormats then
        o ← addFormat o entry
      else
        diag ctx .E0320 s!"invalid entry in '\\output': {entry.quote}" pos
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
    | "url", .str s => m := { m with url := some s }
    | "image", .str s => m := { m with image := some s }
    | "favicon", .str s => m := { m with favicon := some s }
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
    diag ctx .E0325 s!"cannot read assertion: {src.trimAscii.toString.quote}" pos
      (help := some why)
    return none
  match words with
  | ["fonts.all_embedded"] =>
    return some { kind := .fontsAllEmbedded, span := some ⟨ctx.file, pos⟩ }
  | ["text.in_area"] =>
    return some { kind := .textInArea, span := some ⟨ctx.file, pos⟩ }
  | ["text.xheight", ">=", v] =>
    match Decl.parseValue v with
    | some (.dim d) => return some { kind := .minXHeight d, span := some ⟨ctx.file, pos⟩ }
    | _ => fail s!"'{v}' is not a dimension (like 1.4mm)"
  | ["pages", op, n] =>
    match cmpOp op, n.toInt? with
    | some o, some v => return some { kind := .pages o v, span := some ⟨ctx.file, pos⟩ }
    | none, _ => fail s!"'{op}' is not a comparison (== != <= < >= >)"
    | _, none => fail s!"'{n}' is not a whole number"
  | _ => fail "supported forms: pages <op> N, fonts.all_embedded, text.in_area, text.xheight >= <len>"

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
  let mut sawPage := false
  let mut fonts : FontSpec := {}
  let mut palette : Palette := {}
  let mut tokens : Tokens := {}
  let mut head : Option (Array Inline) := none
  let mut foot : Option (Array Inline) := none
  let mut runningFrom : Nat := 1
  let mut styles : Styles := {}
  let mut chrome : Chrome := {}
  let mut chromeDeclared := false
  let mut info : Meta := {}
  let mut output : OutputSpec := {}
  let mut asserts : Array Assertion := #[]
  let mut allow : Array String := #[]
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
          if docClass != "article" && docClass != "slides" && docClass != "card" then
            diag ctx .E0309 s!"unknown document class '{docClass}'" pos
              (help := "classes: article, slides, card")
        | _ =>
          diag ctx .E0304 "'\\documentclass' needs a {class}" pos
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
            modify fun st => { st with diags := st.diags.push (Diag.of .W0303
              s!"'\\{newName}' is built in; this definition is ignored"
              (some ⟨ctx.file, npos⟩)
              (help := "the built-in already does this; \\define it under another name")) }
          else
            match bodyRaws with
            | some b =>
              let params ← parseSig ctx (rawSrc sigRaws) pos
              ctx := { ctx with
                user := ctx.user.push ⟨newName, params, trimRaws b⟩
                limit := ctx.user.size + 1 }
            | none =>
              diag ctx .E0303 s!"'\\define \\{newName}' is missing its \{body}" pos
        | _ =>
          diag ctx .E0303 "expected '\\define \\name(...)  {body}'" pos
          i := j + 1
      | .ctrl "defineenv" pos =>
        -- `\defineenv{name}(sig) {begin} {end}`: the native spelling of
        -- `\newenvironment`. The halves are stored raw and elaborate at
        -- every `\begin{name}`, around its content, with the parameters
        -- bound from the groups after the `\begin`.
        i := i + 1
        let j := skipSpaces preamble i
        match preamble[j]? with
        | some (.group nameRaws npos) =>
          let envName := (rawSrc nameRaws).trimAscii.toString
          let mut sigRaws : Array Raw := #[]
          let mut k := j + 1
          let mut beginRaws : Option (Array Raw) := none
          for _ in [k:preamble.size] do
            match preamble[k]? with
            | some (.group b _) =>
              beginRaws := some b
              k := k + 1
              break
            | some r' =>
              sigRaws := sigRaws.push r'
              k := k + 1
            | none => break
          let k2 := skipSpaces preamble k
          let endRaws : Option (Array Raw) := match preamble[k2]? with
            | some (.group e _) => some e
            | _ => none
          i := if endRaws.isSome then k2 + 1 else k
          if builtinEnvNames.contains envName then
            modify fun st => { st with diags := st.diags.push (Diag.of .W0303
              s!"'\{{envName}}' is built in; this definition is ignored"
              (some ⟨ctx.file, npos⟩)
              (help := "the built-in already does this; \\define it under another name")) }
          else
            match beginRaws, endRaws with
            | some b, some e =>
              let params ← parseSig ctx (rawSrc sigRaws) pos
              ctx := { ctx with
                userEnvs := ctx.userEnvs.push
                  ⟨envName, params, trimRaws b, trimRaws e, ctx.limit⟩
                envLimit := ctx.userEnvs.size + 1 }
            | _, _ =>
              diag ctx .E0303 s!"'\\defineenv \{{envName}}' needs \{begin} and \{end}" pos
        | _ =>
          diag ctx .E0303 "expected '\\defineenv {name}(...) {begin} {end}'" pos
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
                | none => diag ctx .E0321 s!"'from' needs a page number, got {v.quote}" pos
              | _ =>
                diag ctx .E0320 s!"unknown option in \\{name}: {e.quote}" pos
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
            diag ctx .E0304 s!"'\\{name}' needs one group of inline content" pos
        else if name == "logo" then
          -- beamer's `\logo{...}`: one piece of inline content — normally an
          -- image — placed at the lower-right corner of every page carrying
          -- running content. The image inside is the same node
          -- `\includegraphics` makes; only the placement is the deck's.
          let j := skipSpaces preamble i
          match preamble[j]? with
          | some (.group body _) =>
            i := j + 1
            let content ← elabInlines ctx body
            modify fun st => { st with
              logo := if content.isEmpty then none else some content }
          | _ =>
            diag ctx .E0304 "'\\logo' needs one group of inline content" pos
        else if name == "palette" then
          -- `\palette[decorative]{...}`: the block's entries are declared
          -- deliberately low-contrast and exempt from the pairing check. An
          -- unrecognised option skips the block rather than applying it as
          -- the base palette -- a variant block applied as base would
          -- silently restyle the document.
          let mut j := skipSpaces preamble i
          let mut decorative := false
          let mut skipBlock := false
          if let some (.sym '[' _) := preamble[j]? then
            let mut opt : Array Raw := #[]
            let mut k := j + 1
            for _ in [k:preamble.size + 1] do
              match preamble[k]? with
              | some (.sym ']' _) => k := k + 1; break
              | some r => opt := opt.push r; k := k + 1
              | none => break
            for e in Decl.splitEntries (rawSrc opt) do
              if e == "decorative" then
                decorative := true
              else
                diag ctx .W0316 s!"unknown option in '\\palette': {e.quote}; block skipped" pos
                  (help := "options: decorative")
                skipBlock := true
            j := skipSpaces preamble k
          match preamble[j]? with
          | some (.group body _) =>
            i := j + 1
            unless skipBlock do
              let pal ← applyPalette ctx palette (rawSrc body) pos (decorative := decorative)
              palette := pal
              ctx := { ctx with palette := pal }
          | _ =>
            diag ctx .E0304 "'\\palette' needs a {...} block" pos
        else if name == "style" then
          let j := skipSpaces preamble i
          let j2 := skipSpaces preamble (j + 1)
          match preamble[j]?, preamble[j2]? with
          | some (.group elem _), some (.group body _) =>
            i := j2 + 1
            styles ← applyStyle ctx styles (rawSrc elem) (rawSrc body) pos
          | _, _ =>
            diag ctx .E0304 "'\\style' needs {element} and a {...} block" pos
        else if name == "allow" then
          -- `\allow{W0307, E0502}`: the document accepts the named losses.
          -- The teeth: an unknown code is an error (a typo must not grant a
          -- silent blanket), an entry that never fires warns (Main), and
          -- the acceptance always prints in the build summary.
          let j := skipSpaces preamble i
          match preamble[j]? with
          | some (.group body _) =>
            i := j + 1
            for entry in (rawSrc body).splitOn "," do
              let code := entry.trimAscii.toString
              if code.isEmpty then continue
              match DiagCode.ofString? code with
              | some c =>
                unless allow.contains c.code do
                  allow := allow.push c.code
              | none =>
                diag ctx .E0329 s!"'\\allow' names no diagnostic code '{code}'" pos
                  (help := "codes look like 'E0333'; each names the one loss it accepts")
          | _ =>
            diag ctx .E0304 "'\\allow' needs a {...} block of diagnostic codes" pos
        else if declCtrl.contains name then
          let j := skipSpaces preamble i
          match preamble[j]? with
          | some (.group body _) =>
            i := j + 1
            let src := rawSrc body
            if name == "theme" then
              -- A theme is a named bundle of typed values, installed here
              -- through the same replace-on-redeclare door the document's
              -- own declarations use. Everything after this site overrides:
              -- the theme is a default, never a lock.
              let tname := src.trimAscii.toString
              match Theme.find? tname with
              | some th =>
                let pal := th.palette.entries.foldl
                  (fun p (kc : String × Ir.Color) => p.declare kc.1 kc.2) palette
                -- The bundle's covered fraction rides with its palette,
                -- through the same replace-on-redeclare door: a document's
                -- own `covered = <n>\%` after this site overrides it.
                let pal := { pal with
                  coveredFraction := th.palette.coveredFraction <|> pal.coveredFraction }
                palette := pal
                ctx := { ctx with palette := pal }
                let tk := th.tokens.entries.foldl
                  (fun t (kg : String × Dim.SymGlue) => t.declare kg.1 kg.2) tokens
                tokens := tk
                ctx := { ctx with tokens := tk }
                for (element, st) in th.styles.entries do
                  -- Key-wise onto any entry the document already declared,
                  -- exactly as a `\style` block edits keys of the existing
                  -- entry.
                  let cur := (styles.find? element).getD {}
                  styles := styles.declare element { cur with
                    font := st.font <|> cur.font
                    before := st.before <|> cur.before
                    after := st.after <|> cur.after
                    rule := st.rule <|> cur.rule
                    marker := st.marker <|> cur.marker
                    indent := st.indent <|> cur.indent
                    gap := st.gap <|> cur.gap
                    align := st.align <|> cur.align
                    separator := st.separator <|> cur.separator }
                -- The bundle's chrome is typed data: installing it replaces,
                -- exactly as a document's own `\chrome` redeclaration does.
                if th.chrome.hasFooter then
                  chrome := th.chrome
              | none =>
                diag ctx .W0319 s!"unknown theme '{tname}'; the document is unthemed"
                  (some pos)
                  (help := s!"themes: {String.intercalate ", " Theme.names}")
            else if name == "assert" then
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
            else if name == "chrome" then
              -- Parses its own entries: slot values are `\sectiontitle`
              -- spellings a key/value pre-parse would reject.
              chrome ← applyChrome ctx src pos
              -- The author has named what the footer band holds: mixing
              -- the frame and physical sequences there is now declared
              -- (`footerSequenceDiags`).
              chromeDeclared := true
              -- Inert chrome would be a silent failure: only slides draw it.
              if docClass != "slides" then
                diag ctx .W0318
                  s!"'\\chrome' is slides furniture; the {docClass} class never draws it"
                  (some pos) (help := "\\runninghead / \\runningfoot are the page furniture")
            else
              let (entries, ds) := Decl.parseBlock ctx.file src pos name tokens.entries
              modify fun st => { st with diags := st.diags ++ ds }
              if name == "page" then
                page ← applyPage ctx page entries pos
                sawPage := true
              else if name == "fonts" then
                fonts ← applyFonts ctx fonts entries pos
              else
                info ← applyMeta ctx info entries pos
          | _ =>
            diag ctx .E0304 s!"'\\{name}' needs a \{...} block" pos
        else if titleCtrls.contains name then
          -- A declaration-only position: the malformed run is dropped with
          -- W0310 already pointing at it — the preamble has no content.
          let (j, _) ← takeTitleDecl ctx name preamble i pos
          i := j
        else if let some code := reservedCtrl.lookup name then
          warnOnce ctx ("ctrl:" ++ name) code s!"'\\{name}' is not implemented yet; skipped" pos
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
          warnOnce ctx ("ctrl:" ++ name) .W0301 s!"unknown command '\\{name}' in the preamble; skipped" pos
            (help := "\\define \\name(...) {body} declares it")
          let (j, unclosed) := skipReservedArgs preamble i pos (maxGroups := 9)
          match unclosed with
          | some bpos =>
            warnUnclosed ctx s!"'\\{name}'" bpos
            i := skipMalformedArgs preamble i pos
          | none => i := j
      | _ =>
        i := i + 1
        unless textDiagged do
          diag ctx .E0313 "only declarations may appear before '\\begin{document}'" none
          textDiagged := true
    else
      break
  -- The body size: `\page{ fontsize = ... }` wins, else the class option
  -- (`fontsize=11pt`, KOMA's spelling, or the standard classes' bare
  -- `11pt`), else the class default — beamer's documented 11pt for slides
  -- (user guide §18.2.1), the engine's 10pt base otherwise.
  if page.fontSize == ({} : PageSpec).fontSize then
    let optSize := (classOptions.splitOn ",").findSome? fun o =>
      let o := o.trimAscii.toString
      let o := if o.startsWith "fontsize=" then (o.drop "fontsize=".length).toString else o
      if o.endsWith "pt" then
        ((o.dropEnd 2).toString.toNat?).filter (· > 0) |>.map fun n => Dim.pt n
      else none
    match optSize with
    | some d => page := { page with fontSize := d }
    | none =>
      if docClass == "slides" then
        page := { page with fontSize := Ir.slidesFontSize }
  -- Slides fill beamer's stage unless the document declared its own
  -- geometry: a handout on letter portrait is not best effort, it is wrong.
  if docClass == "slides" then
    let dflt : PageSpec := {}
    if page.width == dflt.width && page.height == dflt.height then
      let ratio169 := (classOptions.splitOn ",").any
        fun o => o.trimAscii.toString == "aspectratio=169"
      let (w, h) := if ratio169 then Ir.slidesStage169 else Ir.slidesStage43
      page := { page with width := w, height := h }
    if page.hmargin == dflt.hmargin then
      page := { page with hmargin := Ir.slidesHMargin }
    if page.vmargin == dflt.vmargin then
      page := { page with vmargin := Ir.slidesVMargin }
  -- A card is trimmed from a sheet, so its defaults are the print trade's,
  -- not a guess: ISO/IEC 7810 ID-1 (85.60 × 53.98 mm, the credit-card size)
  -- unless the class option names the US (3.5 × 2 in) or Japanese
  -- (91 × 55 mm) trade size; margins are the print safe zone, inside which
  -- a drifting trim cannot cut. No hyphenation and no running furniture:
  -- a card is one face of display text, not a page of a run — which is
  -- also why the prose measure band (W0201) does not apply to it.
  else if docClass == "card" then
    let dflt : PageSpec := {}
    let opts := (classOptions.splitOn ",").map (·.trimAscii.toString)
    if page.width == dflt.width && page.height == dflt.height then
      let (w, h) :=
        if opts.contains "us" then (Dim.pt 252, Dim.pt 144)
        else if opts.contains "jis" then (Dim.mm 91, Dim.mm 55)
        else (Dim.mm100 8560, Dim.mm100 5398)
      page := { page with width := w, height := h }
    if page.hmargin == dflt.hmargin then
      page := { page with hmargin := Dim.mm 5 }
    if page.vmargin == dflt.vmargin then
      page := { page with vmargin := Dim.mm 5 }
    if page.hyphenate.isNone then
      page := { page with hyphenate := some false }
    -- Below the 40-character working minimum for justified text
    -- (Bringhurst, Elements 2.1.2), the measure is set ragged: at card
    -- width justification has no stretch to work with and the breaker is
    -- left choosing between overfull answers.
    if page.justify.isNone then
      page := { page with justify := some false }
    if head.isSome || foot.isSome then
      diag ctx .W0317
        "a card carries no running head or foot; the declaration is dropped" none
      head := none
      foot := none
  else if !sawPage then
    -- An undeclared letter page takes Bringhurst's text block for a 10pt
    -- text face, 26 picas, not the word-processor inch: the default must
    -- satisfy the measure band the engine checks (W0201). A document that
    -- declares any \page geometry keeps every value it named.
    page := { page with hmargin := (page.width - Ir.articleTextBlock) / 2 }
  ctx := { ctx with slides := docClass == "slides", styles := styles }
  let blocks ← elabBlocks ctx body
  -- Body declarations reach the document both backends read: a colour
  -- declared mid-document resolves in the HTML variables and is judged by
  -- the contrast walk like any other.
  let stBody ← get
  palette := stBody.bodyPalette.getD palette
  tokens := stBody.bodyTokens.getD tokens
  -- The logo may have been declared in either half; a card carries none.
  let mut logo := (← get).logo
  if docClass == "card" && logo.isSome then
    diag ctx .W0317
      "a card carries no logo; the declaration is dropped" none
    logo := none
  -- What a card guarantees, stated as the assertions the engine already
  -- enforces: content fits its faces, ink respects the safe margin, and
  -- the smallest type clears the fluent-reading floor at hand-held
  -- distance — an angular x-height of 0.2°, 1.4 mm at 40 cm (Legge &
  -- Bigelow 2011). Declaring an assertion of the same form is intent and
  -- silences the class default.
  if docClass == "card" then
    let faces : Int := max 1 (blocks.foldl (init := 0) fun n b =>
      match b with
      | .frame _ _ _ _ => n + 1
      | _ => n)
    unless asserts.any (fun a => match a.kind with | .pages _ _ => true | _ => false) do
      asserts := asserts.push {
        kind := .pages .le faces
        help := some s!"the card class asserts content fits its {faces} face(s); \
declare \\assert\{ pages <= N } to take control" }
    unless asserts.any (·.kind == .textInArea) do
      asserts := asserts.push {
        kind := .textInArea
        help := some "the margins are the print safe zone: ink past them risks \
the trim; declare \\assert{ text.in_area } to take control" }
    unless asserts.any (fun a => match a.kind with | .minXHeight _ => true | _ => false) do
      asserts := asserts.push {
        kind := .minXHeight Ir.cardXHeightFloor
        help := some "1.4mm x-height is the fluent-reading floor at hand-held \
distance (Legge & Bigelow 2011); declare \\assert{ text.xheight >= ... } to take control" }
  if trailing.any (!isSpaceOrPar ·) then
    diag ctx .W0001 "content after '\\end{document}' is ignored" none
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
    logo := logo
    runningFrom := runningFrom
    chrome := chrome
    chromeDeclared := chromeDeclared
    styles := styles
    info := info
    output := output
    asserts := asserts
    allow := allow
    body := blocks
  }

/-- Elaborate parsed input. LaTeX idioms are rewritten first, so a document
written for another engine compiles as written. -/
def runRaws (file : String) (raws : Array Raw) (earlier : Array Diag := #[]) :
    Doc × Array Diag :=
  let (raws, compatDiags) := Compat.rewrite file raws
  let (doc, st) := (elabDoc file raws).run {}
  let contrast := Contrast.docDiags doc
  let outline := Ir.outlineDiags doc
  let sequences := Ir.footerSequenceDiags doc
  (doc, earlier ++ compatDiags ++ st.diags ++ contrast ++ outline ++ sequences)

def run (file input : String) : Doc × Array Diag :=
  let (toks, lexDiags) := Lex.lex file input
  let (raws, parseDiags) := Parse.parse file toks
  runRaws file raws (lexDiags ++ parseDiags)

end LeanTex.Core.Elab
