import LeanTex.Core.Lex
import LeanTex.Core.Parse
import LeanTex.Core.MathParse
import LeanTex.Core.Ir
import LeanTex.Core.ListMark
import LeanTex.Core.Dim
import LeanTex.Core.Decl
import LeanTex.Core.Theme
import LeanTex.Core.Compat
import LeanTex.Core.Contrast
import LeanTex.Core.Picture
import LeanTex.Core.FaIcons
import LeanTex.Core.Bib

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
  /-- Where the definition stands, for the shadowing warning: the check
  runs once the final palette is known, long after this site scrolls by. -/
  span : Span
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
  /-- The document's resolved main locale, from the preamble's declared
  language: what the body walk's generated furniture (the References
  heading) is worded in. -/
  locale : Locale := Locale.en
  /-- Named lengths from `\tokens`. -/
  tokens : Tokens := {}
  /-- The resolved page in force for the body: what the engine length
  tokens (`paperwidth`, `textwidth`, …) and a token-named column width
  resolve against. Set once, after the class defaults are applied. -/
  page : Ir.PageSpec := {}
  /-- The engine's own length tokens, resolved from the final page: the
  body-side lookup `\setlength` expressions extend theirs with. -/
  engineTokens : Array (String × Dim.SymGlue) := #[]
  /-- Element styles declared so far (`\style`, theme bundles): the body
  reads `titlepage` at `\maketitle`. -/
  styles : Styles := {}
  /-- Inside mono/verbatim content, where punctuation stays literal. -/
  literalText : Bool := false
  /-- Inside a speaker note, absorbed as beamer absorbs it: a reserved
  character is literal text there, never a build error. -/
  noteBody : Bool := false
  /-- The position of the `\note` whose body is being elaborated, when
  `noteBody` is set: where E0359 names the note whose frame tried to carry
  another note. -/
  notePos : Option Pos := none
  /-- Inside a user command's or environment's argument, bound before its
  use is known: a reserved character there is the caller's literal token —
  the definition may place it in a key position (`\label{\k}`), where it
  is content read verbatim. A text placement keeps it too, a recorded
  leniency over LaTeX's error: dropping it mangled every key that
  travelled through a macro parameter. -/
  argBody : Bool := false
  /-- Overlay steps already opened by `\pause` in enclosing scopes: the next
  pause reveals at `stepBase + 1`. -/
  stepBase : Nat := 0
  /-- The document class is `slides`: `\maketitle` makes a title frame. -/
  slides : Bool := false
  /-- The class numbers its unstarred headings (article; classes.dtx
  §Sectioning). Slides and card headings never number, so a deck renders
  exactly as before. -/
  numberHeadings : Bool := false
  /-- The effective backend target set of the enclosing `{ifbackend}`
  nesting: every backend at the top, intersected at each conditional on the
  way in, so a nested conditional that empties the set is diagnosed where
  it stands (E0334) — the same walk `Ir.orphanFree` performs. -/
  backendTargets : List String := Ir.backendNames

/-- The numeral spellings a counter format may use, LaTeX's own set
(clsguide §Counters: `\arabic`, `\alph`, `\Alph`, `\roman`, `\Roman`);
rendering reuses the `ListMark` encoders, so a format's digits and the
list markers' cannot drift. -/
inductive SecNumStyle where
  | arabic
  | alph
  | uAlph
  | roman
  | uRoman
  deriving Repr, BEq

/-- One piece of a heading-number format — what `\renewcommand
{\thesubsection}{FAQ \arabic{subsection}.}` declares (classes.dtx
§Sectioning: `\the<counter>` is the counter's printed format, not a
macro): literal text, a numeral over a section counter, or another
level's own format (`\thesection` inside a subsection format). -/
inductive SecPart where
  | lit (s : String)
  | num (style : SecNumStyle) (level : Nat)
  | the (level : Nat)
  deriving Repr, BEq

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
  /-- The body of the last refused `\maketitle` redefinition (rule (b),
  W0361): read once more at the preamble's end — when the internals it
  names (`\@maketitle`, `\@toptitlebar`) are all defined — for the
  declarative title styling it may carry (`applyRefusedTitleStyle`). -/
  refusedTitleBody : Option (Array Raw) := none
  /-- Speaker-note bodies met inside inline content, where a block cannot
  stand, each with its `\note`'s position: the enclosing frame drains them
  to its end, so a mid-sentence `\note` neither splits its paragraph nor
  loses its words. -/
  pendingNotes : Array (Array Raw × Pos) := #[]
  /-- beamer's `\logo`, a declaration legal in the preamble and the body
  alike; the last one wins, as in beamer. -/
  logo : Option (Array Inline) := none
  /-- `\bibliographystyle`, wherever it appears — LaTeX reads it anywhere
  before the .aux is written; here the `\bibliography` marker met later
  carries it, so the declared name reaches resolution with the block. -/
  bibStyle : Option String := none
  /-- The palette in force in flow order — the last body `\palette` state,
  written by the declaration arm and read back at the top of every
  `elabBlocks` iteration, so a declaration inside a nested scope reaches
  the content after that scope closes: flow scope, no brace revert (the
  engine's `\centering` choice). `none` while the body declared nothing.
  The document palette both backends read as epoch 0 stays the
  preamble+theme state; the flow state rides the `.setPalette` blocks. -/
  flowPalette : Option Palette := none
  /-- Body-declared tokens (`\setlength` mid-document), same door. -/
  flowTokens : Option Tokens := none
  /-- The language in force from a block-level switch (`\selectlanguage`),
  `none` for the document's main language — the same from-here-forward
  flow state `inAppendix` uses. Paragraphs formed under it carry the
  attribute (`mkPara`). -/
  flowLang : Option String := none
  /-- Bumped by each body declaration: the cheap guard that lets the block
  loop skip re-reading the flow state per raw item. -/
  flowGen : Nat := 0
  /-- Scalar settings the preamble has declared so far, `(decl, key) ↦` the
  value as written: the store behind W0343, which fires only when the same
  key returns with a *different* value — a same-value repeat is harmless
  and stays silent. Holds document declarations only: a theme install never
  writes here, so overriding a theme's default never warns. -/
  seenScalars : Array (String × String × String) := #[]
  /-- Keyed entries the document itself has declared, `(decl, key)`: the
  store behind W0348, which fires only when a `\theme` install replaces a
  value standing from one of these. A theme install removes the keys it
  declares — the standing value is then the bundle's — so `\theme` after
  `\theme` never claims the document declared what a bundle did. -/
  declaredKeys : Array (String × String) := #[]
  /-- The section counters in flow order, levels 1–3: elaboration is one
  pass in document order, so stepping them here is exactly LaTeX's
  \refstepcounter sequence. -/
  secNums : Nat × Nat × Nat := (0, 0, 0)
  /-- Declared heading-number formats, one per level, last wins — the
  flow-order state a `\renewcommand{\the<counter>}{...}` writes wherever
  it stands, as LaTeX's redefinition applies from its own position. Empty
  for a level means the class default (classes.dtx §Sectioning). -/
  secFmts : Array (Nat × Array SecPart) := #[]
  /-- `\appendix` was declared: headings from here on letter (`A`, `B`, …)
  and the section counter restarted — a from-here-forward flow state, the
  `\logo`/body-`\palette` scope model, never a brace-scoped flag. -/
  inAppendix : Bool := false
  /-- The equation counter, per document (amsmath's `\numberwithin` is not
  modelled; a document that declares it keeps the per-document numbers). -/
  eqNum : Nat := 0
  /-- The number of the nearest preceding numbered thing — what a `\label`
  declared here binds to. A heading sets it for the flow after it. A
  captioned float never writes here: its number exists only after
  `Ir.numberFloats` runs on the finished body, so the labels under it are
  bound from the numbered IR (`Ir.floatLabelRows`), never predicted. -/
  refTarget : Option String := none
  /-- The label table in flow order: each key with the number it bound to.
  The first declaration of a key wins (LaTeX's behaviour); a second is
  W0350 at its own position. -/
  labels : Array (String × Option String) := #[]
  /-- Every `\ref`/`\eqref` site, for W0349 once the whole table is known:
  a reference may point forward, so it cannot be judged where it stands. -/
  refSites : Array (String × Pos) := #[]

abbrev EM := StateM ESt

/-- Build the diagnostic `diag` pushes, as a value: the one constructor
both the monadic emitter and the pure preamble steps (`PEvent.say`) share,
so a message exists in exactly one spelling. -/
private def diagOf (ctx : Ctx) (code : DiagCode) (msg : String) (pos : Option Pos)
    (help : Option String := none) : Diag :=
  Diag.of code msg (pos.map (⟨ctx.file, ·⟩)) help

private def diag (ctx : Ctx) (code : DiagCode) (msg : String) (pos : Option Pos)
    (help : Option String := none) : EM Unit :=
  modify fun st => { st with diags := st.diags.push (diagOf ctx code msg pos help) }

/-- One reporting effect a preamble apply step asks for — effects as data,
so the value half of a step is a pure function a theorem can range over.
`.say` is a diagnostic; `.scalar` goes through the `seenScalars` store
(W0343 when the same key returns with a different value); `.declared`
marks a key document-declared (W0348's store). Every constructor writes
only the reporting fields of `ESt` — the ones `ESt.sem` erases — which is
the whole point: an apply step's effect on the compared state is nothing. -/
inductive PEvent where
  | say (d : Diag)
  | scalar (decl key value : String) (pos : Pos)
  | declared (decl key : String)

/-- Apply one reporting event to the elaboration state, purely. -/
private def applyEvent (ctx : Ctx) (st : ESt) : PEvent → ESt
  | .say d => { st with diags := st.diags.push d }
  | .scalar decl key value pos =>
    let st := match st.seenScalars.find? (fun e => e.1 == decl && e.2.1 == key) with
      | some prev =>
        if prev.2.2 != value then
          { st with diags := st.diags.push (diagOf ctx .W0343
              s!"'{key}' in '\\{decl}' was already set to '{prev.2.2}'; this later value wins"
              (some pos)
              (help := s!"one value per key: keep the '{key} = ...' you mean")) }
        else st
      | none => st
    { st with seenScalars :=
      (st.seenScalars.filter fun e => !(e.1 == decl && e.2.1 == key)).push (decl, key, value) }
  | .declared decl key =>
    { st with declaredKeys :=
      if st.declaredKeys.contains (decl, key) then st.declaredKeys
      else st.declaredKeys.push (decl, key) }

/-- Fulfil a step's reporting events, in order, as one state update. -/
private def emitEvents (ctx : Ctx) (evs : Array PEvent) : EM Unit :=
  modify fun st => evs.foldl (applyEvent ctx) st

/-- A warning deduplicated by `key`: the same unsupported construct in forty
frames is one problem, not forty. `demote` delivers it as a note instead —
the spliced-`.sty` TeX-internal refusal (`Compat.styInternal`), correct and
unactionable per line, counted once by N0020 and listed under `-v`. -/
private def warnOnce (ctx : Ctx) (key : String) (code : DiagCode) (msg : String) (pos : Pos)
    (help : Option String := none) (demote : Bool := false) : EM Unit := do
  unless (← get).warnedUnknown.contains key do
    modify fun st => { st with warnedUnknown := st.warnedUnknown.push key }
    let d := diagOf ctx code msg (some pos) help
    modify fun st => { st with diags := st.diags.push (if demote then d.demote else d) }

/-- Reserved control words, and the code each skip earns — W0307 (pending,
a warning: a milestone owns the construct) when the skipped arguments carry
content, W0329 (config) when only layout or selection is lost. -/
def reservedCtrl : List (String × DiagCode) :=
  [("vspace", .W0329), ("noindent", .W0329),
   ("fontfallback", .W0329), ("figure", .W0307), ("pageref", .W0307)]

/-- Declarations that take a `{...}` block and are handled in the preamble. -/
def declCtrl : List String :=
  ["page", "pdfmeta", "assert", "fonts", "palette", "tokens", "style", "output",
   "theme", "chrome"]

/-- Preamble declarations that take one group of *inline content* rather than
a key/value block: running head and foot. -/
def runningCtrl : List String := ["runninghead", "runningfoot"]

def pageKeys : List String :=
  ["size", "width", "height", "margin", "vmargin", "hmargin",
   "textwidth", "textheight", "leading", "parskip",
   "measure", "fontsize", "bleed", "hyphenate", "justify", "protrusion",
   "expansion", "numbers",
   "furnituregap", "headsep", "footskip"]

/-- The `\page` keys that declare the page's physical extent. Exactly these
claim the page as declared (`sawPage` in `elabDoc`), keeping every value
named; a rhythm or policy key (`parskip`, `leading`, `fontsize`, `measure`,
`hyphenate`, `justify`) speaks to the text and must not silently forfeit
the Bringhurst text-block margin the undeclared page is owed. -/
def pageGeometryKeys : List String :=
  ["size", "width", "height", "margin", "vmargin", "hmargin",
   "textwidth", "textheight", "bleed"]

def metaKeys : List String :=
  ["title", "author", "subject", "keywords", "url", "image", "favicon",
   "language"]

def fontKeys : List String := ["body", "sans", "mono", "math", "rm", "sf", "tt", "dir"]

/-- Named page sizes, in sp: the ISO 216 A-series at TeX's big-point
rounding (A4 595 × 842 pt, A5 420 × 595 pt) and the ANSI/US office sizes
(letter 8.5 × 11 in, legal 8.5 × 14 in = 612 × 792 / 612 × 1008 pt). -/
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

/-- The NFSS font axes, one row per axis value with its two spellings — the
declaration (`{\bfseries …}`) and the one-argument text command
(`\textbf{…}`) — as fntguide §2.2's table of font-change commands gives
them (LaTeX2e font selection: family roman/sans/typewriter, series
medium/bold, shape upright/italic/slanted/small-caps, plus the default and
`\em`). `argStyles` and `declStyles` derive from this table, so the two
spellings cannot disagree; they once did as two hand lists (`\scshape` in,
`\textsc` out). The slanted shape sets italic: the engine's face model
carries upright and italic variants, the substitution NFSS itself makes
when a face has no slanted shape. -/
def fontAxes : List (String × String × Style) :=
  [("rmfamily", "textrm", .roman), ("sffamily", "textsf", .sans),
   ("ttfamily", "texttt", .mono),
   ("mdseries", "textmd", .medium), ("bfseries", "textbf", .bold),
   ("upshape", "textup", .upright), ("itshape", "textit", .italic),
   ("slshape", "textsl", .italic), ("scshape", "textsc", .smallcaps),
   ("normalfont", "textnormal", .normal), ("em", "emph", .emph)]

def argStyles : List (String × Style) :=
  fontAxes.map fun (_, arg, s) => (arg, s)

def declStyles : List (String × Style) :=
  (fontAxes.map fun (decl, _, s) => (decl, s)) ++
  [("sans", .sans)] ++
  (["tiny", "scriptsize", "footnotesize", "small", "normalsize", "large",
    "Large", "LARGE", "huge", "Huge"].map fun n => (n, Style.size n))

def escapes : List (String × String) :=
  [("%", "%"), ("{", "{"), ("}", "}"), ("$", "$"), ("&", "&"), ("#", "#"),
   ("_", "_"), ("~", "~"), (" ", " "),
   -- Control-symbol spaces, TeX's spelling. Fixed widths, so they are text.
   (",", "\u2009"), (":", "\u2005"), (";", "\u2004"),
   -- The named fixed spaces, TeXbook widths as Unicode's own space
   -- characters (plain.tex: \quad is 1 em, \qquad 2, \enspace ½;
   -- U+2003 EM SPACE, U+2002 EN SPACE). Rows here, not in
   -- `Lex.textSymbols`: a space command swallows the source space after
   -- it, as in TeX — its content already is the space.
   ("quad", "\u2003"), ("qquad", "\u2003\u2003"), ("enspace", "\u2002"),
   -- The logos set as their plain words (the kerned lowering is a
   -- rendering nicety, the name is the content), and textcomp's symbol
   -- commands beside their bare-symbol siblings in `Lex.textSymbols`.
   ("LaTeX", "LaTeX"), ("TeX", "TeX"),
   ("textdegree", "°"), ("texteuro", "€")]

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

/-- Built-ins a definition may never touch, whatever its body: the names
the walks' own shape depends on — grouping, definition machinery, block
boundaries, the reserved characters' escapes, the engine's declarations —
plus the underline family, whose refusal is the recorded divergence
(`builtinNames`' comment). Redefining one would not change what renders
(the dispatch reads these before any user definition), so refusing loudly
(W0303) is the honest answer. Every other protected name is in
`renderedBuiltins`, where rule (b) judges the body instead. -/
def structuralNames : List String :=
  ["begin", "end", "par", "define", "ifgiven", "documentclass",
   "underline", "uline", "ul", "varul",
   "item", "defineenv", "block", "framefoot", "pagebreak"] ++
  (escapes.map (·.1)) ++ (reservedCtrl.map (·.1)) ++ declCtrl

/-- Built-ins the engine renders that a document may nonetheless redefine,
as LaTeX allows — the names the block and inline dispatch handles by
literal arm only after `lookupUser` fails, so a registered definition
shadows them. `gateRedef` gates a redefinition of one by rule (b): it
wins only if its body, expanded once at the definition, is non-empty and
loses nothing; a body the engine cannot run would otherwise silently erase
the built-in's output (W0361), which is how a venue's `\renewcommand
{\maketitle}` of kernel internals erased a paper's title. -/
def renderedBuiltins : List String :=
  ["maketitle", "titlepage", "logo", "appendix", "note", "pause",
   "centering", "alt", "hfill", "ensuremath", "label", "ref", "eqref",
   "paragraph", "subparagraph", "href", "link", "url", "cite", "citep",
   "citet", "includegraphics", "faIcon", "pagenumber", "pagecount",
   "bibliography", "bibliographystyle", "textcolor",
   "refstepcounter", "stepcounter", "addtocounter", "setcounter",
   "section", "subsection", "subsubsection"] ++
  titleCtrls ++ overlayCtrls ++ runningCtrl ++ (argStyles.map (·.1)) ++
  (declStyles.map (·.1)) ++ (Lex.textSymbols.map (·.1))

/-- One verdict per name: no built-in is both unconditionally protected
and rule-(b) gated — a name in both would fire W0303 at `takeDefine` and
never reach the gate, making the registry's promise (a clean body wins) a
lie for exactly that name. -/
theorem structural_rendered_disjoint :
    (structuralNames.all fun n => !renderedBuiltins.contains n) = true := by
  decide +kernel

/-- The ratchet: every name W0303 used to protect still has a verdict —
unconditional refusal or the rule-(b) gate. Narrowing the structural core
cannot silently strip a built-in of both protections. -/
theorem builtin_verdict_total :
    (builtinNames.all fun n =>
      structuralNames.contains n || renderedBuiltins.contains n) = true := by
  decide +kernel

/-- TeX's accent commands the engine composes to NFC: the control-symbol
marks and the cedilla word, one table with .bib values (`Bib.accentTable`),
so a name renders identically in text and in a bibliography entry. -/
def accentMarkOf (name : String) : Option Char :=
  if name == "'" || name == "`" || name == "\"" || name == "^" || name == "~" then
    some name.front
  else if name == "c" then some 'c'
  else none

/-- The composed text of an accent command applied to what follows: the
first letter of an adjacent word (`\'elair` → "élair") or a one-letter
group (`\'{e}`). `none` — a shape or a pair the table does not know —
falls through to the ordinary dispatch, so nothing new is dropped and an
unknown pair still warns by name. -/
def accentCompose (mark : Char) (r : Parse.Raw) : Option String :=
  match r with
  | .word s _ =>
    match s.toList with
    | b :: rest =>
      let c := Bib.accentOf mark b
      if c == b then none else some (String.ofList (c :: rest))
    | [] => none
  | .group body _ =>
    match body.toList with
    | [.word s _] =>
      match s.toList with
      | [b] =>
        let c := Bib.accentOf mark b
        if c == b then none else some (String.ofList [c])
      | _ => none
    | _ => none
  | _ => none

/-- The one-character word commands (`\ss`, `\ae`, `\o`…), the same table
`.bib` values read (`Bib.charCommands`), folded into one lookup with the
escape table: both splice literal text. -/
def escapeOf (name : String) : Option String :=
  match escapes.lookup name with
  | some lit => some lit
  | none => (Bib.charCommands.find? (·.1 == name)).map (·.2)

/-- The declaration styles by name, plus the language marker (`@lang:fr`
→ `Style.lang "fr"` — Compat's rewrite of `\selectlanguage`, unforgeable
since `@` never lexes into a control word): both apply to the rest of
the scope, so one dispatch arm serves both. -/
def declStyleOf (name : String) : Option Ir.Style :=
  if name.startsWith "@lang:" then
    some (.lang ((name.drop "@lang:".length).toString))
  else declStyles.lookup name

/-- The block form of the language switch: the flow state update, outside
the block-walk knot so the arm inside costs it one call. A switch back to
the main language clears the attribute rather than tagging redundantly. -/
def flowLangUpdate (ctx : Ctx) (marker : String) (st : ESt) : ESt :=
  let tag := (marker.drop "@lang:".length).toString
  { st with flowLang := if tag == ctx.locale.tag then none else some tag }

/-- A paragraph under the flow language carries the attribute
(`langWrap_text`: the census is untouched). -/
def paraUnder (lang : Option String) (inlines : Array Ir.Inline) : Ir.Block :=
  match lang with
  | some tag => .para (Ir.langWrap tag inlines)
  | none => .para inlines

/-- Every palette role is invocable: a role is *defined by the palette* —
`\muted{Alex}` works with no `\newcommand`, because the palette arm of the
inline elaborator resolves any entry name — so no role can exist without
its command. The document door (`applyPalette`) already refuses a key that
collides with a built-in (E0303) and validates its characters; a theme's
bundle installs without that door, so the shipped bundles enter the
contract here: every key lexes as one control word (`Lex.nameChar`) and
collides with no registered built-in. Resolution *order* lives in
`elabInlines`, whose sanctioned recursion is opaque to proof — that every key
really reaches the palette arm is the paired executable check in
Tests.lean (`roleInvocationChecks`), an oracle, not a theorem. -/
theorem every_role_is_invocable :
    (Theme.builtin.all fun t => t.palette.entries.toList.all fun e =>
      e.1.toList.all Lex.nameChar && !builtinNames.contains e.1) = true := by decide

private def lookupUserGo (user : Array UserCmd) (name : String) :
    Nat → Option (Nat × UserCmd)
  | 0 => none
  | k + 1 =>
    if h : k < user.size then
      if user[k].name == name then some (k, user[k]) else lookupUserGo user name k
    else lookupUserGo user name k

private def lookupUser (ctx : Ctx) (name : String) : Option (Nat × UserCmd) :=
  lookupUserGo ctx.user name ctx.limit

private theorem lookupUserGo_lt {user : Array UserCmd} {name : String}
    {n k : Nat} {cmd : UserCmd} (h : lookupUserGo user name n = some (k, cmd)) :
    k < n := by
  fun_induction lookupUserGo user name n with
  | case1 => simp at h
  | case2 m hm heq => simp_all
  | case3 m hm heq ih => exact Nat.lt_succ_of_lt (ih h)
  | case4 m hm ih => exact Nat.lt_succ_of_lt (ih h)

/-- The visible-prefix bound expansion terminates by: a found command's
index is strictly below the limit the caller searched under. -/
private theorem lookupUser_lt {ctx : Ctx} {name : String} {k : Nat}
    {cmd : UserCmd} (h : lookupUser ctx name = some (k, cmd)) : k < ctx.limit :=
  lookupUserGo_lt h

/-- The latest visible definition wins, so `\renewenvironment` is one more
push, exactly as `lookupUser` treats commands. -/
private def lookupUserEnvGo (envs : Array UserEnv) (name : String) :
    Nat → Option (Nat × UserEnv)
  | 0 => none
  | k + 1 =>
    if h : k < envs.size then
      if envs[k].name == name then some (k, envs[k]) else lookupUserEnvGo envs name k
    else lookupUserEnvGo envs name k

private def lookupUserEnv (ctx : Ctx) (name : String) : Option (Nat × UserEnv) :=
  lookupUserEnvGo ctx.userEnvs name ctx.envLimit

private theorem lookupUserEnvGo_lt {envs : Array UserEnv} {name : String}
    {n k : Nat} {env : UserEnv} (h : lookupUserEnvGo envs name n = some (k, env)) :
    k < n := by
  fun_induction lookupUserEnvGo envs name n with
  | case1 => simp at h
  | case2 m hm heq => simp_all
  | case3 m hm heq ih => exact Nat.lt_succ_of_lt (ih h)
  | case4 m hm ih => exact Nat.lt_succ_of_lt (ih h)

private theorem lookupUserEnv_lt {ctx : Ctx} {name : String} {k : Nat}
    {env : UserEnv} (h : lookupUserEnv ctx name = some (k, env)) :
    k < ctx.envLimit :=
  lookupUserEnvGo_lt h

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
private def spanRaws (raws : Array Raw) (i : Nat) (p : Raw → Bool) : Nat :=
  if h : i < raws.size then
    if p raws[i] then spanRaws raws (i + 1) p else i
  else i
termination_by raws.size - i

private theorem spanRaws_ge (raws : Array Raw) (i : Nat) (p : Raw → Bool) :
    i ≤ spanRaws raws i p := by
  fun_induction spanRaws raws i p <;> omega

/-- The backward companion: the index before the trailing run satisfying `p`. -/
private def spanRawsEnd (raws : Array Raw) (p : Raw → Bool) : Nat := Id.run do
  let mut b := raws.size
  for _ in [0:raws.size] do
    match raws[b - 1]? with
    | some r => if b > 0 && p r then b := b - 1 else break
    | none => break
  return b

/-- The array between its edge runs of `p`. -/
private def trimBy (raws : Array Raw) (p : Raw → Bool) : Array Raw :=
  raws.extract (spanRaws raws 0 p) (spanRawsEnd raws p)

/-- Drop whitespace at both edges: a define body's braces delimit, the
padding inside them is not content. -/
private def trimRaws (raws : Array Raw) : Array Raw :=
  trimBy raws isSpaceOrPar

/-- `lookupUser` over an explicit table and prefix bound, for the math
expansion below, which threads its own decreasing `limit`. -/
private def lookupUserIn (user : Array UserCmd) (limit : Nat) (name : String) :
    Option (Nat × UserCmd) := Id.run do
  let mut k := limit
  for _ in [0:limit] do
    k := k - 1
    if h : k < user.size then
      if user[k].name == name then
        return some (k, user[k])
  return none

/-- Bind a user command's parameters from already-expanded raws, for the
math expansion: the raw-level twin of `takeArgs` — an optional binds from
`[...]`, a required from the next group or word — except that values stay
raws, because they splice back into a token stream the math parser reads.
Pure and forward: it only slices `rest`, never expands. -/
private def bindMathArgs (params : Array Param) (rest : Array Raw) :
    Array (String × Array Raw) × Array Raw := Id.run do
  let mut bindings : Array (String × Array Raw) := #[]
  let mut i : Nat := 0
  for p in params do
    if p.optional then
      let j := skipSpaces rest i
      match rest[j]? with
      | some (.sym '[' _) =>
        let mut body : Array Raw := #[]
        let mut k := j + 1
        for _ in [j:rest.size] do
          match rest[k]? with
          | some (.sym ']' _) =>
            k := k + 1
            break
          | some r =>
            body := body.push r
            k := k + 1
          | none => break
        i := k
        bindings := bindings.push (p.name, body)
      | _ => bindings := bindings.push (p.name, #[])
    else
      let j := skipSpaces rest i
      match rest[j]? with
      | some (.group body _) =>
        i := j + 1
        bindings := bindings.push (p.name, body)
      | some r =>
        i := j + 1
        bindings := bindings.push (p.name, #[r])
      | none =>
        bindings := bindings.push (p.name, #[])
  return (bindings, rest.extract i rest.size)

/-- Expand user commands (`\define`) inside a formula's raws: the one hook
where `MathParse` meets the elaborator's macro table, closing the
document-defined macro tail W0012 named formula by formula. The walk runs
right to left — the suffix is fully expanded before its head — so when a
command binds its arguments they are already macro-free splices, expanded
under the caller's visible prefix exactly as `takeArgs` elaborates them in
text. Termination is the definition-order rule that already terminates
text-mode expansion, made structural: a definition sees only definitions
before it, so the body expands under `k < limit` (the measure's first
component), and within one level the walk descends the raw list (the
second). No fuel and no escape hatch: the language stays terminating by
design. -/
private def expandMathList (user : Array UserCmd) (limit : Nat)
    (args : Array (String × Array Raw)) : List Raw → Array Raw
  | [] => #[]
  | .ctrl n pos :: rest =>
    let tail := expandMathList user limit args rest
    if let some (_, sub) := args.find? (·.1 == n) then
      sub ++ tail
    else
      match lookupUserIn user limit n with
      | some (k, cmd) =>
        if _h : k < limit then
          let (bindings, rest') := bindMathArgs cmd.params tail
          let body := expandMathList user k bindings cmd.body.toList
          body ++ rest'
        else
          #[Raw.ctrl n pos] ++ tail
      | none => #[Raw.ctrl n pos] ++ tail
  | .group body p :: rest =>
    let tail := expandMathList user limit args rest
    let inner := expandMathList user limit args body.toList
    #[Raw.group inner p] ++ tail
  | r :: rest =>
    let tail := expandMathList user limit args rest
    #[r] ++ tail
termination_by raws => (limit, sizeOf raws)
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    (have hb : sizeOf body = 1 + sizeOf body.toList := rfl; omega)

/-- One formula: parsed into math atoms when this slice can model it, kept
as source text with a warning naming the construct when it cannot — out of
scope is a named warning, never a silent drop. User commands expand first
(`expandMathList`), so a `\define`d macro renders instead of degrading its
formula. A ragged alignment row inside the formula (an `array`) is W0014:
padded with empty cells, named. -/
private def elabMathInline (ctx : Ctx) (display : Bool) (body : Array Parse.Raw)
    (pos : Pos) : EM Ir.Inline := do
  let expanded := expandMathList ctx.user ctx.limit #[] body.toList
  match MathParse.parseMath expanded with
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
  let expanded := expandMathList ctx.user ctx.limit #[] body.toList
  match MathParse.parseMathRows kind expanded with
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

/-- The index of the next `]` symbol at or past `k`, if any: the closing
half every bracket-argument collector shares, stated as an index so the
consumed extent is a fact the termination measure can read. -/
private def closeBracketFrom (raws : Array Raw) (k : Nat) : Option Nat :=
  if h : k < raws.size then
    if raws[k] matches .sym ']' _ then some k else closeBracketFrom raws (k + 1)
  else none
termination_by raws.size - k

private theorem closeBracketFrom_ge {raws : Array Raw} {k c : Nat}
    (h : closeBracketFrom raws k = some c) : k ≤ c ∧ c < raws.size := by
  fun_induction closeBracketFrom raws k with
  | case1 =>
    rename_i hk _
    simp only [Option.some.injEq] at h
    omega
  | case2 =>
    rename_i ih
    have := ih h
    omega
  | case3 => simp at h

/-- The one bracket-argument scan, shared by every consumer of an optional
`[...]`. An argument's `[` opens on `anchor`'s line — a bracket on a later
line is content, where LaTeX's own argument scanning stops looking too — and
it has a matching `]`. One that never closes is malformed content, never an
argument: consuming to the end of the scan would silently drop everything
after it, a frame body or the rest of a preamble included. `.took` carries
the index past the `]`; `.unclosed` consumes nothing and carries the `[`'s
position for the caller to warn about. -/
private def scanBracketArg (raws : Array Raw) (i : Nat) (anchor : Pos) : ArgScan :=
  let j := skipSpaces raws i
  match raws[j]? with
  | some (.sym '[' bpos) =>
    if bpos.line != anchor.line then .content
    else
      match closeBracketFrom raws (j + 1) with
      | some c => .took (c + 1)
      | none => .unclosed bpos
  | _ => .content

private theorem scanBracketArg_took_lt {raws : Array Raw} {i : Nat}
    {anchor : Pos} {n : Nat} (h : scanBracketArg raws i anchor = .took n) :
    i < n ∧ n ≤ raws.size := by
  unfold scanBracketArg at h
  dsimp only at h
  split at h
  next j bpos heq =>
    split at h
    · simp at h
    · split at h
      next c hc =>
        have h1 := skipSpaces_ge raws i
        have h2 := closeBracketFrom_ge hc
        simp only [ArgScan.took.injEq] at h
        omega
      next => simp at h
  next => simp at h

/-- An unclosed `[` stays as content; this says why it was not an argument. -/
private def warnUnclosed (ctx : Ctx) (after : String) (bpos : Pos) : EM Unit :=
  diag ctx .W0310 s!"'[' after {after} never closes; it is not an argument" (some bpos)
    (help := "add the matching ']'")

/-- The index of a command's `{...}` group past its optional argument, best
effort — the pure extent half, so a scanner that owns no diagnostics can
walk it too. A well-formed `[...]` is skipped whole. An unclosed one is
returned as data (its position, for the caller that owns W0310); its
run — the rest of the command's own line — is returned too, because W0310
calls it content: a body position renders it, and only the preamble, where
no content can live, drops it with the warning already pointing there. The
group the author wrote is then found wherever the line break falls — this
line, the next, or past a blank line — but never past another construct.
Returns the candidate index, whether it recovered from an unclosed bracket
(a recovered command with no group left is skipped with a warning by its
caller, never a fatal error), the malformed run, and the unclosed `[`'s
position. -/
private def scanOptArg (raws : Array Raw) (start : Nat) (pos : Pos) :
    Nat × Bool × Array Raw × Option Pos :=
  let j := skipSpaces raws start
  match scanBracketArg raws start pos with
  | .took k => (skipSpaces raws k, false, #[], none)
  | .content => (j, false, #[], none)
  | .unclosed bpos =>
    let e := malformedRun raws j pos (groups := false)
    let k := spanRaws raws e isSpaceOrPar
    if let some (.group _ _) := raws[k]? then
      (k, true, raws.extract j e, some bpos)
    else
      (e, true, raws.extract j e, some bpos)

private theorem malformedRun_ge (raws : Array Raw) (i : Nat) (anchor : Pos)
    (groups : Bool) : i ≤ malformedRun raws i anchor groups := by
  unfold malformedRun; exact spanRaws_ge ..

private theorem scanOptArg_ge (raws : Array Raw) (start : Nat) (pos : Pos) :
    start ≤ (scanOptArg raws start pos).1 := by
  unfold scanOptArg
  have hj := skipSpaces_ge raws start
  have he := malformedRun_ge raws (skipSpaces raws start) pos false
  have hk := spanRaws_ge raws
    (malformedRun raws (skipSpaces raws start) pos false) isSpaceOrPar
  dsimp only
  split
  next k h =>
    have h1 := scanBracketArg_took_lt h
    have h2 := skipSpaces_ge raws k
    simp; omega
  next => simp; omega
  next bpos h =>
    split <;> simp <;> omega

private def skipOptArg (ctx : Ctx) (name : String) (raws : Array Raw)
    (start : Nat) (pos : Pos) : EM ({ j : Nat // start ≤ j } × Bool × Array Raw) := do
  match h : scanOptArg raws start pos with
  | (j, recovered, junk, unclosed) =>
    if let some bpos := unclosed then
      warnUnclosed ctx s!"'\\{name}'" bpos
    return (⟨j, by have := scanOptArg_ge raws start pos; rw [h] at this; exact this⟩,
      recovered, junk)

/-- The body of an unknown environment without its arguments: leading `[...]`
runs and `{...}` groups on the `\begin` line are the environment's own
arguments (`\begin{banner}{Logo}`), not content. A group or bracket on a
later line is content — LaTeX's own argument scanning stops looking there
too. Also returns the position of an unclosed `[`, for the caller to warn
about (its run is kept as content), and how many groups went with the
wrapper, for the caller to name what W0302's "body is kept" does not cover. -/
private def dropEnvArgs (body : Array Raw) (beginPos : Pos) :
    Nat × Option Pos × Nat := Id.run do
  let mut i : Nat := 0
  let mut dropped := 0
  for _ in [0:body.size] do
    match scanBracketArg body i beginPos with
    | .took k => i := k
    | .unclosed bpos => return (i, some bpos, dropped)
    | .content =>
      let j := skipSpaces body i
      match body[j]? with
      | some (.group _ gpos) =>
        if gpos.line == beginPos.line then
          i := j + 1
          dropped := dropped + 1
        else break
      | _ => break
  return (i, none, dropped)

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

/-- The index past consecutive `[...]` option runs, each accepted by
`scanBracketArg`'s rule — opened on `anchor`'s line, closed. An option run
is how the author addressed a command, never their content, so the callers
(`skipReservedArgs`, and the unknown-command recovery) send it with the
command rather than onto the page. A run that never closes stops the scan
and its `[` position is returned: that run is malformed content, the
caller's to keep and warn about. -/
private def skipOptionRuns (raws : Array Raw) (i : Nat) (anchor : Pos) :
    Nat × Option Pos :=
  match _h : scanBracketArg raws i anchor with
  | .took k => skipOptionRuns raws k anchor
  | .unclosed bpos => (i, some bpos)
  | .content => (i, none)
termination_by raws.size + 1 - i
decreasing_by have := scanBracketArg_took_lt _h; omega

private theorem skipOptionRuns_ge (raws : Array Raw) (i : Nat) (anchor : Pos) :
    i ≤ (skipOptionRuns raws i anchor).1 := by
  fun_induction skipOptionRuns raws i anchor with
  | case1 =>
    rename_i k hk ih
    have := scanBracketArg_took_lt hk
    omega
  | case2 => simp
  | case3 => simp

/-- Skip an argument run: argument recovery after a reserved (not yet
implemented) or unknown command. A starred form's `*`, the `[...]` option
runs, and up to `maxGroups` `{...}` groups are consumed with the command
they belong to — recovery never turns a warning into an error, and a stray
`*` or second group in the preamble is exactly how one skipped command
used to become E0313. In the body `maxGroups` stays 1, so a scope group
standing after a reserved command is still content; in the preamble there
is no content, so the caller passes TeX's own argument limit of nine. The
scan stops at anything else, so the author's next construct is never
consumed. Returns the next index and, when an unclosed `[` stopped the
scan, its position. -/
private def skipReservedArgsGo (raws : Array Raw) (j : Nat) (anchor : Pos) :
    Nat → Nat × Option Pos
  | 0 => (j, none)
  | g + 1 =>
    let (k, unclosed) := skipOptionRuns raws j anchor
    match unclosed with
    | some bpos => (k, some bpos)
    | none =>
      let k2 := skipSpaces raws k
      if raws[k2]? matches some (.group _ _) then
        skipReservedArgsGo raws (k2 + 1) anchor g
      else (k, none)

private theorem skipReservedArgsGo_ge (raws : Array Raw) (anchor : Pos)
    (g : Nat) : ∀ j : Nat, j ≤ (skipReservedArgsGo raws j anchor g).1 := by
  induction g with
  | zero => intro j; simp [skipReservedArgsGo]
  | succ g ih =>
    intro j
    have h1 := skipOptionRuns_ge raws j anchor
    unfold skipReservedArgsGo
    dsimp only
    split
    · simpa using h1
    · split
      · have h2 := skipSpaces_ge raws (skipOptionRuns raws j anchor).1
        have h3 := ih (skipSpaces raws (skipOptionRuns raws j anchor).1 + 1)
        simp only [reduceIte]
        omega
      · simpa using h1

private def skipReservedArgs (raws : Array Raw) (i : Nat) (anchor : Pos)
    (maxGroups : Nat := 1) : Nat × Option Pos :=
  match raws[i]? with
  | some (.word "*" _) => skipReservedArgsGo raws (i + 1) anchor maxGroups
  | _ => skipReservedArgsGo raws i anchor maxGroups

private theorem skipReservedArgs_ge (raws : Array Raw) (i : Nat) (anchor : Pos)
    (maxGroups : Nat) : i ≤ (skipReservedArgs raws i anchor maxGroups).1 := by
  unfold skipReservedArgs
  split
  · have := skipReservedArgsGo_ge raws anchor maxGroups (i + 1); omega
  · exact skipReservedArgsGo_ge raws anchor maxGroups i

-- The termination measure for the elaboration knot: every raw weighs at
-- least one, a container outweighs its body, so consuming a token or
-- descending into one strictly lightens the remaining slice. Measure only,
-- erased at runtime — no artifact reads a weight.

mutual
-- conserves: none — a termination measure, not a content walk
private def rawWeight : Raw → Nat
  | .group body _ => 1 + rawWeightList body.toList
  | .math _ body _ => 1 + rawWeightList body.toList
  | .env _ body _ => 1 + rawWeightList body.toList
  | _ => 1
-- conserves: none — a termination measure, not a content walk
private def rawWeightList : List Raw → Nat
  | [] => 0
  | r :: rest => rawWeight r + rawWeightList rest
end

/-- The measure component the knot's spine recurses on: the weight of the
slice from `i`. -/
private def sliceWeight (raws : Array Raw) (i : Nat) : Nat :=
  rawWeightList (raws.toList.drop i)

private theorem rawWeightList_append (a b : List Raw) :
    rawWeightList (a ++ b) = rawWeightList a + rawWeightList b := by
  induction a with
  | nil => simp [rawWeightList]
  | cons x xs ih => simp [rawWeightList, ih]; omega

private theorem rawWeight_pos (r : Raw) : 1 ≤ rawWeight r := by
  cases r <;> simp [rawWeight]

private theorem rawWeightList_drop_le (l : List Raw) (i : Nat) :
    rawWeightList (l.drop i) ≤ rawWeightList l := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ n =>
      have := ih n
      simp only [List.drop_succ_cons, rawWeightList]
      have := rawWeight_pos x
      omega

private theorem rawWeightList_take_le (l : List Raw) (i : Nat) :
    rawWeightList (l.take i) ≤ rawWeightList l := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp [rawWeightList]
    | succ n =>
      have := ih n
      simp only [List.take_succ_cons, rawWeightList]
      omega

private theorem sliceWeight_here (raws : Array Raw) {i : Nat} (h : i < raws.size) :
    sliceWeight raws i = rawWeight raws[i] + sliceWeight raws (i + 1) := by
  unfold sliceWeight
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp [rawWeightList]

/-- The workhorse: any strict advance strictly lightens the slice. -/
private theorem sliceWeight_lt (raws : Array Raw) {i j : Nat}
    (hi : i < raws.size) (hij : i < j) : sliceWeight raws j < sliceWeight raws i := by
  have h1 := sliceWeight_here raws hi
  have h2 : sliceWeight raws j ≤ sliceWeight raws (i + 1) := by
    unfold sliceWeight
    have : raws.toList.drop j = (raws.toList.drop (i + 1)).drop (j - (i + 1)) := by
      rw [List.drop_drop]; congr 1; omega
    rw [this]
    exact rawWeightList_drop_le _ _
  have := rawWeight_pos raws[i]
  omega

/-- An element standing anywhere at or past `i` weighs no more than the
slice from `i`. -/
private theorem elem_weight_le {raws : Array Raw} {j : Nat} {r : Raw}
    (h : raws[j]? = some r) {i : Nat} (hij : i ≤ j) :
    rawWeight r ≤ sliceWeight raws i := by
  cases Array.getElem?_eq_some_iff.mp h with
  | intro hj hr =>
    have h1 := sliceWeight_here raws hj
    have h2 : sliceWeight raws j ≤ sliceWeight raws i := by
      unfold sliceWeight
      rw [show raws.toList.drop j = (raws.toList.drop i).drop (j - i) by
        rw [List.drop_drop]; congr 1; omega]
      exact rawWeightList_drop_le _ _
    rw [hr] at h1
    omega

/-- An extracted tail of a body weighs no more than the body. -/
private theorem extract_weight_le (body : Array Raw) (a b : Nat) :
    rawWeightList (body.extract a b).toList ≤ rawWeightList body.toList := by
  rw [Array.toList_extract]
  exact Nat.le_trans (rawWeightList_take_le _ _) (rawWeightList_drop_le _ _)

/-- The unknown-environment splice strictly lightens the slice: the kept
body is lighter than the wrapper it replaces, whatever prefix its argument
scan dropped. -/
private theorem sliceWeight_splice {raws : Array Raw} {i : Nat}
    (h : i < raws.size) {name : String} {body : Array Raw} {pos : Pos}
    (hr : raws[i] = .env name body pos) (keptFrom : Nat) :
    sliceWeight (raws.extract 0 i ++ body.extract keptFrom body.size
      ++ raws.extract (i + 1) raws.size) i < sliceWeight raws i := by
  have hlen : (raws.extract 0 i).toList.length = i := by
    simp [Array.length_toList]; omega
  have hdrop : ((raws.extract 0 i ++ body.extract keptFrom body.size
      ++ raws.extract (i + 1) raws.size)).toList.drop i
      = (body.extract keptFrom body.size).toList
        ++ (raws.extract (i + 1) raws.size).toList := by
    simp only [Array.toList_append, List.append_assoc]
    rw [List.drop_append_of_le_length (by omega)]
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
  unfold sliceWeight
  rw [hdrop, rawWeightList_append]
  have h1 := sliceWeight_here raws h
  rw [hr] at h1
  have h2 := extract_weight_le body keptFrom body.size
  have h3 : rawWeightList (raws.extract (i + 1) raws.size).toList
      ≤ rawWeightList (raws.toList.drop (i + 1)) := by
    rw [Array.toList_extract]
    exact rawWeightList_take_le _ _
  unfold sliceWeight at h1
  simp only [rawWeight] at h1
  omega

/-- The weight of every command body the walk can see: the elabBlocks
measure term that makes a user-command expansion decrease — the expanded
body leaves this sum (`visWeight_expand`), and what a body `\define` adds
to it is exactly the body the walk paid a heavier group for
(`bindCmd_visWeight`). The old `(envLimit, limit, …)` lex is unsound for
the block walk: `limit` rises across a define on the spine; this sum
replaces it. -/
private def visWeightGo (user : Array UserCmd) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    (if h : k < user.size then rawWeightList user[k].body.toList else 0)
      + visWeightGo user k

private theorem visWeightGo_mono (user : Array UserCmd) {a b : Nat}
    (h : a ≤ b) : visWeightGo user a ≤ visWeightGo user b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · subst heq; exact Nat.le_refl _
    · have h2 := ih (by omega)
      simp only [visWeightGo]
      omega

private theorem visWeightGo_congr {u v : Array UserCmd} {n : Nat}
    (h : ∀ m, m < n → u[m]? = v[m]?) : visWeightGo u n = visWeightGo v n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have h1 := h m (by omega)
    have h2 := ih fun k hk => h k (by omega)
    simp only [visWeightGo]
    split <;> split
    · rename_i hu hv
      have : u[m] = v[m] := by
        have := Array.getElem?_eq_getElem hu
        have := Array.getElem?_eq_getElem hv
        simp_all
      rw [this, h2]
    · rename_i hu hv
      rw [Array.getElem?_eq_getElem hu, Array.getElem?_eq_none (by omega)] at h1
      simp at h1
    · rename_i hu hv
      rw [Array.getElem?_eq_getElem hv, Array.getElem?_eq_none (by omega)] at h1
      simp at h1
    · rw [h2]

private theorem lookupUserGo_found {user : Array UserCmd} {name : String}
    {n k : Nat} {cmd : UserCmd}
    (h : lookupUserGo user name n = some (k, cmd)) : user[k]? = some cmd := by
  fun_induction lookupUserGo user name n with
  | case1 => simp at h
  | case2 m hm heq =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, Array.getElem?_eq_getElem hm, h.2]
  | case3 m hm heq ih => exact ih h
  | case4 m hm ih => exact ih h

/-- Expanding a visible command moves weight out of the visible sum: the
body recursed into, plus everything still visible to the callee, never
exceeds what the caller's sum already carried. -/
private theorem visWeight_expand {ctx : Ctx} {name : String} {k : Nat}
    {cmd : UserCmd} (h : lookupUser ctx name = some (k, cmd)) :
    rawWeightList cmd.body.toList + visWeightGo ctx.user k
      ≤ visWeightGo ctx.user ctx.limit := by
  have hlt := lookupUser_lt h
  have hfound := lookupUserGo_found h
  obtain ⟨hk, hbody⟩ := Array.getElem?_eq_some_iff.mp hfound
  have hstep : visWeightGo ctx.user (k + 1)
      = rawWeightList cmd.body.toList + visWeightGo ctx.user k := by
    simp only [visWeightGo, hk, dite_true, hbody]
  have hmono := visWeightGo_mono ctx.user (show k + 1 ≤ ctx.limit by omega)
  omega

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

/-- Record one `\label` binding. The first declaration of a key wins,
LaTeX's behaviour; a second is W0350 where it stands and binds nothing. -/
private def recordLabel (ctx : Ctx) (key : String) (target : Option String)
    (pos : Pos) : EM Unit := do
  let st ← get
  if st.labels.any (·.1 == key) then
    diag ctx .W0350 s!"'{key}' is already a \\label'ed key; the first wins" (some pos)
      (help := s!"one \\label\{{key}} per key: give this one its own name")
  else
    modify fun st => { st with labels := st.labels.push (key, target) }

/-- Strip a display-math body's metadata before the math parser sees it:
top-level `\label{...}` keys (returned for binding to the display's
number) and `\nonumber`/`\notag` (amsldoc §3: a numbered form opts out).
Neither is mathematics; left in place they would push the whole formula
into the W0012 source-text degradation — with the label spelled inside
the rendered text. -/
private def stripMathMeta (ctx : Ctx) (body : Array Raw) :
    EM (Array Raw × Array String × Bool) := do
  let mut out : Array Raw := #[]
  let mut keys : Array String := #[]
  let mut nonum := false
  let mut i : Nat := 0
  repeat
    if h : i < body.size then
      match body[i] with
      | .ctrl "label" pos =>
        let j := skipSpaces body (i + 1)
        match body[j]? with
        | some (.group keyRaw _) =>
          keys := keys.push (argText ctx keyRaw)
          i := j + 1
        | _ =>
          diag ctx .E0304 "'\\label' needs a {key} group" pos
          i := i + 1
      | .ctrl "nonumber" _ =>
        nonum := true
        i := i + 1
      | .ctrl "notag" _ =>
        nonum := true
        i := i + 1
      | r =>
        out := out.push r
        i := i + 1
    else break
  return (out, keys, nonum)

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
  let mut i : Nat := 0
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

-- Small pure helpers whose progress the knot's termination proof reads.

private theorem getElem?_lt {raws : Array Raw} {j : Nat} {r : Raw}
    (h : raws[j]? = some r) : j < raws.size := by
  cases Array.getElem?_eq_some_iff.mp h with
  | intro hj _ => exact hj

private theorem sliceWeight_le (raws : Array Raw) {i j : Nat} (hij : i ≤ j) :
    sliceWeight raws j ≤ sliceWeight raws i := by
  unfold sliceWeight
  rw [show raws.toList.drop j = (raws.toList.drop i).drop (j - i) by
    rw [List.drop_drop]; congr 1; omega]
  exact rawWeightList_drop_le _ _

private theorem extract_slice_le (raws : Array Raw) (a b : Nat) :
    rawWeightList (raws.extract a b).toList ≤ sliceWeight raws a := by
  rw [Array.toList_extract]
  exact rawWeightList_take_le _ _

private theorem extract_lt_slice {raws : Array Raw} {i a : Nat} (b : Nat)
    (h : i < raws.size) (ha : i < a) :
    rawWeightList (raws.extract a b).toList < sliceWeight raws i :=
  Nat.lt_of_le_of_lt (extract_slice_le raws a b) (sliceWeight_lt raws h ha)

private theorem body_lt_slice' {raws : Array Raw} {i : Nat} (h : i < raws.size)
    {body : Array Raw} (hb : rawWeightList body.toList < rawWeight raws[i]) :
    rawWeightList body.toList < sliceWeight raws i := by
  have h1 := sliceWeight_here raws h
  omega

private theorem body_lt_slice {raws : Array Raw} {j : Nat} {r : Raw}
    (hj : raws[j]? = some r) {body : Array Raw}
    (hb : rawWeightList body.toList < rawWeight r) {i : Nat} (hij : i ≤ j) :
    rawWeightList body.toList < sliceWeight raws i :=
  Nat.lt_of_lt_of_le hb (elem_weight_le hj hij)

/-- The index past a starred form's `*`: a star belongs to the command,
not to the text. -/
private def skipStar (raws : Array Raw) (j : Nat) : Nat :=
  match raws[j]? with
  | some (.word "*" _) => skipSpaces raws (j + 1)
  | _ => j

private theorem skipStar_ge (raws : Array Raw) (j : Nat) : j ≤ skipStar raws j := by
  unfold skipStar
  split
  · have := skipSpaces_ge raws (j + 1); omega
  · omega

/-- The index past a consumed `[short]` title and the spaces after it —
`.took`'s continuation, one pure function so its progress is a fact. -/
private def skipShortTitle (raws : Array Raw) (j : Nat) (pos : Pos) : Nat :=
  match scanBracketArg raws j pos with
  | .took k => skipSpaces raws k
  | _ => j

private theorem skipShortTitle_ge (raws : Array Raw) (j : Nat) (pos : Pos) :
    j ≤ skipShortTitle raws j pos := by
  unfold skipShortTitle
  split
  next k hk =>
    have h1 := scanBracketArg_took_lt hk
    have h2 := skipSpaces_ge raws k
    omega
  next => omega

/-- The content of one adjacent `[...]` run — `\includegraphics` and
`\faIcon`'s option scan. An unclosed run consumes to the end, as the
collectors always have. -/
private def bracketRunSrc (raws : Array Raw) (j : Nat) : Option (Array Raw) :=
  match raws[j]? with
  | some (.sym '[' _) =>
    match closeBracketFrom raws (j + 1) with
    | some c => some (raws.extract (j + 1) c)
    | none => some (raws.extract (j + 1) raws.size)
  | _ => none

/-- The index past that run and the spaces after it, one pure function so
its progress is a fact. -/
private def skipBracketRun (raws : Array Raw) (j : Nat) : Nat :=
  match raws[j]? with
  | some (.sym '[' _) =>
    match closeBracketFrom raws (j + 1) with
    | some c => skipSpaces raws (c + 1)
    | none => skipSpaces raws raws.size
  | _ => j

private theorem skipBracketRun_ge (raws : Array Raw) (j : Nat) :
    j ≤ skipBracketRun raws j := by
  unfold skipBracketRun
  split
  next bpos hb =>
    split
    next c hc =>
      have h1 := closeBracketFrom_ge hc
      have h2 := skipSpaces_ge raws (c + 1)
      omega
    next =>
      have h1 := getElem?_lt hb
      have h2 := skipSpaces_ge raws raws.size
      omega
  next => omega

/-- Applied to a level's own text only; nested bodies were processed by
their own call, with their own literal-text setting. -/
private def mapSmartText (x : Inline) : Inline :=
  if let .text t := x then .text (smartPunct t) else x

/-- `\\[len]`'s declared extra space, read from the bracket's source. -/
private def readBreakLen (ctx : Ctx) (src : String) (pos : Pos) : EM SymGlue := do
  match Decl.parseValue src ctx.tokens.entries with
  | some (.glue g) => pure g
  | some (.dim d) => pure { width := Dim.Length.ofSp d }
  | _ =>
    diag ctx .E0331 s!"cannot read a length from '{src}'" pos
      (help := "lengths look like 10pt or 1.5ex, or name a token")
    pure {}

/-- `\\includegraphics`' option run: the modelled keys — width, height,
scale, keepaspectratio, alt — and a name for everything else. -/
private def readImageOpts (ctx : Ctx) (optSrc : Option (Array Raw))
    (pos : Pos) : EM (Image.SizeSpec × String) := do
  let mut spec : Image.SizeSpec := {}
  let mut altText := ""
  if let some src := optSrc then
    for e in Decl.splitEntries (rawSrc src) do
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
  return (spec, altText)

/-- `\\faIcon`'s option run: only `label = ...` is modelled, overriding the
icon's default text alternative. -/
private def readIconLabel (ctx : Ctx) (labelSrc : Option (Array Raw))
    (pos : Pos) : EM (Option String) := do
  let mut label : Option String := none
  if let some optSrc := labelSrc then
    for e in Decl.splitEntries (rawSrc optSrc) do
      match Decl.splitEntry e with
      | some ("label", v) => label := some v.trimAscii.toString
      | _ =>
        warnOnce ctx ("faopt:" ++ e) .W0110
          s!"'\\faIcon' option '{e.trimAscii.toString}' is not modelled; ignored" pos
          (help := "the face that renders an icon is whichever declared or installed face covers its scalar; 'label = ...' overrides the icon's text alternative")
  return label

/-- Discharges the knot's termination goals: navigate the lexicographic
tuple to the strictly-decreasing component; the strict fact is a `have`
standing beside each recursive call. -/
macro "knot_dec" : tactic =>
  `(tactic| (
    simp_wf
    <;> first
      | (apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left
         assumption)
      | (apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.right
         first | assumption | omega)
      | (apply Prod.Lex.right; apply Prod.Lex.left; assumption)
      | (apply Prod.Lex.left; assumption)
      | (apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left
         simp only [Array.toList_extract, Array.append_assoc] at *
         assumption)))

/-- The numbered heading levels, by counter name: `\section` is 1. -/
private def sectionLevel : String → Option Nat
  | "section" => some 1
  | "subsection" => some 2
  | "subsubsection" => some 3
  | _ => none

/-- `\thesection`/`\thesubsection`/`\thesubsubsection` to its level. -/
private def theCounterLevel? (n : String) : Option Nat :=
  if n.startsWith "the" then sectionLevel (n.drop 3).toString else none

private def secStyleOf? : String → Option SecNumStyle
  | "arabic" => some .arabic
  | "alph" => some .alph
  | "Alph" => some .uAlph
  | "roman" => some .roman
  | "Roman" => some .uRoman
  | _ => none

private def secStyleRender (style : SecNumStyle) (n : Nat) : String :=
  match style with
  | .arabic => ListMark.arabicN n
  | .alph => ListMark.alphN n
  | .uAlph => ListMark.AlphN n
  | .roman => ListMark.romanN n
  | .uRoman => (ListMark.romanN n).toUpper

private def counterAt (nums : Nat × Nat × Nat) (level : Nat) : Nat :=
  match level with
  | 1 => nums.1
  | 2 => nums.2.1
  | _ => nums.2.2

/-- The class default number (classes.dtx §Sectioning): `\thesection` is
`\arabic{section}` (`\Alph` after `\appendix`), each deeper level prefixes
its parent. -/
private def defaultSecNum (nums : Nat × Nat × Nat) (inApp : Bool)
    (level : Nat) : String :=
  let (n1, n2, n3) := nums
  let base := if inApp then ListMark.AlphN n1 else ListMark.arabicN n1
  match level with
  | 1 => base
  | 2 => s!"{base}.{n2}"
  | _ => s!"{base}.{n2}.{n3}"

mutual
/-- Render one level's heading number: the declared format when one
stands (`ESt.secFmts`, last declaration wins), the class default
otherwise. `fuel` bounds `\the<counter>` references between formats —
a self-referential chain cannot outrun it — and an exhausted budget
falls back to the counter's bare arabic value. -/
private def renderSecLevel (fmts : Array (Nat × Array SecPart))
    (nums : Nat × Nat × Nat) (inApp : Bool) (fuel level : Nat) : String :=
  match fuel with
  | 0 => ListMark.arabicN (counterAt nums level)
  | fuel + 1 =>
    match fmts.findRev? (·.1 == level) with
    | some (_, parts) => renderSecParts fmts nums inApp fuel parts.toList ""
    | none => defaultSecNum nums inApp level
termination_by (fuel, 0)

private def renderSecParts (fmts : Array (Nat × Array SecPart))
    (nums : Nat × Nat × Nat) (inApp : Bool) (fuel : Nat) :
    List SecPart → String → String
  | [], acc => acc
  | p :: rest, acc =>
    let piece := match p with
      | .lit s => s
      | .num style lvl => secStyleRender style (counterAt nums lvl)
      | .the lvl => renderSecLevel fmts nums inApp fuel lvl
    renderSecParts fmts nums inApp fuel rest (acc ++ piece)
termination_by parts _ => (fuel, parts.length + 1)
end

/-- The `\the<counter>` render budget: the three section levels can chain
at most through each other once each. -/
private def secFmtFuel : Nat := 3

/-- Read a definition body as a heading-number format: literal words and
spaces, a numeral command over a section counter (`\arabic{subsection}`),
or another level's format (`\thesection`). Any other token means the
definition is not a format and stays an ordinary macro (`none`). -/
private def secFmtOfBody (body : Array Raw) : Option (Array SecPart) := Id.run do
  let mut parts : Array SecPart := #[]
  let mut i : Nat := 0
  for _ in [0:body.size + 1] do
    match body[i]? with
    | none => break
    | some (.word s _) =>
      parts := parts.push (.lit s)
      i := i + 1
    | some .space =>
      parts := parts.push (.lit " ")
      i := i + 1
    | some (.ctrl n _) =>
      if let some lvl := theCounterLevel? n then
        parts := parts.push (.the lvl)
        i := i + 1
      else if let some style := secStyleOf? n then
        match body[i + 1]? with
        | some (.group g _) =>
          match g.toList.filter (fun r => match r with | .space => false | _ => true) with
          | [.word cn _] =>
            match sectionLevel cn with
            | some lvl =>
              parts := parts.push (.num style lvl)
              i := i + 2
            | none => return none
          | _ => return none
        | _ => return none
      else return none
    | some _ => return none
  return some parts

/-- A definition that is a heading-number format: parameterless, named
`\the<section counter>`, its body readable as a format. classes.dtx
§Sectioning: `\the<counter>` is the counter's printed format, so
`\renewcommand{\thesubsection}{FAQ \arabic{subsection}.}` — which the
definer rewrite spells `\define \thesubsection() {...}` — restyles the
heading numbers; binding it as a macro instead left every such document
with dead `\arabic` text and E0312 where the renew stood inline. -/
private def secFmtDefine? (cmd : UserCmd) : Option (Nat × Array SecPart) :=
  if !cmd.params.isEmpty then none
  else (theCounterLevel? cmd.name).bind fun lvl =>
    (secFmtOfBody cmd.body).map ((lvl, ·))

/-- Declare one level's heading-number format from where it stands: flow
scope, the `\logo`/body-`\palette` model, never a brace revert. -/
private def applySecFmt (lvl : Nat) (parts : Array SecPart) : EM Unit :=
  modify fun st =>
    { st with secFmts := (st.secFmts.filter (·.1 != lvl)).push (lvl, parts) }

/-- The counter-command names (ltcounts.dtx), one gate for the
block-shape judgement and the block walk's arm. -/
private def counterCtrl (n : String) : Bool :=
  n == "refstepcounter" || n == "stepcounter"
    || n == "addtocounter" || n == "setcounter"

/-- LaTeX's counter commands over the section counters (ltcounts.dtx):
`\stepcounter` steps and zeroes the levels below, `\refstepcounter` also
makes the counter the current `\ref` target (`\@currentlabel` is
`\p@counter\thecounter`, so the format in force renders it), and
`\addtocounter`/`\setcounter` change the value alone. Values are flow
Nats; a negative result clamps to zero. -/
private def applyCounter (name : String) (lvl : Nat) (n : Int) : EM Unit := do
  let st ← get
  let (s1, s2, s3) := st.secNums
  let cur : Int := Int.ofNat (counterAt st.secNums lvl)
  let v : Int := match name with
    | "setcounter" => n
    | "addtocounter" => cur + n
    | _ => cur + 1
  let v := v.toNat
  let step := name == "stepcounter" || name == "refstepcounter"
  let nums := match lvl with
    | 1 => if step then (v, 0, 0) else (v, s2, s3)
    | 2 => if step then (s1, v, 0) else (s1, v, s3)
    | _ => (s1, s2, v)
  modify fun st => { st with secNums := nums }
  if name == "refstepcounter" then
    let num := renderSecLevel st.secFmts nums st.inAppendix secFmtFuel lvl
    modify fun st => { st with refTarget := some num }

/-- One counter command with its arguments starting at `i` (just past
the control word): scan, apply over the section counters, name any
other counter (W0104) with its arguments consumed — configuration,
never content. Out of the block knot so the fixpoint never unfolds
it; the returned index carries the progress fact the knot's measure
reads. -/
private def counterArm (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (n : String) (pos : Pos) : EM { j : Nat // i ≤ j } := do
  let j := skipSpaces raws i
  have hjge : i ≤ j := skipSpaces_ge raws i
  match raws[j]? with
  | some (.group ctrRaw _) =>
    let ctr := (rawSrc ctrRaw).trimAscii.toString
    let ⟨(amt, j2), hj2⟩ : { t : Option Int × Nat // j + 1 ≤ t.2 } ←
      if n == "addtocounter" || n == "setcounter" then
        let ja := skipSpaces raws (j + 1)
        have hja : j + 1 ≤ ja := skipSpaces_ge raws (j + 1)
        match raws[ja]? with
        | some (.group nRaw _) =>
          pure ⟨((rawSrc nRaw).trimAscii.toString.toInt?, ja + 1), by omega⟩
        | _ => pure ⟨(none, j + 1), Nat.le_refl _⟩
      else
        pure ⟨(some 1, j + 1), Nat.le_refl _⟩
    match sectionLevel ctr, amt with
    | some lvl, some v => applyCounter n lvl v
    | some _, none =>
      diag ctx .E0304 s!"'\\{n}' needs an integer \{value} group" pos
    | none, _ =>
      warnOnce ctx ("ctrl:" ++ n ++ ":" ++ ctr) .W0104
        s!"counter '{ctr}' is not modelled; '\\{n}' changes nothing" pos
    return ⟨j2, by omega⟩
  | _ =>
    diag ctx .E0304 s!"'\\{n}' needs a \{counter} group" pos
    return ⟨i, Nat.le_refl _⟩

-- The well-founded translation whnf-reduces through the knot's body when it
-- assembles the fixpoint and its equations; the string machinery in the
-- arms is data to that process, never proof material, and unfolding it is
-- what blew the elaboration budget (measured: String.Slice.skipPrefixWhile
-- alone at 184k reductions). Sealed for the knot, unsealed right after.
seal String.trimAscii Parse.rawSrc Parse.rawSrcOne Decl.splitEntries
seal Decl.splitEntry Decl.parseValue Decl.parseDecimal smartPunct
seal String.Slice.trimAscii String.Slice.trimAsciiStart String.Slice.trimAsciiEnd
seal String.Slice.dropWhile String.Slice.dropEndWhile String.Slice.skipPrefixWhile

seal secFmtOfBody applySecFmt applyCounter counterCtrl counterArm
seal theCounterLevel? sectionLevel String.toInt? String.toNat?

mutual

/-- One parameter binding at a time — `takeArgs`' recursion spelled so the
measure can read it: each parameter either consumes tokens (the slice from
the scan position lightens strictly) or binds nothing (the parameter index
advances). The final index returns with its progress fact, which is what
lets a caller's own termination argument continue from it. -/
def takeArgsFrom (ctx : Ctx) (params : Array Param) (k : Nat) (name : String)
    (raws : Array Raw) (start : Nat) (pos : Pos)
    (bindings : Array (String × Option (Array Inline))) :
    EM (Array (String × Option (Array Inline)) × { j : Nat // start ≤ j }) := do
  if hk : k < params.size then
    let p := params[k]
    if p.optional then
      let j := skipSpaces raws start
      have hjge := skipSpaces_ge raws start
      match hj : raws[j]? with
      | some (.sym '[' _) =>
        have hjlt := getElem?_lt hj
        match hc : closeBracketFrom raws (j + 1) with
        | some c =>
          have hcge := closeBracketFrom_ge hc
          have hw : rawWeightList (raws.extract (j + 1) c).toList
              < sliceWeight raws start :=
            extract_lt_slice c (by omega) (by omega)
          let v ← elabInlines { ctx with argBody := true } (raws.extract (j + 1) c)
          if p.type == .text && !allText v then
            diag ctx .E0305 s!"parameter '{p.name}' of '\\{name}' expects text" pos
          have hadv : sliceWeight raws (c + 1) < sliceWeight raws start :=
            sliceWeight_lt raws (by omega) (by omega)
          let (bs, ⟨j2, hj2⟩) ← takeArgsFrom ctx params (k + 1) name raws (c + 1)
            pos (bindings.push (p.name, some v))
          return (bs, ⟨j2, by omega⟩)
        | none =>
          diag ctx .E0316 s!"unclosed optional argument for '\\{name}'" pos
          have hw : rawWeightList (raws.extract (j + 1) raws.size).toList
              < sliceWeight raws start :=
            extract_lt_slice raws.size (by omega) (by omega)
          let v ← elabInlines { ctx with argBody := true } (raws.extract (j + 1) raws.size)
          if p.type == .text && !allText v then
            diag ctx .E0305 s!"parameter '{p.name}' of '\\{name}' expects text" pos
          have hadv : sliceWeight raws raws.size < sliceWeight raws start :=
            sliceWeight_lt raws (by omega) (by omega)
          let (bs, ⟨j2, hj2⟩) ← takeArgsFrom ctx params (k + 1) name raws raws.size
            pos (bindings.push (p.name, some v))
          return (bs, ⟨j2, by omega⟩)
      | _ =>
        takeArgsFrom ctx params (k + 1) name raws start pos
          (bindings.push (p.name, none))
    else
      let j := skipSpaces raws start
      have hjge := skipSpaces_ge raws start
      match hj : raws[j]? with
      | some (.group body _) =>
        have hjlt := getElem?_lt hj
        have hw : rawWeightList body.toList < sliceWeight raws start :=
          body_lt_slice hj (by simp only [rawWeight]; omega) hjge
        let v ← elabInlines { ctx with argBody := true } body
        if p.type == .text && !allText v then
          diag ctx .E0305 s!"parameter '{p.name}' of '\\{name}' expects text" pos
        have hadv : sliceWeight raws (j + 1) < sliceWeight raws start :=
          sliceWeight_lt raws (by omega) (by omega)
        let (bs, ⟨j2, hj2⟩) ← takeArgsFrom ctx params (k + 1) name raws (j + 1)
          pos (bindings.push (p.name, some v))
        return (bs, ⟨j2, by omega⟩)
      | some (.word s _) =>
        have hjlt := getElem?_lt hj
        have hadv : sliceWeight raws (j + 1) < sliceWeight raws start :=
          sliceWeight_lt raws (by omega) (by omega)
        let (bs, ⟨j2, hj2⟩) ← takeArgsFrom ctx params (k + 1) name raws (j + 1)
          pos (bindings.push (p.name, some #[.text s]))
        return (bs, ⟨j2, by omega⟩)
      | _ =>
        diag ctx .E0304 s!"missing argument '{p.name}' for '\\{name}'" pos
        takeArgsFrom ctx params (k + 1) name raws start pos
          (bindings.push (p.name, some #[]))
  else
    return (bindings, ⟨start, Nat.le_refl start⟩)
termination_by (ctx.envLimit, ctx.limit, sliceWeight raws start, 5 + (params.size - k))
decreasing_by all_goals knot_dec

/-- An unknown command's argument groups: up to nine `{...}` groups (TeX's
own argument limit) are kept as content, a space standing in where the
consumed separators were. Returns the accumulator and pending text, the
index past the run with its progress fact, how many groups were kept, and
whether whitespace followed the last one. -/
def elabUnknownArgs (ctx : Ctx) (raws : Array Raw) (j : Nat) (count : Nat)
    (acc : Array Inline) (sb : String) (spaceAfter : Bool) :
    EM (Array Inline × String × { j' : Nat // j ≤ j' } × Nat × Bool) := do
  if 9 ≤ count then
    return (acc, sb, ⟨j, Nat.le_refl j⟩, count, spaceAfter)
  else
    match hj : raws[j]? with
    | some (.group body _) =>
      have hjlt := getElem?_lt hj
      let acc := flushText acc sb
      -- Whatever separated the arguments visually is gone with the
      -- command, so a space stands in; without one, `{a}{b}` runs
      -- together as `ab`.
      let acc := flushText acc (if count > 0 then " " else "")
      have hw : rawWeightList body.toList < sliceWeight raws j :=
        body_lt_slice hj (by simp only [rawWeight]; omega) (Nat.le_refl j)
      let inner ← elabInlines ctx body
      let j2 := skipSpaces raws (j + 1)
      have hj2ge := skipSpaces_ge raws (j + 1)
      have hadv : sliceWeight raws j2 < sliceWeight raws j :=
        sliceWeight_lt raws hjlt (by omega)
      let (acc', sb', ⟨j', hj'⟩, kept, sp) ←
        elabUnknownArgs ctx raws j2 (count + 1) (acc ++ inner) "" (j2 != j + 1)
      return (acc', sb', ⟨j', by omega⟩, kept, sp)
    | _ => return (acc, sb, ⟨j, Nat.le_refl j⟩, count, spaceAfter)
termination_by (ctx.envLimit, ctx.limit, sliceWeight raws j, 0)
decreasing_by all_goals knot_dec

/-- Elaborate raw items as inline content. -/
def elabInlines (ctx : Ctx) (raws : Array Raw) : EM (Array Inline) := do
  let out ← elabInlinesFrom ctx raws 0 #[] ""
  return if ctx.literalText then out else out.map mapSmartText
termination_by (ctx.envLimit, ctx.limit, rawWeightList raws.toList, 4)
decreasing_by all_goals knot_dec

/-- The inline elaboration spine: one raw at `i` per step, the text
accumulator and pending string threading through as arguments. The measure
is lexicographic — user environments, then user commands, then the weight
of the slice from `i` — so every step either consumes tokens, descends
into a strictly lighter body, or expands under a strictly smaller
visibility limit. -/
def elabInlinesFrom (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (acc : Array Inline) (sb : String) : EM (Array Inline) := do
  if h : i < raws.size then
    have hadv1 : sliceWeight raws (i + 1) < sliceWeight raws i :=
      sliceWeight_lt raws h (Nat.lt_succ_self i)
    match hr : raws[i] with
    | .word s _ =>
      elabInlinesFrom ctx raws (i + 1) acc (sb ++ s)
    | .space =>
      -- Whitespace is one separator however many tokens a splice put side
      -- by side (a run was a single token at the lexer), and a paragraph
      -- never opens with one: a leading space glue would indent the line.
      elabInlinesFrom ctx raws (i + 1) acc
        (if needsSep acc sb then sb.push ' ' else sb)
    | .par _ =>
      elabInlinesFrom ctx raws (i + 1) acc
        (if needsSep acc sb then sb.push ' ' else sb)
    | .sym '[' _ =>
      elabInlinesFrom ctx raws (i + 1) acc (sb.push '[')
    | .sym ']' _ =>
      elabInlinesFrom ctx raws (i + 1) acc (sb.push ']')
    | .sym '~' _ =>
      -- Every LaTeX author means a non-breaking space by `~`, and reserving
      -- it buys nothing: there is no catcode machinery here to reserve it for.
      elabInlinesFrom ctx raws (i + 1) acc (sb.push '\u00a0')
    | .sym c pos =>
      if ctx.noteBody || ctx.argBody then
        -- A note is absorbed, as beamer absorbs it, and an argument is
        -- the caller's token list: in both, a reserved character is
        -- literal text — an argument's may still be a key on arrival.
        elabInlinesFrom ctx raws (i + 1) acc (sb.push c)
      else
        diag ctx .E0311 s!"reserved character '{c}'" pos (help := s!"escape it as '\\{c}'")
        elabInlinesFrom ctx raws (i + 1) acc sb
    | .math d body mpos =>
      let acc := flushText acc sb
      let x ← elabMathInline ctx d body mpos
      elabInlinesFrom ctx raws (i + 1) (acc.push x) ""
    | .group body _ =>
      have hw : rawWeightList body.toList < sliceWeight raws i :=
        body_lt_slice' h (by rw [hr]; simp only [rawWeight]; omega)
      let acc := flushText acc sb
      let inner ← elabInlines ctx body
      elabInlinesFrom ctx raws (i + 1) (acc ++ inner) ""
    | .env name body pos =>
      have hw : rawWeightList body.toList < sliceWeight raws i :=
        body_lt_slice' h (by rw [hr]; simp only [rawWeight]; omega)
      if let some f := Parse.inputEnvFile? name then
        let acc := flushText acc sb
        let inner ← elabInlines { ctx with file := f } body
        elabInlinesFrom ctx raws (i + 1) (acc ++ inner) ""
      else if let some numbered := displayMathEnvs.lookup name then
        let acc := flushText acc sb
        -- A display in an inline position (a caption, an item label) has
        -- no block to hang a number on: it sets unnumbered, named.
        let (cleaned, keys, _) ← stripMathMeta ctx body
        let mut acc := acc
        for key in keys do
          recordLabel ctx key (← get).refTarget pos
          acc := acc.push (.label key)
        if numbered then
          warnOnce ctx "math:eqnum" .W0015
            s!"equation numbers are not rendered here; '\{{name}}' sets unnumbered" pos
            (help := s!"'\{{name}}*' spells the unnumbered form, which renders the same")
        let x ← elabMathInline ctx true cleaned pos
        elabInlinesFrom ctx raws (i + 1) (acc.push x) ""
      else if let some (kind, numbered) := alignEnvs.lookup name then
        let acc := flushText acc sb
        let (cleaned, keys, _) ← stripMathMeta ctx body
        let mut acc := acc
        for key in keys do
          recordLabel ctx key none pos
          acc := acc.push (.label key)
        let x ← elabMathEnv ctx name kind numbered cleaned pos
        elabInlinesFrom ctx raws (i + 1) (acc.push x) ""
      else
        match he : lookupUserEnv ctx name with
        | some (k, env) =>
          -- A defined wrapper: its parameters bind from the groups after
          -- `\begin{name}`, its halves elaborate around the content. The
          -- halves see the commands and environments defined before the
          -- wrapper (never itself), the content sees the caller's.
          have hklt : k < ctx.envLimit := lookupUserEnv_lt he
          have hb0 : sliceWeight body 0 < sliceWeight raws i := by
            have h0 : sliceWeight body 0 = rawWeightList body.toList := by
              simp [sliceWeight]
            omega
          let acc := flushText acc sb
          let (bindings, ⟨j, hj⟩) ← takeArgsFrom ctx env.params 0 name body 0 pos #[]
          let envCtx : Ctx := { ctx with
            limit := env.cmdLimit, envLimit := k, args := bindings }
          have hw2 : rawWeightList (body.extract j body.size).toList
              < sliceWeight raws i := by
            have h1 := extract_slice_le body j body.size
            have h2 := sliceWeight_le body (Nat.zero_le j)
            have h0 : sliceWeight body 0 = rawWeightList body.toList := by
              simp [sliceWeight]
            omega
          let a1 ← elabInlines envCtx env.beginBody
          let a2 ← elabInlines ctx (body.extract j body.size)
          let a3 ← elabInlines envCtx env.endBody
          elabInlinesFrom ctx raws (i + 1) (acc ++ a1 ++ a2 ++ a3) ""
        | none =>
        if reservedEnv.contains name then
          warnOnce ctx ("env:" ++ name) .W0307
            s!"'\{{name}}' is not implemented yet; its content is not rendered" pos
          elabInlinesFrom ctx raws (i + 1) acc sb
        else
          warnOnce ctx ("env:" ++ name) .W0302 s!"unknown environment '\{{name}}'; its body is kept" pos
            (help := "\\defineenv{name}(...) {begin} {end} declares one")
          -- The arguments on the `\begin` line go with the wrapper here
          -- too: an inline unknown environment obeys the same scanner as a
          -- block one. The body splices into this very scan, so its edge
          -- spaces are ordinary separators — collapsed against the
          -- neighbours by the whitespace arm, never dropped (gluing
          -- `before` to `inner`) and never doubled.
          let (keptFrom, unclosed, dropped) := dropEnvArgs body pos
          if let some bpos := unclosed then
            warnUnclosed ctx s!"'\\begin\{{name}}'" bpos
          warnDroppedArgs ctx name dropped pos
          have hspl : sliceWeight (raws.extract 0 i ++ body.extract keptFrom body.size
              ++ raws.extract (i + 1) raws.size) i < sliceWeight raws i :=
            sliceWeight_splice h hr keptFrom
          elabInlinesFrom ctx (raws.extract 0 i ++ body.extract keptFrom body.size
            ++ raws.extract (i + 1) raws.size) i acc sb
    | .verb s _ =>
      -- Verbatim inside inline content: kept as mono text, spaces held as
      -- no-break spaces, lines separated by forced breaks.
      let acc := flushText acc sb
      elabInlinesFrom ctx raws (i + 1)
        (acc.push (.styled .mono (Ir.verbatimInlines s))) ""
    | .ctrl name pos =>
      -- The document's own names come first: a parameter, then a defined
      -- command. Built-ins the document cannot redefine are exactly
      -- `builtinNames`, refused with W0303 at the definition; every other
      -- built-in yields to a definition, silently, as in LaTeX. Order here
      -- is the whole mechanism — a built-in tested earlier would shadow
      -- the definition without a word.
      if let some (_, binding) := ctx.args.find? (·.1 == name) then
        let acc := flushText acc sb
        match binding with
        | some inlines =>
          let acc := acc ++ inlines
          elabInlinesFrom ctx raws (i + 1) acc ""
        | none =>
          elabInlinesFrom ctx raws (i + 1) acc ""
      else
        match hu : lookupUser ctx name with
        | some (k, cmd) =>
          have hklt : k < ctx.limit := lookupUser_lt hu
          have hto : sliceWeight raws (i + 1) < sliceWeight raws i := hadv1
          let acc := flushText acc sb
          let (bindings, ⟨j, hj⟩) ← takeArgsFrom ctx cmd.params 0 name raws (i + 1) pos #[]
          let callCtx : Ctx := { ctx with limit := k, args := bindings }
          let expanded ← elabInlines callCtx cmd.body
          -- A parameterized command is a classifier of its argument — a
          -- semantic role — and its name survives into the artifact as an
          -- addressable annotation (Inline.role, the class hook). A 0-ary
          -- command is a spelling and splices transparently: arity reads
          -- the definition, not the use, so one name gets one treatment
          -- document-wide, with no new syntax and no body inspection.
          let acc := if cmd.params.isEmpty then acc ++ expanded
            else acc.push (.role cmd.name expanded)
          have hadv : sliceWeight raws j < sliceWeight raws i :=
            Nat.lt_of_le_of_lt (sliceWeight_le raws hj) hadv1
          elabInlinesFrom ctx raws j acc ""
        | none =>
        if name == "hfill" then
          let acc := flushText acc sb
          elabInlinesFrom ctx raws (i + 1) (acc.push .fill) ""
        else if name == "ensuremath" then
          -- `\ensuremath` enters math from text (amsldoc: the argument is
          -- typeset in math mode wherever the command lands); inside math
          -- the parser treats it as transparent.
          let j := skipSpaces raws (i + 1)
          have hjge := skipSpaces_ge raws (i + 1)
          match hj : raws[j]? with
          | some (.group body _) =>
            have hjlt := getElem?_lt hj
            let acc := flushText acc sb
            let x ← elabMathInline ctx false body pos
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1) (acc.push x) ""
          | _ =>
            diag ctx .E0304 "missing argument 'body' for '\\ensuremath'" pos
            elabInlinesFrom ctx raws (i + 1) acc sb
        else if name == "\\" || name == "par" then
          -- `\\[len]` adds space after the break. The bracket must be
          -- adjacent: LaTeX skips spaces here and so swallows the `[` of a
          -- line that legitimately starts with one. Whitespace after a
          -- break is the source's line ending, not content; keeping it
          -- would open the next line with a stray space.
          if name == "\\" then
            match hb : raws[i + 1]? with
            | some (.sym '[' _) =>
              match hc : closeBracketFrom raws (i + 2) with
              | some c =>
                have hcge := closeBracketFrom_ge hc
                let extra ← readBreakLen ctx (rawSrc (raws.extract (i + 2) c)) pos
                let acc := (flushText acc sb).push (.linebreak extra)
                let j := skipSpaces raws (c + 1)
                have hjge := skipSpaces_ge raws (c + 1)
                have hadv : sliceWeight raws j < sliceWeight raws i :=
                  sliceWeight_lt raws h (by omega)
                elabInlinesFrom ctx raws j acc ""
              | none =>
                let extra ← readBreakLen ctx (rawSrc (raws.extract (i + 2) raws.size)) pos
                let acc := (flushText acc sb).push (.linebreak extra)
                have hadv : sliceWeight raws raws.size < sliceWeight raws i :=
                  sliceWeight_lt raws h h
                elabInlinesFrom ctx raws raws.size acc ""
            | _ =>
              let acc := (flushText acc sb).push (.linebreak {})
              let j := skipSpaces raws (i + 1)
              have hjge := skipSpaces_ge raws (i + 1)
              have hadv : sliceWeight raws j < sliceWeight raws i :=
                sliceWeight_lt raws h (by omega)
              elabInlinesFrom ctx raws j acc ""
          else
            let acc := (flushText acc sb).push (.linebreak {})
            let j := skipSpaces raws (i + 1)
            have hjge := skipSpaces_ge raws (i + 1)
            have hadv : sliceWeight raws j < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws j acc ""
        else if let some composed := (accentMarkOf name).bind
            (fun mk => raws[i + 1]?.bind (accentCompose mk)) then
          -- `\'e` and family: composed to NFC at elaboration, one table
          -- with Bib — the accent is content, never a droppable mark.
          have hadv : sliceWeight raws (i + 2) < sliceWeight raws i :=
            sliceWeight_lt raws h (by omega)
          elabInlinesFrom ctx raws (i + 2) acc (sb ++ composed)
        else if let some lit := escapeOf name then
          elabInlinesFrom ctx raws (i + 1) acc (sb ++ lit)
        else if (Lex.textSymbols.lookup name).isSome then
          -- A document may define a symbol's name for itself; its definition
          -- wins, so the symbol only fires when nothing shadows it.
          elabInlinesFrom ctx raws (i + 1) acc
            (sb ++ (Lex.textSymbols.lookup name).getD "")
        else if let some style := argStyles.lookup name then
          let argCtx := { ctx with
            literalText := style == Style.mono || ctx.literalText }
          let j := skipSpaces raws (i + 1)
          have hjge := skipSpaces_ge raws (i + 1)
          match hj : raws[j]? with
          | some (.group body _) =>
            have hjlt := getElem?_lt hj
            have hw : rawWeightList body.toList < sliceWeight raws i :=
              body_lt_slice hj (by simp only [rawWeight]; omega) (by omega)
            let acc := flushText acc sb
            let inner ← elabInlines argCtx body
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1) (acc.push (.styled style inner)) ""
          | some (.word s _) =>
            have hjlt := getElem?_lt hj
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1)
              ((flushText acc sb).push (.styled style #[.text s])) ""
          | _ =>
            diag ctx .E0304 s!"'\\{name}' needs an argument" pos
            elabInlinesFrom ctx raws (i + 1) acc sb
        else if name == "underline" || name == "uline" then
          -- Drawn, not a face change, so not a Style: one group, like \textbf.
          let j := skipSpaces raws (i + 1)
          have hjge := skipSpaces_ge raws (i + 1)
          match hj : raws[j]? with
          | some (.group body _) =>
            have hjlt := getElem?_lt hj
            have hw : rawWeightList body.toList < sliceWeight raws i :=
              body_lt_slice hj (by simp only [rawWeight]; omega) (by omega)
            let acc := flushText acc sb
            let inner ← elabInlines ctx body
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1) (acc.push (.underline inner)) ""
          | some (.word s _) =>
            have hjlt := getElem?_lt hj
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1)
              ((flushText acc sb).push (.underline #[.text s])) ""
          | _ =>
            diag ctx .E0304 s!"'\\{name}' needs an argument" pos
            elabInlinesFrom ctx raws (i + 1) acc sb
        else if name == "label" then
          let j := skipSpaces raws (i + 1)
          have hjge := skipSpaces_ge raws (i + 1)
          match hj : raws[j]? with
          | some (.group keyRaw _) =>
            have hjlt := getElem?_lt hj
            let key := argText ctx keyRaw
            let acc := (flushText acc sb).push (.label key)
            recordLabel ctx key (← get).refTarget pos
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1) acc ""
          | _ =>
            diag ctx .E0304 s!"'\\label' needs a \{key} group" pos
            elabInlinesFrom ctx raws (i + 1) acc sb
        else if name == "ref" || name == "eqref" then
          let j := skipSpaces raws (i + 1)
          have hjge := skipSpaces_ge raws (i + 1)
          match hj : raws[j]? with
          | some (.group keyRaw _) =>
            have hjlt := getElem?_lt hj
            let key := argText ctx keyRaw
            -- Unresolved until the whole document's labels are known:
            -- `resolveRefs` fills the number at the end of elaboration, so
            -- a forward reference costs no second pass over the source.
            let acc := (flushText acc sb).push (.ref key (name == "eqref") "??" none)
            modify fun st => { st with refSites := st.refSites.push (key, pos) }
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1) acc ""
          | _ =>
            diag ctx .E0304 s!"'\\{name}' needs a \{key} group" pos
            elabInlinesFrom ctx raws (i + 1) acc sb
        else if name == "paragraph" || name == "subparagraph" then
          -- The level-4 and level-5 headings are run-in in article
          -- (clsguide §2.2; classes.dtx defines both with a negative
          -- afterskip of 1 em): the title sets bold at the body size on
          -- the text's own line, an em quad between title and text —
          -- never display type, so `heading_hierarchy`'s display levels
          -- are untouched and no new level joins that statement. Both are
          -- below article's secnumdepth of 3, so neither numbers.
          let j0 := skipSpaces raws (i + 1)
          have hj0 := skipSpaces_ge raws (i + 1)
          let j1 := skipStar raws j0
          have hj1 := skipStar_ge raws j0
          if scanBracketArg raws j1 pos matches .took _ then
            warnOnce ctx "section:short" .N0103
              s!"'\\{name}[short]' short title is unused: nothing consumes it yet" pos
          let j := skipShortTitle raws j1 pos
          have hjst := skipShortTitle_ge raws j1 pos
          match hj : raws[j]? with
          | some (.group body _) =>
            have hjlt := getElem?_lt hj
            have hw : rawWeightList body.toList < sliceWeight raws i :=
              body_lt_slice hj (by simp only [rawWeight]; omega) (by omega)
            let acc := flushText acc sb
            let inner ← elabInlines ctx body
            let acc := acc.push (.styled .bold inner)
            -- The run-in gap: classes.dtx's 1 em, as the em quad U+2003
            -- (a fixed-width space, kerned in layout like the \, family).
            -- Whitespace after the title collapses into the quad: the gap
            -- is the declared em, not the em plus the source's newline.
            let j2 := skipSpaces raws (j + 1)
            have hj2 := skipSpaces_ge raws (j + 1)
            have hadv : sliceWeight raws j2 < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws j2 acc "\u2003"
          | _ =>
            diag ctx .E0304 s!"'\\{name}' needs a \{title}" pos
            elabInlinesFrom ctx raws (i + 1) acc sb
        else if name == "href" || name == "link" then
          let j := skipSpaces raws (i + 1)
          have hjge := skipSpaces_ge raws (i + 1)
          let j2 := skipSpaces raws (j + 1)
          have hj2ge := skipSpaces_ge raws (j + 1)
          match hj : raws[j]?, hj2 : raws[j2]? with
          | some (.group urlRaw _), some (.group body _) =>
            have hj2lt := getElem?_lt hj2
            have hw : rawWeightList body.toList < sliceWeight raws i :=
              body_lt_slice hj2 (by simp only [rawWeight]; omega) (by omega)
            let acc := flushText acc sb
            let inner ← elabInlines ctx body
            have hadv : sliceWeight raws (j2 + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j2 + 1)
              (acc.push (.link (argText ctx urlRaw) inner)) ""
          | some (.group urlRaw _), _ =>
            -- One argument: the URL is also the text, which is the common case
            -- for a bare link and saves writing it twice.
            have hjlt := getElem?_lt hj
            let url := argText ctx urlRaw
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1)
              ((flushText acc sb).push (.link url #[.text url])) ""
          | _, _ =>
            diag ctx .E0304 s!"'\\{name}' needs a URL group, optionally followed by text" pos
            elabInlinesFrom ctx raws (i + 1) acc sb
        else if name == "url" then
          -- hyperref/url/xurl's one-argument sibling of `\href`: the URL is
          -- its own text, set mono (url.sty's `\urlstyle{tt}` default).
          let j := skipSpaces raws (i + 1)
          have hjge := skipSpaces_ge raws (i + 1)
          match hj : raws[j]? with
          | some (.group urlRaw _) =>
            have hjlt := getElem?_lt hj
            let url := argText ctx urlRaw
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1)
              ((flushText acc sb).push (.link url #[.styled .mono #[.text url]])) ""
          | _ =>
            diag ctx .E0304 "'\\url' needs a {url} group" pos
            elabInlinesFrom ctx raws (i + 1) acc sb
        else if name == "cite" || name == "citep" || name == "citet" then
          -- natbib's citation commands (natbib manual §2.3): one node per
          -- citation group, keys as written — the brackets or parentheses
          -- around the group are the bibliography style's to draw, so
          -- elaboration keeps the group whole and resolution renders it.
          -- The pre/post note options (`\citep[see][p. 5]{k}`) are not
          -- modelled; a `[` here stays literal text, named in the slice
          -- report rather than silently eaten.
          let j := skipSpaces raws (i + 1)
          have hjge := skipSpaces_ge raws (i + 1)
          match hj : raws[j]? with
          | some (.group keysRaw _) =>
            have hjlt := getElem?_lt hj
            let keys := (((argText ctx keysRaw).splitOn ",").map
              (·.trimAscii.toString)).filter (!·.isEmpty)
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1)
              ((flushText acc sb).push (.cite (name == "citet") keys.toArray)) ""
          | _ =>
            diag ctx .E0304 s!"'\\{name}' needs a \{keys} group" pos
            elabInlinesFrom ctx raws (i + 1) acc sb
        else
          elabInlinesCtrl ctx raws i acc sb name pos h hadv1
  else
    return mergeText (flushText acc sb)
termination_by (ctx.envLimit, ctx.limit, sliceWeight raws i, 3)
decreasing_by all_goals knot_dec

/-- The rest of the control-word chain — graphics, icons, colour, overlay,
recovery — split from `elabInlinesFrom` only so each half stays within the
elaborator's budget for one definition. Same measure, same step shape. -/
def elabInlinesCtrl (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (acc : Array Inline) (sb : String) (name : String) (pos : Pos)
    (h : i < raws.size)
    (_hadv1 : sliceWeight raws (i + 1) < sliceWeight raws i) :
    EM (Array Inline) := do
  if name == "includegraphics" then
    -- graphicx's command, native. The keys that size figures in real
    -- documents are modelled — width, height, scale, keepaspectratio —
    -- and anything else (rotation included) is named and skipped: a
    -- silently dropped key would misplace the figure without a word.
    let j0 := skipSpaces raws (i + 1)
    have hj0 := skipSpaces_ge raws (i + 1)
    let optSrc := bracketRunSrc raws j0
    let j := skipBracketRun raws j0
    have hjb := skipBracketRun_ge raws j0
    let (spec, altText) ← readImageOpts ctx optSrc pos
    match hj : raws[j]? with
    | some (.group pathRaw _) =>
      have hjlt := getElem?_lt hj
      have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
        sliceWeight_lt raws h (by omega)
      elabInlinesFrom ctx raws (j + 1)
        ((flushText acc sb).push (.image (argText ctx pathRaw) spec altText)) ""
    | _ =>
      diag ctx .E0304 "'\\includegraphics' needs a {file} group" pos
      elabInlinesFrom ctx raws (i + 1) acc sb
  else if name == "faIcon" then
    -- fontawesome5's generic spelling: `\faIcon[style]{icon-name}`,
    -- optionally starred for the `-alt` variant. The style argument
    -- selects a Pro face there; here which file covers the scalar is
    -- the per-scalar fallback chain's question, so a style is named
    -- as an ignored option rather than dropped without a word. The
    -- one extension: `label = ...` overrides the icon's default text
    -- alternative, for a context where Font Awesome's own name is
    -- not the right accessible name (`Return to top` on an arrow).
    let j0 := skipSpaces raws (i + 1)
    have hj0 := skipSpaces_ge raws (i + 1)
    let alt := raws[j0]? matches some (.word "*" _)
    let j1 := skipStar raws j0
    have hj1 := skipStar_ge raws j0
    let labelSrc := bracketRunSrc raws j1
    let j := skipBracketRun raws j1
    have hjb := skipBracketRun_ge raws j1
    let label ← readIconLabel ctx labelSrc pos
    match hg : raws[j]? with
    | some (.group nameRaw _) =>
      have hjlt := getElem?_lt hg
      let iconName := (argText ctx nameRaw).trimAscii.toString
        ++ (if alt then "-alt" else "")
      have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
        sliceWeight_lt raws h (by omega)
      match FaIcons.byName[iconName]? with
      | some e =>
        elabInlinesFrom ctx raws (j + 1)
          ((flushText acc sb).push (.icon e.scalar (label.getD e.label))) ""
      | none =>
        diag ctx .E0340 s!"unknown icon '{iconName}'; nothing is rendered" pos
          (help := "icon names are Font Awesome 5 Free's, like 'arrow-up' or 'github'")
        elabInlinesFrom ctx raws (j + 1) (flushText acc sb) ""
    | _ =>
      diag ctx .E0304 "'\\faIcon' needs an {icon-name} group" pos
      elabInlinesFrom ctx raws (i + 1) acc sb
  else if let some e := FaIcons.byMacro[name]? then
    -- The per-icon fontawesome5 command (`\faGithub`, `\faArrowUp`):
    -- the package's own name-to-scalar mapping, carried as data
    -- (`FaData`, generated from fontawesome5-mapping.def).
    elabInlinesFrom ctx raws (i + 1)
      ((flushText acc sb).push (.icon e.scalar e.label)) ""
  else if name == "pagenumber" then
    elabInlinesFrom ctx raws (i + 1) ((flushText acc sb).push .pageNumber) ""
  else if name == "pagecount" then
    elabInlinesFrom ctx raws (i + 1) ((flushText acc sb).push .pageCount) ""
  else if name == "textcolor" then
    let j := skipSpaces raws (i + 1)
    have hjge := skipSpaces_ge raws (i + 1)
    let j2 := skipSpaces raws (j + 1)
    have hj2ge := skipSpaces_ge raws (j + 1)
    match hj : raws[j]?, hj2 : raws[j2]? with
    | some (.group cname _), some (.group body _) =>
      have hj2lt := getElem?_lt hj2
      have hw : rawWeightList body.toList < sliceWeight raws i :=
        body_lt_slice hj2 (by simp only [rawWeight]; omega) (by omega)
      have hadv : sliceWeight raws (j2 + 1) < sliceWeight raws i :=
        sliceWeight_lt raws h (by omega)
      let key := argText ctx cname
      match ctx.palette.resolve key with
      | some c =>
        -- A mix expression is a computed value, not a token: only a
        -- plain palette name rides along for the HTML var(--name).
        let cssName := if (ctx.palette.find? key).isSome then some key else none
        let acc := flushText acc sb
        let inner ← elabInlines ctx body
        elabInlinesFrom ctx raws (j2 + 1) (acc.push (.colored c cssName inner)) ""
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
        let acc := flushText acc sb
        let inner ← elabInlines ctx body
        elabInlinesFrom ctx raws (j2 + 1) (acc ++ inner) ""
    | _, _ =>
      diag ctx .E0304 "'\\textcolor' needs {name} and {content}" pos
      elabInlinesFrom ctx raws (i + 1) acc sb
  else
    elabInlinesCtrl2 ctx raws i acc sb name pos h _hadv1
termination_by (ctx.envLimit, ctx.limit, sliceWeight raws i, 2)
decreasing_by all_goals knot_dec

/-- The chain's tail: colour declarations, overlays, notes, and the
recovery arms. Same measure, same step shape. -/
def elabInlinesCtrl2 (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (acc : Array Inline) (sb : String) (name : String) (pos : Pos)
    (h : i < raws.size)
    (_hadv1 : sliceWeight raws (i + 1) < sliceWeight raws i) :
    EM (Array Inline) := do
  -- `\color{n}`'s marker: inline it reads exactly as the bare name.
  let name := if name.startsWith "@ink:" then (name.drop "@ink:".length).toString
    else name
  if let some c := ctx.palette.resolve name then

    -- With a group, that group is the argument: `\primary{Alex}` means
    -- colour Alex, which is what it looks like. Without one it is a
    -- declaration colouring the rest of the group, as `\bfseries` does.
    -- `resolve`, not `find?`: the name may be the `!`-mix expression
    -- `\color`'s rewrite carries whole, and the mix grammar lives in
    -- one place (`Palette.resolve`). A computed mix is a value, not a
    -- token: only a declared entry rides as the HTML var(--name), the
    -- same rule `\textcolor` holds.
    let cssName := if (ctx.palette.find? name).isSome then some name else none
    let j := skipSpaces raws (i + 1)
    have hjge := skipSpaces_ge raws (i + 1)
    match hj : raws[j]? with
    | some (.group body _) =>
      have hjlt := getElem?_lt hj
      have hw : rawWeightList body.toList < sliceWeight raws i :=
        body_lt_slice hj (by simp only [rawWeight]; omega) (by omega)
      let acc := flushText acc sb
      let inner ← elabInlines ctx body
      have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
        sliceWeight_lt raws h (by omega)
      elabInlinesFrom ctx raws (j + 1) (acc.push (.colored c cssName inner)) ""
    | _ =>
      have hw : rawWeightList (raws.extract (i + 1) raws.size).toList
          < sliceWeight raws i :=
        extract_lt_slice raws.size h (Nat.lt_succ_self i)
      let rest ← elabInlines ctx (raws.extract (i + 1) raws.size)
      let acc := (flushText acc sb).push (.colored c cssName rest)
      have hadv : sliceWeight raws raws.size < sliceWeight raws i :=
        sliceWeight_lt raws h h
      elabInlinesFrom ctx raws raws.size acc ""
  else if let some style := declStyleOf name then
    let declCtx := { ctx with
      literalText := style == Style.mono || ctx.literalText }
    have hw : rawWeightList (raws.extract (i + 1) raws.size).toList
        < sliceWeight raws i :=
      extract_lt_slice raws.size h (Nat.lt_succ_self i)
    let rest ← elabInlines declCtx (raws.extract (i + 1) raws.size)
    let acc := (flushText acc sb).push (.styled style rest)
    have hadv : sliceWeight raws raws.size < sliceWeight raws i :=
      sliceWeight_lt raws h h
    elabInlinesFrom ctx raws raws.size acc ""
  else if name == "ifgiven" then
    let j := skipSpaces raws (i + 1)
    have hjge := skipSpaces_ge raws (i + 1)
    let j2 := skipSpaces raws (j + 1)
    have hj2ge := skipSpaces_ge raws (j + 1)
    match hj : raws[j]?, hj2 : raws[j2]? with
    | some (.group cond _), some (.group tmpl _) =>
      have hj2lt := getElem?_lt hj2
      have hw : rawWeightList tmpl.toList < sliceWeight raws i :=
        body_lt_slice hj2 (by simp only [rawWeight]; omega) (by omega)
      have hadv : sliceWeight raws (j2 + 1) < sliceWeight raws i :=
        sliceWeight_lt raws h (by omega)
      let refs := cond.filter (!isSpace ·)
      match refs.toList with
      | [.ctrl pname _] =>
        match ctx.args.find? (·.1 == pname) with
        | some (_, some _) =>
          let inner ← elabInlines ctx tmpl
          elabInlinesFrom ctx raws (j2 + 1) (acc ++ inner) sb
        | some (_, none) =>
          elabInlinesFrom ctx raws (j2 + 1) acc sb
        | none =>
          diag ctx .E0306 s!"unknown parameter '\\{pname}'" pos
          elabInlinesFrom ctx raws (j2 + 1) acc sb
      | _ =>
        diag ctx .E0306 "expected a parameter reference like {\\team}" pos
        elabInlinesFrom ctx raws (j2 + 1) acc sb
    | _, _ =>
      diag ctx .E0304 "'\\ifgiven' needs {\\param} and {content}" pos
      elabInlinesFrom ctx raws (i + 1) acc sb
  else if overlayCtrls.contains name then
    -- Overlay commands, dim-not-hide (PLAN M5): the content wraps in
    -- a step and dims before its turn — \only included, one overlay
    -- semantics for both backends. Without a group the spec declares:
    -- the rest of this inline scope steps. A spec the model cannot
    -- number keeps the honest W0105 and the content stays shown.
    let j := skipSpaces raws (i + 1)
    have hjge := skipSpaces_ge raws (i + 1)
    match raws[j]?.bind specWord? with
    | some w =>
      match overlayFrom w with
      | some (n, last) =>
        let j2 := skipSpaces raws (j + 1)
        have hj2ge := skipSpaces_ge raws (j + 1)
        match hj2 : raws[j2]? with
        | some (.group gbody _) =>
          have hj2lt := getElem?_lt hj2
          have hw : rawWeightList gbody.toList < sliceWeight raws i :=
            body_lt_slice hj2 (by simp only [rawWeight]; omega) (by omega)
          let acc := flushText acc sb
          let inner ← elabInlines ctx gbody
          have hadv : sliceWeight raws (j2 + 1) < sliceWeight raws i :=
            sliceWeight_lt raws h (by omega)
          elabInlinesFrom ctx raws (j2 + 1) (acc.push (.step n last inner)) ""
        | _ =>
          have hw : rawWeightList (raws.extract (j + 1) raws.size).toList
              < sliceWeight raws i :=
            extract_lt_slice raws.size h (by omega)
          let acc := flushText acc sb
          let inner ← elabInlines ctx (raws.extract (j + 1) raws.size)
          have hadv : sliceWeight raws raws.size < sliceWeight raws i :=
            sliceWeight_lt raws h h
          elabInlinesFrom ctx raws raws.size (acc.push (.step n last inner)) ""
      | none =>
        warnOnce ctx "spec:overlay" .W0105
          s!"overlay specification '{w}' does not name a step; its content is \
shown on every step" pos
          (help := "write a numbered spec: <2>, <2->, or <2-3>; incremental \
specs are not modelled")
        have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        elabInlinesFrom ctx raws (j + 1) acc sb
    | none =>
      elabInlinesFrom ctx raws (i + 1) acc sb
  else if name == "alt" then
    -- `\alt<spec>{active}{otherwise}`: under dim-not-hide both
    -- alternatives are on the page — the active one crisp within its
    -- spec, the other before it — so alternation reads as emphasis
    -- moving, and nothing reflows. The complement of a mid-deck range
    -- is not one range, so the otherwise side stays dimmed past it.
    let j := skipSpaces raws (i + 1)
    have hjge := skipSpaces_ge raws (i + 1)
    match raws[j]?.bind specWord? with
    | some w =>
      let spec := overlayFrom w
      let j2 := skipSpaces raws (j + 1)
      have hj2ge := skipSpaces_ge raws (j + 1)
      let j3 := skipSpaces raws (j2 + 1)
      have hj3ge := skipSpaces_ge raws (j2 + 1)
      match hj2 : raws[j2]?, hj3 : raws[j3]? with
      | some (.group ga _), some (.group gb _) =>
        have hj3lt := getElem?_lt hj3
        have hwa : rawWeightList ga.toList < sliceWeight raws i :=
          body_lt_slice hj2 (by simp only [rawWeight]; omega) (by omega)
        have hwb : rawWeightList gb.toList < sliceWeight raws i :=
          body_lt_slice hj3 (by simp only [rawWeight]; omega) (by omega)
        have hadv : sliceWeight raws (j3 + 1) < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        let acc := flushText acc sb
        match spec with
        | some (n, last) =>
          let ia ← elabInlines ctx ga
          let ib ← elabInlines ctx gb
          elabInlinesFrom ctx raws (j3 + 1)
            ((acc.push (.step n last ia)).push (.step 1 (some (n - 1)) ib)) ""
        | none =>
          warnOnce ctx "spec:overlay" .W0105
            "'\\alt' without a numbered specification shows both \
alternatives on every step" pos
            (help := "write a numbered spec: <2>, <2->, or <2-3>; incremental \
specs are not modelled")
          let ia ← elabInlines ctx ga
          let ib ← elabInlines ctx gb
          elabInlinesFrom ctx raws (j3 + 1) (acc ++ ia ++ ib) ""
      | _, _ =>
        diag ctx .E0304 "'\\alt' needs <spec>{content}{content}" pos
        elabInlinesFrom ctx raws (i + 1) acc sb
    | none =>
      let j3 := skipSpaces raws (j + 1)
      have hj3ge := skipSpaces_ge raws (j + 1)
      match hj2 : raws[j]?, hj3 : raws[j3]? with
      | some (.group ga _), some (.group gb _) =>
        have hj3lt := getElem?_lt hj3
        have hwa : rawWeightList ga.toList < sliceWeight raws i :=
          body_lt_slice hj2 (by simp only [rawWeight]; omega) (by omega)
        have hwb : rawWeightList gb.toList < sliceWeight raws i :=
          body_lt_slice hj3 (by simp only [rawWeight]; omega) (by omega)
        have hadv : sliceWeight raws (j3 + 1) < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        let acc := flushText acc sb
        warnOnce ctx "spec:overlay" .W0105
          "'\\alt' without a numbered specification shows both \
alternatives on every step" pos
          (help := "write a numbered spec: <2>, <2->, or <2-3>; incremental \
specs are not modelled")
        let ia ← elabInlines ctx ga
        let ib ← elabInlines ctx gb
        elabInlinesFrom ctx raws (j3 + 1) (acc ++ ia ++ ib) ""
      | _, _ =>
        diag ctx .E0304 "'\\alt' needs <spec>{content}{content}" pos
        elabInlinesFrom ctx raws (i + 1) acc sb
  else if name == "pause" then
    -- Reachable only inside an argument or definition body; between
    -- blocks the boundary rule steps the rest of the scope.
    warnOnce ctx "spec:pause-inline" .W0105
      "'\\pause' inside an argument cannot step; its content is shown" pos
    elabInlinesFrom ctx raws (i + 1) acc sb
  else if name == "note" then
    -- A speaker note met mid-sentence: no block can stand here, so
    -- the body is stashed for the enclosing frame to drain — the
    -- paragraph flows on unbroken and the note never leaks into it.
    if scanBracketArg raws (i + 1) pos matches .took _ then
      warnOnce ctx "note:options" .N0102
        "'\\note' placement and overlay options are ignored: the note is \
a side channel, never slide content" pos
    let (⟨j, hjge⟩, _, _) ← skipOptArg ctx "note" raws (i + 1) pos
    let js := skipSpaces raws j
    have hjsge := skipSpaces_ge raws j
    if (raws[js]?.bind specWord?).isSome then
      warnOnce ctx "note:options" .N0102
        "'\\note' placement and overlay options are ignored: the note is \
a side channel, never slide content" pos
      let j2 := skipSpaces raws (js + 1)
      have hj2ge := skipSpaces_ge raws (js + 1)
      match hn : raws[j2]? with
      | some (.group nbody _) =>
        modify fun st => { st with pendingNotes := st.pendingNotes.push (nbody, pos) }
        have hadv : sliceWeight raws (j2 + 1) < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        elabInlinesFrom ctx raws (j2 + 1) acc sb
      | _ =>
        have hadv : sliceWeight raws (js + 1) < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        elabInlinesFrom ctx raws (js + 1) acc sb
    else
      match hn : raws[js]? with
      | some (.group nbody _) =>
        modify fun st => { st with pendingNotes := st.pendingNotes.push (nbody, pos) }
        have hadv : sliceWeight raws (js + 1) < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        elabInlinesFrom ctx raws (js + 1) acc sb
      | _ =>
        have hadv : sliceWeight raws j < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        elabInlinesFrom ctx raws j acc sb
  else if name == "centering" then

    -- Between blocks the declaration centres the rest of its scope;
    -- here, inside inline content, there is no block to centre.
    warnOnce ctx "ctrl:centering" .W0108
      "'\\centering' centres nothing inside an argument; content stays left-aligned" pos
      (help := "move '\\centering' to the start of the group or environment body")
    elabInlinesFrom ctx raws (i + 1) acc sb
  else if let some code := reservedCtrl.lookup name then
    warnOnce ctx ("ctrl:" ++ name) code s!"'\\{name}' is not implemented yet; skipped" pos
    let jr := skipReservedArgs raws (i + 1) pos
    if let some bpos := jr.2 then
      warnUnclosed ctx s!"'\\{name}'" bpos
    have hge : i + 1 ≤ jr.1 := skipReservedArgs_ge raws (i + 1) pos 1
    have hadv : sliceWeight raws jr.1 < sliceWeight raws i :=
      sliceWeight_lt raws h (by omega)
    elabInlinesFrom ctx raws jr.1 acc sb
  else if declCtrl.contains name || runningCtrl.contains name then
    -- A native declaration met inside inline content is ours,
    -- misplaced — never "unknown": its arguments address the engine,
    -- not the sentence, so they go with the declaration. A running
    -- declaration carries content, so skipping it is a drop (E0347);
    -- the key/value rest is configuration (W0346).
    if runningCtrl.contains name then
      diag ctx .E0347 s!"'\\{name}' in the body is dropped with its content" pos
        (help := "declare it in the preamble, before '\\begin{document}'")
    else
      warnOnce ctx ("ctrl:" ++ name) .W0346
        s!"'\\{name}' is a declaration; inside inline content it is ignored" pos
        (help := if name == "palette" || name == "tokens" then
            s!"write '\\{name}' between paragraphs, after a blank line; there it applies \
from where it stands"
          else "declare it in the preamble, before '\\begin{document}'")
    let jr := skipReservedArgs raws (i + 1) pos (maxGroups := 2)
    if let some bpos := jr.2 then
      warnUnclosed ctx s!"'\\{name}'" bpos
    have hge : i + 1 ≤ jr.1 := skipReservedArgs_ge raws (i + 1) pos 2
    have hadv : sliceWeight raws jr.1 < sliceWeight raws i :=
      sliceWeight_lt raws h (by omega)
    elabInlinesFrom ctx raws jr.1 acc sb
  else if blockOnly.contains name then
    diag ctx .E0312 s!"'\\{name}' is not allowed here" pos
      (help := "it is a block-level command: use it between paragraphs, " ++
        "not inside inline content")
    elabInlinesFrom ctx raws (i + 1) acc sb
  else
    -- Best effort: the {...} arguments are content, and content is
    -- never dropped for want of a command. Only the formatting is lost.
    warnOnce ctx ("ctrl:" ++ name) .W0301
      s!"unknown command '\\{name}'; its \{...} arguments were kept as text" pos
      (help := "\\define \\name(...) {body} declares it")
      (demote := Compat.styInternal ctx.file name)
    let j0 := skipSpaces raws (i + 1)
    have hj0 := skipSpaces_ge raws (i + 1)
    -- A starred form's `*` belongs to the command, not to the text.
    let j1 := skipStar raws j0
    have hj1 := skipStar_ge raws j0
    -- A leading [...] run is how the author addressed the command,
    -- never their content: kept, it is ink nobody wrote ('[16]'
    -- printed in front of a URL). It goes with the command, named.
    let jr := skipOptionRuns raws j1 pos
    have hjr : j1 ≤ jr.1 := skipOptionRuns_ge raws j1 pos
    if jr.1 > j1 then
      let run := (Parse.rawSrc (raws.extract j1 jr.1)).trimAscii.toString
      diag ctx .W0341
        s!"'{run}' went with unknown command '\\{name}'; an option run is not content" pos
        (help := "content, not options? start the '[' on the next line")
    if let some bpos := jr.2 then
      warnUnclosed ctx s!"'\\{name}'" bpos
    let j2 := skipSpaces raws jr.1
    have hj2 := skipSpaces_ge raws jr.1
    have hcall : sliceWeight raws j2 < sliceWeight raws i :=
      sliceWeight_lt raws h (by omega)
    let (acc2, sb2, ⟨j3, hj3⟩, kept, sp) ← elabUnknownArgs ctx raws j2 0 acc sb false
    -- The control word swallowed a space after it; give back only one
    -- that was really there — `\x{a} b` keeps its space, `\x{a}.b`
    -- gains no ink the author never wrote.
    let sbF := if kept > 0 && sp && j3 < raws.size then " " else sb2
    have hadv : sliceWeight raws j3 < sliceWeight raws i :=
      sliceWeight_lt raws h (by omega)
    elabInlinesFrom ctx raws j3 acc2 sbF
termination_by (ctx.envLimit, ctx.limit, sliceWeight raws i, 0)
decreasing_by all_goals knot_dec

end

unseal String.trimAscii Parse.rawSrc Parse.rawSrcOne Decl.splitEntries
unseal Decl.splitEntry Decl.parseValue Decl.parseDecimal smartPunct
unseal secFmtOfBody applySecFmt applyCounter counterCtrl counterArm
unseal theCounterLevel? sectionLevel String.toInt? String.toNat?
unseal String.Slice.trimAscii String.Slice.trimAsciiStart String.Slice.trimAsciiEnd
unseal String.Slice.dropWhile String.Slice.dropEndWhile String.Slice.skipPrefixWhile

/-- Bind declared parameters from the call site — a user command's, or a
user environment's from the groups after its `\begin`. Returns the bindings
and the index just past the consumed arguments. Shared by inline and block
expansion so both bind identically. -/
def takeArgs (ctx : Ctx) (params : Array Param) (name : String)
    (raws : Array Raw) (start : Nat) (pos : Pos) :
    EM (Array (String × Option (Array Inline)) × Nat) := do
  let (bs, ⟨j, _⟩) ← takeArgsFrom ctx params 0 name raws start pos #[]
  return (bs, j)

/-- Argument consumption only moves forward: the index `takeArgs` returns
is never before the one it was given — the progress half of the
elaborator's termination measure (arch-provable I6), discharged by the
subtype `takeArgsFrom` carries its progress in. -/
theorem take_args_consumes_forward
    (ctx : Ctx) (params : Array Param) (name : String)
    (raws : Array Raw) (start : Nat) (pos : Pos) (st : ESt) :
    start ≤ ((takeArgs ctx params name raws start pos).run st).1.2 := by
  unfold takeArgs
  rcases h : (takeArgsFrom ctx params 0 name raws start pos #[]).run st
    with ⟨⟨bs, j, hj⟩, st'⟩
  simp [StateT.run, bind, StateT.bind, pure, StateT.pure] at h ⊢
  rw [h]
  exact hj

/-- Block environments: those whose content is a block sequence. -/
def blockEnvs : List String :=
  ["itemize", "enumerate", "center", "document", "frame", "columns", "figure",
   "figure*", "table", "table*", "quote", "quotation", "abstract", "ifbackend",
   "nav", "minipage", "block", "alertblock", "exampleblock"]

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
private def columnWidth (ctx : Ctx) (src : String) : Option Nat := Id.run do
  let mut s := src.trimAscii.toString
  let mut stripped := false
  for suffix in ["\\textwidth", "\\linewidth", "\\columnwidth"] do
    if s.endsWith suffix then
      s := ((s.dropEnd suffix.length).trimAscii).toString
      stripped := true
  if s.isEmpty then return if stripped then some 1000 else none
  -- A declared token names the width (`\begin{column}{\colwidth}`, the
  -- beamerposter idiom): its resolved length against the page's text
  -- width, the same permille every fraction spelling produces — W0314
  -- retires exactly where the token resolves.
  if !stripped && s.startsWith "\\" then
    let name := (s.drop 1).toString.trimAscii.toString
    match ctx.tokens.find? name with
    | some g =>
      let tw := ctx.page.width - 2 * ctx.page.hmargin
      let v := g.width.resolve ctx.page.fontSize 0
      if tw > 0 && 0 ≤ v && v ≤ tw then return some ((v * 1000 / tw).toNat)
      else return none
    | none => return none
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
      || n == "bibliography" || n == "bibliographystyle"
      -- A definition or a counter command makes the body
      -- declaration-shaped: it must expand through the block walk,
      -- where the define door and the counter arm stand.
      || n == "define" || counterCtrl n
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

/-- The number an unstarred heading takes, stepped in flow order — or
`none`, which is also the answer for every heading of a class that does
not number. classes.dtx §Sectioning: `\thesection` is `\arabic{section}`
(`\Alph` after `\appendix`), each deeper level prefixes its parent, a
starred form neither numbers nor steps, and secnumdepth is 3, so
`\paragraph` and below never number. A document's own
`\renewcommand{\the<counter>}{...}` format (`ESt.secFmts`) renders
instead where one stands. Stepping a level zeroes the deeper
ones, so `2.1` after a fresh `\section` is impossible by construction. -/
private def sectionNumber (ctx : Ctx) (level : Nat) (starred : Bool) :
    EM (Option String) := do
  if starred || !ctx.numberHeadings || level == 0 || level > 3 then
    return none
  let st ← get
  let (s1, s2, s3) := st.secNums
  let nums := match level with
    | 1 => (s1 + 1, 0, 0)
    | 2 => (s1, s2 + 1, 0)
    | _ => (s1, s2, s3 + 1)
  let num := renderSecLevel st.secFmts nums st.inAppendix secFmtFuel level
  -- The heading is the numbered thing in force from here on: a \label in
  -- the flow after it binds to this number.
  modify fun st => { st with secNums := nums, refTarget := some num }
  return some num

/-- A declaration standing in a group applies to the rest of the group:
`\Huge`, `\bfseries`, `\centering`, a palette name used bare. -/
private def isDeclaration (ctx : Ctx) : Raw → Bool
  | .ctrl n _ =>
    n == "centering" || (declStyles.lookup n).isSome || (ctx.palette.find? n).isSome
  | _ => false

/-- The flow palette `\color{n}`'s block form declares: `fg` set to the
resolved colour — the palette's one resolving site, mixes included —
or `none` when the name resolves to nothing. Outside the block-walk knot
so the arm stays one match. -/
private def inkFlowPalette (ctx : Ctx) (marker : String) : Option Ir.Palette :=
  (ctx.palette.resolve ((marker.drop "@ink:".length).toString)).map fun c =>
    ctx.palette.declare "fg" c

/-- The W0304 the inline colour arm speaks, for the block form. -/
private def warnInkUnknown (ctx : Ctx) (marker : String) (pos : Pos) : EM Unit := do
  let key := (marker.drop "@ink:".length).toString
  warnOnce ctx ("palette:" ++ key) .W0304
    s!"'{key}' is not in the palette; content kept uncoloured" pos
    (help := if ctx.palette.entries.isEmpty then
        "declare colours with \\palette{ name = #RRGGBB }"
      else s!"declared: {String.intercalate ", "
        (ctx.palette.entries.toList.map (·.1))}")

/-- The block form's whole effect but the recursion: declare the flow ink
(the palette with `fg` resolved) and bump the flow state, or warn. One
function outside the block-walk knot, so the arm inside costs the knot's
elaboration one call and one recursion. -/
private def inkFlowDecl (ctx : Ctx) (marker : String) (pos : Pos) :
    EM (Option Ir.Palette) := do
  match inkFlowPalette ctx marker with
  | some pal =>
    modify fun st => { st with flowPalette := some pal
                               flowGen := st.flowGen + 1 }
    return some pal
  | none =>
    warnInkUnknown ctx marker pos
    return none

private def isParRaw : Raw → Bool
  | .par _ => true
  | .ctrl "par" _ => true
  | _ => false

mutual
-- conserves: none — a termination measure, not a content walk
private def rawPars : Raw → Nat
  | .par _ => 1
  | .ctrl n _ => if n == "par" then 1 else 0
  | .group body _ => rawParsList body.toList
  | .math _ body _ => rawParsList body.toList
  | .env _ body _ => rawParsList body.toList
  | _ => 0
-- conserves: none — a termination measure, not a content walk
private def rawParsList : List Raw → Nat
  | [] => 0
  | r :: rest => rawPars r + rawParsList rest
end

/-- The pars standing strictly inside an element: what the par-splice
measure component counts, since a top-level `\par` is a boundary the walk
consumes, never descends into. -/
private def nestedPars : Raw → Nat
  | .group body _ => rawParsList body.toList
  | .math _ body _ => rawParsList body.toList
  | .env _ body _ => rawParsList body.toList
  | _ => 0

-- conserves: none — a termination measure, not a content walk
private def nestedParsList : List Raw → Nat
  | [] => 0
  | r :: rest => nestedPars r + nestedParsList rest

private theorem rawPars_split (r : Raw) :
    rawPars r = (if isParRaw r then 1 else 0) + nestedPars r := by
  cases r with
  | ctrl n _ => simp only [rawPars, nestedPars, isParRaw]; split <;> simp_all
  | _ => simp [rawPars, nestedPars, isParRaw]

private theorem rawParsList_append (a b : List Raw) :
    rawParsList (a ++ b) = rawParsList a + rawParsList b := by
  induction a with
  | nil => simp [rawParsList]
  | cons x xs ih => simp [rawParsList, ih]; omega

private theorem nestedParsList_append (a b : List Raw) :
    nestedParsList (a ++ b) = nestedParsList a + nestedParsList b := by
  induction a with
  | nil => simp [nestedParsList]
  | cons x xs ih => simp [nestedParsList, ih]; omega

private theorem nestedParsList_le (l : List Raw) :
    nestedParsList l ≤ rawParsList l := by
  induction l with
  | nil => simp [nestedParsList, rawParsList]
  | cons x xs ih =>
    have := rawPars_split x
    simp only [nestedParsList, rawParsList]
    omega

/-- A declaration is a control word other than `\par`, so it carries no
pars: duplicating the declarations into each split part costs the measure
nothing. -/
private theorem rawPars_decl {ctx : Ctx} {r : Raw}
    (hnp : isParRaw r = false) (hd : isDeclaration ctx r = true) :
    rawPars r = 0 := by
  cases r with
  | ctrl n _ =>
    simp only [rawPars]
    split
    · simp_all [isParRaw]
    · rfl
  | _ => simp_all [isDeclaration]

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
holds only declarations and space sets nothing and is dropped. Explicit
recursion (state: split parts built, declarations seen, the open part) so
`splitAtPars_pars_lt` — the splice edge of the elabBlocks measure — can
follow the accumulators; the goldens witness it computes what the old
`Id.run` loop did. -/
private def splitAtParsGo (ctx : Ctx) (pos : Pos) :
    List Raw → Array Raw → Array Raw → Array Raw → Array Raw
  | [], out, _, pre =>
    if pre.any (fun r => !(isSpaceOrPar r || isDeclaration ctx r)) then
      out.push (.group pre pos)
    else out
  | r :: rest, out, decls, pre =>
    if isParRaw r then
      splitAtParsGo ctx pos rest
        ((if pre.any (fun r => !(isSpaceOrPar r || isDeclaration ctx r)) then
            out.push (.group pre pos)
          else out).push r)
        decls decls
    else
      splitAtParsGo ctx pos rest out
        (if isDeclaration ctx r then decls.push r else decls) (pre.push r)

private def splitAtPars (ctx : Ctx) (body : Array Raw) (pos : Pos) : Array Raw :=
  splitAtParsGo ctx pos body.toList #[] #[] #[]

private theorem nestedParsList_push (a : Array Raw) (r : Raw) :
    nestedParsList (a.push r).toList = nestedParsList a.toList + nestedPars r := by
  simp [Array.toList_push, nestedParsList_append, nestedParsList]

private theorem rawParsList_push (a : Array Raw) (r : Raw) :
    rawParsList (a.push r).toList = rawParsList a.toList + rawPars r := by
  simp [Array.toList_push, rawParsList_append, rawParsList]

/-- The accounting invariant of the split: however the walk closes its
parts, the pars nested in its output never exceed the pars already nested
in `out`, still open in `pre`, or anywhere in the input — with the
declarations array par-free, so duplicating it into each part costs
nothing. -/
private theorem splitAtParsGo_pars (ctx : Ctx) (pos : Pos) (l : List Raw)
    (out decls pre : Array Raw) (hd : rawParsList decls.toList = 0) :
    nestedParsList (splitAtParsGo ctx pos l out decls pre).toList
      ≤ nestedParsList out.toList + rawParsList pre.toList
        + nestedParsList l := by
  induction l generalizing out decls pre with
  | nil =>
    simp only [splitAtParsGo]
    split
    · rw [nestedParsList_push]
      simp only [nestedPars, nestedParsList]
      omega
    · simp only [nestedParsList]; omega
  | cons r rest ih =>
    simp only [splitAtParsGo]
    split
    · rename_i hpar
      have h1 := ih ((if pre.any (fun r => !(isSpaceOrPar r || isDeclaration ctx r)) then
          out.push (.group pre pos) else out).push r) decls decls hd
      have h2 : nestedParsList ((if pre.any (fun r =>
          !(isSpaceOrPar r || isDeclaration ctx r)) then
            out.push (.group pre pos) else out).push r).toList
          ≤ nestedParsList out.toList + rawParsList pre.toList + nestedPars r := by
        split
        · rw [nestedParsList_push, nestedParsList_push]
          simp only [nestedPars] <;> omega
        · rw [nestedParsList_push]; omega
      have h3 : rawParsList decls.toList = 0 := hd
      have h4 : nestedPars r = 0 := by
        cases r <;> simp_all [isParRaw, nestedPars]
      simp only [nestedParsList]
      omega
    · rename_i hpar
      have hd' : rawParsList (if isDeclaration ctx r then decls.push r
          else decls).toList = 0 := by
        split
        · rename_i hdecl
          rw [rawParsList_push, rawPars_decl (by simpa using hpar) hdecl]
          omega
        · exact hd
      have h1 := ih out (if isDeclaration ctx r then decls.push r else decls)
        (pre.push r) hd'
      have h2 : rawParsList (pre.push r).toList
          = rawParsList pre.toList + rawPars r := rawParsList_push pre r
      have h3 := rawPars_split r
      simp only [isParRaw] at hpar
      simp only [nestedParsList]
      rw [show (if isParRaw r then 1 else 0) = 0 by simp_all [isParRaw]] at h3
      omega

private def directParsList : List Raw → Nat
  | [] => 0
  | r :: rest => (if isParRaw r then 1 else 0) + directParsList rest

private theorem rawParsList_split (l : List Raw) :
    rawParsList l = directParsList l + nestedParsList l := by
  induction l with
  | nil => simp [rawParsList, directParsList, nestedParsList]
  | cons x xs ih =>
    have := rawPars_split x
    simp only [rawParsList, directParsList, nestedParsList]
    omega

private theorem directParsList_mem {l : List Raw} {r : Raw}
    (hmem : r ∈ l) (hr : isParRaw r = true) : 0 < directParsList l := by
  induction l with
  | nil => simp at hmem
  | cons x xs ih =>
    simp only [directParsList]
    rcases List.mem_cons.mp hmem with h | h
    · subst h; simp only [hr, ite_true]; omega
    · have := ih h; omega

private theorem directParsList_pos {body : Array Raw}
    (hp : body.any isParRaw = true) : 0 < directParsList body.toList := by
  rw [Array.any_eq_true] at hp
  obtain ⟨i, hi, hr⟩ := hp
  exact directParsList_mem (Array.getElem_mem_toList hi) hr

/-- The splice edge strictly lightens the par component: what the split
emits nests strictly fewer pars than the group it replaces carried,
because every top-level `\par` of the body — and the guard promises one —
now stands at the boundary depth the walk consumes directly. -/
private theorem splitAtPars_pars_lt (ctx : Ctx) (body : Array Raw) (pos : Pos)
    (hp : body.any isParRaw = true) :
    nestedParsList (splitAtPars ctx body pos).toList
      < rawParsList body.toList := by
  have h1 := splitAtParsGo_pars ctx pos body.toList #[] #[] #[] (by rfl)
  have h2 := rawParsList_split body.toList
  have h3 := directParsList_pos hp
  simp only [splitAtPars]
  simp only [nestedParsList, rawParsList] at h1 ⊢
  omega

-- The pars side of the block knot's measure, mirroring the weight side
-- above: `slicePars` is to `nestedParsList` what `sliceWeight` is to
-- `rawWeightList`, and `visParsGo` mirrors `visWeightGo`. The par-splice
-- edge falls in this component (`slicePars_splice`); every other edge
-- keeps it and falls in the weight component.

private theorem nestedParsList_drop_le (l : List Raw) (i : Nat) :
    nestedParsList (l.drop i) ≤ nestedParsList l := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ n =>
      have := ih n
      simp only [List.drop_succ_cons, nestedParsList]
      omega

private theorem nestedParsList_take_le (l : List Raw) (i : Nat) :
    nestedParsList (l.take i) ≤ nestedParsList l := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp [nestedParsList]
    | succ n =>
      have := ih n
      simp only [List.take_succ_cons, nestedParsList]
      omega

private theorem rawParsList_drop_le (l : List Raw) (i : Nat) :
    rawParsList (l.drop i) ≤ rawParsList l := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ n =>
      have := ih n
      simp only [List.drop_succ_cons, rawParsList]
      omega

private theorem rawParsList_take_le (l : List Raw) (i : Nat) :
    rawParsList (l.take i) ≤ rawParsList l := by
  induction l generalizing i with
  | nil => simp [rawParsList]
  | cons x xs ih =>
    cases i with
    | zero => simp [rawParsList]
    | succ n =>
      have := ih n
      simp only [List.take_succ_cons, rawParsList]
      omega

/-- An extracted piece of a body nests no more pars than the body. -/
private theorem extract_pars_le (body : Array Raw) (a b : Nat) :
    rawParsList (body.extract a b).toList ≤ rawParsList body.toList := by
  rw [Array.toList_extract]
  exact Nat.le_trans (rawParsList_take_le _ _) (rawParsList_drop_le _ _)

private theorem extract_nested_le (body : Array Raw) (a b : Nat) :
    nestedParsList (body.extract a b).toList ≤ nestedParsList body.toList := by
  rw [Array.toList_extract]
  exact Nat.le_trans (nestedParsList_take_le _ _) (nestedParsList_drop_le _ _)

/-- The pars companion of `sliceWeight`: what still nests below the
spine's own boundary depth, from `i` on. -/
private def slicePars (raws : Array Raw) (i : Nat) : Nat :=
  nestedParsList (raws.toList.drop i)

private theorem slicePars_here (raws : Array Raw) {i : Nat} (h : i < raws.size) :
    slicePars raws i = nestedPars raws[i] + slicePars raws (i + 1) := by
  unfold slicePars
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp [nestedParsList]

private theorem slicePars_le (raws : Array Raw) {i j : Nat} (hij : i ≤ j) :
    slicePars raws j ≤ slicePars raws i := by
  unfold slicePars
  rw [show raws.toList.drop j = (raws.toList.drop i).drop (j - i) by
    rw [List.drop_drop]; congr 1; omega]
  exact nestedParsList_drop_le _ _

/-- An element standing anywhere at or past `i` nests no more pars than the
slice from `i`. -/
private theorem elem_pars_le {raws : Array Raw} {j : Nat} {r : Raw}
    (h : raws[j]? = some r) {i : Nat} (hij : i ≤ j) :
    nestedPars r ≤ slicePars raws i := by
  cases Array.getElem?_eq_some_iff.mp h with
  | intro hj hr =>
    have h1 := slicePars_here raws hj
    have h2 := slicePars_le raws hij
    rw [hr] at h1
    omega

private theorem extract_slice_pars_le (raws : Array Raw) (a b : Nat) :
    nestedParsList (raws.extract a b).toList ≤ slicePars raws a := by
  rw [Array.toList_extract]
  exact nestedParsList_take_le _ _

/-- The par-splice strictly lowers the pars component: the split parts
spliced in place of the group nest strictly fewer pars than the group
carried, and the rest of the slice is untouched. -/
private theorem slicePars_splice {raws : Array Raw} {i : Nat}
    (h : i < raws.size) {body : Array Raw} {gpos : Pos}
    (hr : raws[i] = .group body gpos) (hp : body.any isParRaw = true)
    (ctx : Ctx) (pos : Pos) :
    slicePars (raws.extract 0 i
        ++ splitAtPars ctx body pos ++ raws.extract (i + 1) raws.size) i
      < slicePars raws i := by
  have hlen : (raws.extract 0 i).toList.length = i := by
    simp [Array.length_toList]; omega
  have hdrop : ((raws.extract 0 i
      ++ splitAtPars ctx body pos ++ raws.extract (i + 1) raws.size)).toList.drop i
      = (splitAtPars ctx body pos).toList
        ++ (raws.extract (i + 1) raws.size).toList := by
    simp only [Array.toList_append, List.append_assoc]
    rw [List.drop_append_of_le_length (by omega)]
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
  unfold slicePars
  rw [hdrop, nestedParsList_append]
  have h1 := slicePars_here raws h
  rw [hr] at h1
  have h2 := splitAtPars_pars_lt ctx body pos hp
  have h3 : nestedParsList (raws.extract (i + 1) raws.size).toList
      ≤ nestedParsList (raws.toList.drop (i + 1)) := by
    rw [Array.toList_extract]
    exact nestedParsList_take_le _ _
  unfold slicePars at h1
  simp only [nestedPars] at h1
  omega

/-- The pars of every command body the walk can see, mirroring
`visWeightGo`: the pars component a user-command expansion must not raise. -/
private def visParsGo (user : Array UserCmd) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    (if h : k < user.size then rawParsList user[k].body.toList else 0)
      + visParsGo user k

private theorem visParsGo_mono (user : Array UserCmd) {a b : Nat}
    (h : a ≤ b) : visParsGo user a ≤ visParsGo user b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · subst heq; exact Nat.le_refl _
    · have h2 := ih (by omega)
      simp only [visParsGo]
      omega

private theorem visParsGo_congr {u v : Array UserCmd} {n : Nat}
    (h : ∀ m, m < n → u[m]? = v[m]?) : visParsGo u n = visParsGo v n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have h1 := h m (by omega)
    have h2 := ih fun k hk => h k (by omega)
    simp only [visParsGo]
    split <;> split
    · rename_i hu hv
      have : u[m] = v[m] := by
        have := Array.getElem?_eq_getElem hu
        have := Array.getElem?_eq_getElem hv
        simp_all
      rw [this, h2]
    · rename_i hu hv
      rw [Array.getElem?_eq_getElem hu, Array.getElem?_eq_none (by omega)] at h1
      simp at h1
    · rename_i hu hv
      rw [Array.getElem?_eq_getElem hv, Array.getElem?_eq_none (by omega)] at h1
      simp at h1
    · rw [h2]

/-- Expanding a visible command moves its pars out of the visible sum,
mirroring `visWeight_expand`. -/
private theorem visPars_expand {ctx : Ctx} {name : String} {k : Nat}
    {cmd : UserCmd} (h : lookupUser ctx name = some (k, cmd)) :
    rawParsList cmd.body.toList + visParsGo ctx.user k
      ≤ visParsGo ctx.user ctx.limit := by
  have hlt := lookupUser_lt h
  have hfound := lookupUserGo_found h
  obtain ⟨hk, hbody⟩ := Array.getElem?_eq_some_iff.mp hfound
  have hstep : visParsGo ctx.user (k + 1)
      = rawParsList cmd.body.toList + visParsGo ctx.user k := by
    simp only [visParsGo, hk, dite_true, hbody]
  have hmono := visParsGo_mono ctx.user (show k + 1 ≤ ctx.limit by omega)
  omega

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
  -- paragraph never opens with a space glue. Leading label anchors ship
  -- no ink, so the paragraph's first text is judged past them.
  let firstText := (inlines.toList.findIdx? fun x =>
    !(x matches Inline.label _)).getD 0
  if let some (Inline.text s) := inlines[firstText]? then
    if s.startsWith " " then
      let t := String.ofList (s.toList.dropWhile (· == ' '))
      if t.isEmpty then
        inlines := inlines.extract 0 firstText ++ inlines.extract (firstText + 1) inlines.size
      else
        inlines := inlines.modify firstText fun _ => .text t
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
  if inlines.isEmpty then return none
  return some (paraUnder (← get).flowLang inlines)

/-- Store one `\title`-family declaration; `\maketitle` reads them back.
Returns the index just past the consumed arguments, and the malformed run
of an unclosed optional argument for the caller to keep where content can
live. -/
private def takeTitleDecl (ctx : Ctx) (name : String) (raws : Array Raw)
    (start : Nat) (pos : Pos) : EM ({ j : Nat // start ≤ j } × Array Raw) := do
  -- `\title[short]{long}`: the short form feeds furniture we do not render.
  -- Past an unclosed `[`, the group the author wrote is still there —
  -- wherever the line break falls — and best effort takes it as the
  -- argument rather than failing the build.
  let (⟨j, hj⟩, recovered, junk) ← skipOptArg ctx name raws start pos
  match raws[j]? with
  | some (.group body _) =>
    let content ← elabInlines ctx body
    modify fun st => match name with
      | "title" => { st with title := some content }
      | "subtitle" => { st with subtitle := some content }
      | "author" => { st with author := some content }
      | "institute" => { st with institute := some content }
      | _ => { st with date := some content }
    return (⟨j + 1, by omega⟩, junk)
  | _ =>
    if recovered then
      warnSkippedDecl ctx name pos
      return (⟨j, hj⟩, junk)
    diag ctx .E0304 s!"'\\{name}' needs a \{...} group" pos
    return (⟨start, Nat.le_refl start⟩, #[])

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
    inner := push inner none (.section 0 true none xs)
  if let some xs := part st.subtitle then
    inner := push inner (ctx.tokens.find? "subtitlegap") (.para #[.styled (.size "large") xs])
  if let some (c, nm) := tps.separator then
    unless inner.isEmpty && (part st.author).isNone && (part st.institute).isNone
        && (part st.date).isNone do
      -- moloch's own default, `titleseparator linewidth=0.5pt`
      -- (beamerinnerthememoloch.dtx, \moloch@inner@setdefaults), when no
      -- token names one.
      let th := (ctx.tokens.find? "separatorheight").getD
        { width := Dim.Length.ofSp (Dim.pt 1 / 2) }
      inner := push inner none (.rule c nm th)
      pending := ctx.tokens.find? "separatorgap"
  if let some xs := part st.author then
    -- The declared author styling: the font template wraps the name (the
    -- lineage's \bf, or author-font), and the strut props its line open
    -- to the declared height.
    let xs := match tps.authorFont with
      | some tpl => Ir.fillTemplate tpl xs
      | none => xs
    let xs := match tps.authorStrut with
      | some h => #[Ir.Inline.strut h] ++ xs
      | none => xs
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
  | _ =>
    -- The declared title bars bracket the level-0 heading, in the ink
    -- colour (`Design.ofDoc`'s own rule: the palette's `fg`, else black).
    -- `titleBars_text` is the statement that they change no content.
    let ink := match ctx.palette.find? "fg" with
      | some c => (c, some "fg")
      | none => (Ir.Color.black, none)
    let blocks := Ir.titleBars tps ink inner
    -- The declared gap after the whole block (`after` on titlepage): a
    -- standalone skip the next placed line pays, no ink of its own.
    return match tps.after with
      | some g => blocks.push (.spaced g #[])
      | none => blocks

/-- One keyed declaration accepted from the document, remembered for the
`\theme` site: replacing it there is worth a word (W0348). The store logic
is `applyEvent`'s `.declared` arm — one meaning, two doors. -/
private def noteDeclared (ctx : Ctx) (decl key : String) : EM Unit :=
  modify fun st => applyEvent ctx st (.declared decl key)

/-- The engine's own length tokens, LaTeX's page dimen parameters read
onto the token namespace: `paperwidth`/`paperheight` (the physical page),
`textwidth`/`textheight` (the measure between the margins — TeX's own
parameters, TeXbook ch. 23). Resolved eagerly at the read site, as every
token reference is (the `\setlength{\x}{2\x}` rule) — from the declared
page where one is declared, else from what the class already fixes: a
face's `trimDefault`/`safeMargin` row, the slides stage and margins, a
flow class's named paper option. A dimension the class will still adjust
after the preamble fold — the flow classes' text block — is deliberately
not offered: an expression reading it keeps its named error (E0321)
rather than capturing a value the finished page would contradict. -/
private def engineLengthTokens (docClass : Ir.DocClass) (classOptions : String)
    (page : PageSpec) : Array (String × Dim.SymGlue) := Id.run do
  let record := docClass.record
  let dflt : PageSpec := {}
  let opts := (classOptions.splitOn ",").map (·.trimAscii.toString)
  let wh : Option (Dim.Sp × Dim.Sp) :=
    if !(page.width == dflt.width && page.height == dflt.height) then
      some (page.width, page.height)
    else match record.model with
      | .face =>
        if opts.contains "us" then some (Dim.pt 252, Dim.pt 144)
        else if opts.contains "jis" then some (Dim.mm 91, Dim.mm 55)
        else record.trimDefault
      | .frame =>
        some (if opts.contains "aspectratio=169" then Ir.slidesStage169
          else Ir.slidesStage43)
      | .flow =>
        let sized := opts.findSome? fun o =>
          let o := if o.startsWith "paper=" then
            (o.drop "paper=".length).toString ++ "paper" else o
          if o.endsWith "paper" then
            pageSizes.lookup ((o.dropEnd "paper".length).toString)
          else none
        let base := sized.getD (page.width, page.height)
        some (if opts.contains "landscape" then (base.2, base.1) else base)
  let hm : Option Dim.Sp :=
    if page.hmargin != dflt.hmargin then some page.hmargin
    else match record.model with
      | .face => record.safeMargin
      | .frame => some Ir.slidesHMargin
      | .flow => none
  let vm : Option Dim.Sp :=
    if page.vmargin != dflt.vmargin then some page.vmargin
    else match record.model with
      | .face => record.safeMargin
      | .frame => some Ir.slidesVMargin
      | .flow => some dflt.vmargin
  let mut out : Array (String × Dim.SymGlue) := #[]
  if let some (w, h) := wh then
    out := out.push ("paperwidth", { width := Dim.Length.ofSp w })
    out := out.push ("paperheight", { width := Dim.Length.ofSp h })
    if let some m := hm then
      out := out.push ("textwidth", { width := Dim.Length.ofSp (w - 2 * m) })
    if let some m := vm then
      out := out.push ("textheight", { width := Dim.Length.ofSp (h - 2 * m) })
  return out

/-- The engine tokens over the finished page, for body reads: every value
is determined once the class defaults are applied, so all four resolve. -/
private def engineLengthTokensOfPage (page : PageSpec) :
    Array (String × Dim.SymGlue) :=
  #[("paperwidth", { width := Dim.Length.ofSp page.width }),
    ("paperheight", { width := Dim.Length.ofSp page.height }),
    ("textwidth", { width := Dim.Length.ofSp (page.width - 2 * page.hmargin) }),
    ("textheight", { width := Dim.Length.ofSp (page.height - 2 * page.vmargin) })]

/-- `\tokens{...}`: named lengths. Entries are walked one at a time so a
token may be defined by scaling an earlier one (`sep = 0.6 * rhythm`);
parsing the block in one shot would leave those references unresolved. -/
private def applyTokens (ctx : Ctx) (toks : Tokens) (src : String) (pos : Pos)
    (engine : Array (String × Dim.SymGlue) := #[]) : EM Tokens := do
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
      match Decl.parseValue valueSrc (acc.entries ++ engine) with
      | some (.glue g) =>
        acc := acc.declare key g
        noteDeclared ctx "tokens" key
      | some (.dim d) =>
        acc := acc.declare key { width := Dim.Length.ofSp d }
        noteDeclared ctx "tokens" key
      | some v =>
        modify fun st => { st with
          diags := st.diags.push (Decl.wrongType ctx.file "tokens" key
            "a length (10pt, 1.5ex, 0.6 * other)" v pos) }
      | none =>
        -- The expression parser's own verdict names the defect: an
        -- unknown token errors as itself, never resolving to zero.
        let detail := if Decl.looksLikeExpr valueSrc then
            match Decl.parseLengthExpr (acc.entries ++ engine) valueSrc with
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
            noteDeclared ctx "palette" "covered"
          else
            diag ctx .E0332 s!"covered fraction must be 1–99 percent, got '{valueSrc}'" pos
              (help := "the fraction of each covered colour kept over the page; the default is 38\\%")
        | none =>
          diag ctx .E0321 s!"cannot read covered fraction: {valueSrc.quote}" pos
            (help := "a percentage like: covered = 38\\%")
      else
        let put (pal : Palette) (c : Color) : EM Palette := do
          noteDeclared ctx "palette" key
          return pal.declare key c decorative
        match Decl.parseValue valueSrc with
        | some (.color r g b) => pal := ← put pal { r := r, g := g, b := b }
        | some (.cmyk c m y k) => pal := ← put pal (Ir.Color.ofCmyk c m y k)
        | v? =>
          -- A name, an alias, or a mix: all read against what is declared
          -- so far, so two names that must never drift apart share a value.
          match pal.resolve valueSrc with
          | some c => pal := ← put pal c
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


/-- Rule (b)'s three answers for a redefinition of a rendered built-in. -/
private inductive RedefVerdict where
  | wins
  | empty
  | refused (d : Diag)

/-- The W0361 a refused redefinition earns: the built-in stands, and the
message names why the body cannot run — its first losing construct and
that construct's site, or the empty expansion. -/
private def refuseRedef (cmd : UserCmd) (verdict : RedefVerdict) : EM Unit := do
  let msg := match verdict with
    | .refused d =>
      let construct := match d.message.splitOn "'" with
        | _ :: q :: _ => s!"'{q}'"
        | _ => "a construct"
      let site := match d.span with
        | some sp => s!" ({sp.file}:{sp.pos.line})"
        | none => ""
      s!"the redefinition of '\\{cmd.name}' uses {construct}{site}, which the \
engine cannot run; the built-in stands"
    | _ => s!"the redefinition of '\\{cmd.name}' renders nothing; the built-in stands"
  modify fun st => { st with diags := st.diags.push (Diag.of .W0361 msg (some cmd.span)) }

/-- Past the end, a slice weighs nothing. -/
private theorem sliceWeight_end (raws : Array Raw) {j : Nat}
    (h : raws.size ≤ j) : sliceWeight raws j = 0 := by
  unfold sliceWeight
  rw [List.drop_eq_nil_of_le (by simpa using h)]
  rfl

private theorem slicePars_end (raws : Array Raw) {j : Nat}
    (h : raws.size ≤ j) : slicePars raws j = 0 := by
  unfold slicePars
  rw [List.drop_eq_nil_of_le (by simpa using h)]
  rfl

private theorem sliceWeight_zero (a : Array Raw) :
    sliceWeight a 0 = rawWeightList a.toList := rfl

private theorem slicePars_zero (a : Array Raw) :
    slicePars a 0 = nestedParsList a.toList := rfl

/-- Trimming a body's whitespace edges never adds weight or pars. -/
private theorem trimRaws_weight_le (raws : Array Raw) :
    rawWeightList (trimRaws raws).toList ≤ rawWeightList raws.toList := by
  unfold trimRaws trimBy
  exact extract_weight_le ..

private theorem trimRaws_pars_le (raws : Array Raw) :
    rawParsList (trimRaws raws).toList ≤ rawParsList raws.toList := by
  unfold trimRaws trimBy
  exact extract_pars_le ..

/-- The first `{...}` group at or past `k` with the index just after it —
`takeDefine`'s body scan, carrying what the consumed run weighs so a
`\define`'s termination edges can read it. -/
private def defineBody? (raws : Array Raw) (k : Nat) :
    Option ((b : Array Raw) × { k' : Nat //
      k < k'
        ∧ rawWeightList b.toList + sliceWeight raws k' + 1 ≤ sliceWeight raws k
        ∧ rawParsList b.toList + slicePars raws k' ≤ slicePars raws k }) :=
  if h : k < raws.size then
    match hg : raws[k] with
    | .group b _ => some ⟨b, k + 1, by
        have hw := sliceWeight_here raws h
        have hp := slicePars_here raws h
        rw [hg] at hw hp
        simp only [rawWeight] at hw
        simp only [nestedPars] at hp
        omega⟩
    | _ =>
      match defineBody? raws (k + 1) with
      | some ⟨b, k', hf⟩ => some ⟨b, k', by
          obtain ⟨h1, h2, h3⟩ := hf
          have hw := sliceWeight_here raws h
          have hp := slicePars_here raws h
          have := rawWeight_pos raws[k]
          exact ⟨by omega, by omega, by omega⟩⟩
      | none => Option.none
  else none
termination_by raws.size - k

-- Rule (b)'s third answer: a redefinition the engine cannot run may still
-- *declare* the built-in's styling. The scan below reads a refused
-- `\maketitle` body once — expanded through the user commands visible at
-- the preamble's end — for the closed list of declarative title-styling
-- constructs: rules (`\hrule height`), skips (`\vskip`), size and weight
-- declarations, alignment, sitting around the built-in's own datum
-- (`\@title`). Everything else in the body stays refused and counted.

/-- One observed construct of a refused `\maketitle` body, in body order:
`barInterpret` reads the sequence relative to the `\@title` event. -/
private inductive BarEvent where
  /-- A `\vskip` of this length; `\vskip -\parskip` emits nothing — under
  the engine's gap model a declared gap already replaces the paragraph
  skip, so the venue's cancellation is the identity. -/
  | gap (g : Dim.SymGlue)
  /-- A `\vskip` whose length the scan cannot read: the run it stands in
  extracts no gap — an incomplete sum would place a bar where the venue
  never asked. -/
  | gapUnknown
  /-- An `\hrule`; `none` when its declared height cannot be read, which
  abandons that side's extraction entirely. -/
  | bar (w : Option Dim.SymGlue)
  /-- `\@title`, with the size, weight, and alignment declarations in
  force where it stands. -/
  | title (size : Option String) (bold : Bool) (align : Option String)
  /-- `\@author`, with the weight in force and whether a zero-width
  `\rule` strut props its line — the NeurIPS-lineage author `tabular`
  (`\begin{tabular}[t]{c}\bf\rule{\z@}{24\p@}\@author`). Ink, like
  `.content`: it closes the bottom bar's trailing skip. -/
  | author (bold : Bool) (strut : Bool)
  /-- Ink that is not the title — an environment, math, verbatim, a word:
  what closes the bottom bar's trailing skip. -/
  | content

/-- The declarations in force at a point of the scanned body: threaded
along each list, copied into groups and expansions so a scoped
declaration does not escape. -/
private structure BarSt where
  size : Option String := none
  bold : Bool := false
  align : Option String := none

private def barSkipSp : List Raw → List Raw
  | [] => []
  | .space :: rest => barSkipSp rest
  | r :: rest => r :: rest

/-- A length at the head of a raw run: a self-contained word (`0.25in`),
or a number completed by `\p@` (`4\p@`, source2e's one-point register).
`-\parskip` is the identity (`BarEvent.gap`'s docstring says why). -/
private inductive BarLen where
  | len (g : Dim.SymGlue)
  | cancel
  | unread

private def barLength (l : List Raw) : BarLen :=
  match barSkipSp l with
  | .word "-" _ :: rest =>
    match barSkipSp rest with
    | .ctrl "parskip" _ :: _ => .cancel
    | _ => .unread
  | .word w _ :: rest =>
    match Decl.parseValue w with
    | some (.dim d) => .len { width := Dim.Length.ofSp d }
    | some (.glue g) => .len g
    | _ =>
      match barSkipSp rest with
      | .ctrl "p@" _ :: _ =>
        match Decl.parseValue (w ++ "pt") with
        | some (.dim d) => .len { width := Dim.Length.ofSp d }
        | _ => .unread
      | _ => .unread
  | _ => .unread

/-- `\hrule` and its declared height; a bare `\hrule` is TeX's default rule
thickness, 0.4 pt (TeXbook ch. 21). `none` when a written height cannot be
read. -/
private def barRuleWeight (l : List Raw) : Option Dim.SymGlue :=
  match barSkipSp l with
  | .word "height" _ :: rest =>
    match barLength rest with
    | .len g => some g
    | _ => none
  | _ => some { width := Dim.Length.ofSp (Dim.pt 2 / 5) }

/-- A word that is a construct's own operand, never ink: a readable length
or number (`0.25in`, `4`), a sign, or one of the dimension keywords TeX
spells beside `\hrule` and `\hbox`. -/
private def barWordTransparent (w : String) : Bool :=
  ["-", "height", "width", "depth", "to", "plus", "minus"].contains w ||
    (match Decl.parseValue w with
      | some (.dim _) | some (.glue _) | some (.int _) => true
      | _ => false)

private def sizeCtrlNames : List String := Ir.sizeScale.map (·.1)

/-- The author `tabular` of a refused `\maketitle` body, folded to
(bold, strut, author): does it hold `\@author`, under `\bf`, behind a
zero-width `\rule` strut (`\rule{\z@}{...}`, the lineage's spelling —
the strut's own height is not taken; the engine's is `Ir.titleAuthorStrut`).
Groups are looked through; everything else stays the refusal's. -/
private def authorScanList (found : Bool × Bool × Bool) :
    List Raw → Bool × Bool × Bool
  | [] => found
  | .group body _ :: rest =>
    authorScanList (authorScanList found body.toList) rest
  | .ctrl "rule" _ :: rest =>
    let strut := match barSkipSp rest with
      | .group w _ :: _ => match barSkipSp w.toList with
        | .ctrl "z@" _ :: _ => true
        | _ => false
      | _ => false
    authorScanList (found.1, found.2.1 || strut, found.2.2) rest
  | .ctrl n _ :: rest =>
    if n == "bf" || n == "bfseries" then authorScanList (true, found.2) rest
    else if n == "@author" then authorScanList (found.1, found.2.1, true) rest
    else authorScanList found rest
  | _ :: rest => authorScanList found rest
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    (have hb : sizeOf body = 1 + sizeOf body.toList := rfl; omega)

/-- The declarative appearance a refused built-in *environment*
redefinition still declares — the abstract's
`\centerline{\large\bf Abstract}`: sizes and weights anywhere in the
begin body (the heading's font), `\centerline`/`\centering` (its
alignment). `\begin{quote}` is the built-in's own shape and the `\vskip`s
are the engine's rhythm: both stay refused. Groups are looked through with
the state threaded — the closed list wants any declaration in the body. -/
private def envStyleScanList (st : BarSt) : List Raw → BarSt
  | [] => st
  | .group body _ :: rest => envStyleScanList (envStyleScanList st body.toList) rest
  | .ctrl n _ :: rest =>
    if sizeCtrlNames.contains n then envStyleScanList { st with size := some n } rest
    else if n == "bf" || n == "bfseries" then
      envStyleScanList { st with bold := true } rest
    else if n == "centerline" || n == "centering" then
      envStyleScanList { st with align := some "center" } rest
    else envStyleScanList st rest
  | _ :: rest => envStyleScanList st rest
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    (have hb : sizeOf body = 1 + sizeOf body.toList := rfl; omega)

/-- `envStyleScanList`'s verdict as the style fragment the built-in can
honour, `barInterpret`'s font shape. -/
private def envStyleInterpret (sc : BarSt) : Option Ir.ElementStyle :=
  let font : Option (Array Ir.Inline) := match sc.size, sc.bold with
    | some s, true => some #[.styled (.size s) #[.styled .bold #[]]]
    | some s, false => some #[.styled (.size s) #[]]
    | none, true => some #[.styled .bold #[]]
    | none, false => none
  if font.isNone && sc.align.isNone then none
  else some { font := font, align := sc.align }

/-- The scan: one pass over the refused body, expanding the user commands
visible below `bound` (the definition-order rule that terminates every
expansion here), descending into groups with a copy of the declarations in
force so a scoped declaration does not escape. Unrecognised commands are
transparent — the refusal already counted them; this pass only collects
what the closed list can honour. -/
private def barScanList (user : Array UserCmd) (bound : Nat) (st : BarSt)
    (events : Array BarEvent) : List Raw → Array BarEvent
  | [] => events
  | .space :: rest => barScanList user bound st events rest
  | .par _ :: rest => barScanList user bound st events rest
  | .sym _ _ :: rest => barScanList user bound st events rest
  | .word w _ :: rest =>
    let events := if barWordTransparent w then events else events.push .content
    barScanList user bound st events rest
  | .verb _ _ :: rest => barScanList user bound st (events.push .content) rest
  | .math _ _ _ :: rest => barScanList user bound st (events.push .content) rest
  | .env _ body _ :: rest =>
    let (bold, strut, author) := authorScanList (false, false, false) body.toList
    let events := if author then events.push (.author (bold || st.bold) strut)
      else events.push .content
    barScanList user bound st events rest
  | .group body _ :: rest =>
    let events := barScanList user bound st events body.toList
    barScanList user bound st events rest
  | .ctrl n _ :: rest =>
    if n == "vskip" then
      let events := match barLength rest with
        | .len g => events.push (.gap g)
        | .cancel => events
        | .unread => events.push .gapUnknown
      barScanList user bound st events rest
    else if n == "hrule" then
      barScanList user bound st (events.push (.bar (barRuleWeight rest))) rest
    else if sizeCtrlNames.contains n then
      barScanList user bound { st with size := some n } events rest
    else if n == "bf" || n == "bfseries" then
      barScanList user bound { st with bold := true } events rest
    else if n == "centering" then
      barScanList user bound { st with align := some "center" } events rest
    else if n == "raggedright" then
      barScanList user bound { st with align := some "left" } events rest
    else if n == "@title" then
      barScanList user bound st (events.push (.title st.size st.bold st.align)) rest
    else if n == "@author" then
      barScanList user bound st (events.push (.author st.bold false)) rest
    else if n == "@date" then
      barScanList user bound st (events.push .content) rest
    else
      match lookupUserIn user bound n with
      | some (k, cmd) =>
        if _h : k < bound then
          let events := barScanList user k st events cmd.body.toList
          barScanList user bound st events rest
        else
          barScanList user bound st events rest
      | none =>
        barScanList user bound st events rest
termination_by l => (bound, sizeOf l)
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    (have hb : sizeOf body = 1 + sizeOf body.toList := rfl; omega)

/-- The `\vskip`s between two events, summed; `none` when the run holds one
the scan could not read — an incomplete sum would misplace a bar. -/
private def barGapSum (events : Array BarEvent) (lo hi : Nat) :
    Option Dim.SymGlue := Id.run do
  let mut acc : Option Dim.SymGlue := none
  for i in [lo:hi] do
    if h : i < events.size then
      match events[i] with
      | .gap g => acc := some (match acc with | some a => a.add g | none => g)
      | .gapUnknown => return none
      | _ => pure ()
  return acc

/-- Read the event sequence relative to `\@title` into the style fragment
the built-in can honour: the last bar before the title and the first after
it, each placed by the skips beside it, plus the size, weight, and
alignment the title stood under. A body with no `\@title` is not a title
restyling — rule (b) stands alone and nothing is extracted. A bar whose
weight cannot be read extracts nothing on its side. -/
private def barInterpret (events : Array BarEvent) : Option Ir.ElementStyle := Id.run do
  let some t := events.findIdx? (· matches .title _ _ _) | return none
  let mut st : Ir.ElementStyle := {}
  if let some (.title size bold align) := events[t]? then
    st := { st with
      align := align
      font := match size, bold with
        | some s, true => some #[.styled (.size s) #[.styled .bold #[]]]
        | some s, false => some #[.styled (.size s) #[]]
        | none, true => some #[.styled .bold #[]]
        | none, false => none }
  let mut above : Option Nat := none
  for i in [0:t] do
    if h : i < events.size then
      if events[i] matches .bar _ then above := some i
  if let some i := above then
    if h : i < events.size then
      if let .bar (some w) := events[i] then
        st := { st with
          ruleAbove := some w
          ruleAboveSkip := barGapSum events 0 i
          ruleAboveGap := barGapSum events (i + 1) t }
  let mut below : Option Nat := none
  for i in [t + 1:events.size] do
    if h : i < events.size then
      if below.isNone && (events[i] matches .bar _) then below := some i
  if let some j := below then
    if h : j < events.size then
      if let .bar (some w) := events[j] then
        let stop := Id.run do
          for k in [j + 1:events.size] do
            if hk : k < events.size then
              if (events[k] matches .content) || (events[k] matches .author _ _) then
                return k
          return events.size
        st := { st with
          ruleBelow := some w
          ruleBelowGap := barGapSum events (t + 1) j
          ruleBelowSkip := barGapSum events (j + 1) stop }
  -- The author block: the weight is the venue's, read; the strut and the
  -- gap after the block are the engine's rhythm (`Ir.titleAuthorStrut`,
  -- `Ir.titleBlockAfter`) — the venue chooses that the furniture exists,
  -- the engine chooses where it sits (title-bars' gap rule).
  if let some ai := events.findIdx? (· matches .author _ _) then
    if h : ai < events.size then
      if let .author bold strutDeclared := events[ai] then
        if bold then
          st := { st with authorFont := some #[.styled .bold #[]] }
        if strutDeclared then
          st := { st with authorStrut := some Ir.titleAuthorStrut }
        let trailing := Id.run do
          for k in [ai + 1:events.size] do
            if hk : k < events.size then
              match events[k] with
              | .gap _ | .gapUnknown => return true
              | .content | .author _ _ => return false
              | _ => pure ()
          return false
        if trailing then
          st := { st with after := some Ir.titleBlockAfter }
  return if st == ({} : Ir.ElementStyle) then none else some st

/-- `\\define \\name(sig) {body}`, from the element after the `\\define`
head: parses and validates the definition, returning the bound command and
the index after its body. One door for the preamble walk and the body arm,
so the two positions cannot drift (built-in collision W0303, missing-body
E0303, the signature grammar). -/
private def takeDefine (ctx : Ctx) (raws : Array Raw) (i : Nat) (pos : Pos) :
    EM { r : Option UserCmd × Nat // i ≤ r.2 ∧
      ∀ cmd, r.1 = some cmd →
        rawWeightList cmd.body.toList + sliceWeight raws r.2 + 2
            ≤ sliceWeight raws i
          ∧ rawParsList cmd.body.toList + slicePars raws r.2
            ≤ slicePars raws i } := do
  let j := skipSpaces raws i
  have hj : i ≤ j := skipSpaces_ge raws i
  match hjr : raws[j]? with
  | some (.ctrl newName npos) =>
    have hjlt := getElem?_lt hjr
    let warnBuiltin : EM Unit := modify fun st => { st with
      diags := st.diags.push (Diag.of .W0303
        s!"'\\{newName}' is built in; this definition is ignored"
        (some ⟨ctx.file, npos⟩)
        (help := "the built-in already does this; \\define it under another name")) }
    match defineBody? raws (j + 1) with
    | some ⟨b, k', hf⟩ =>
      have h1 : j + 1 < k' := hf.1
      if structuralNames.contains newName then
        warnBuiltin
        return ⟨(none, k'), by
          refine ⟨show i ≤ k' by omega, ?_⟩
          intro _ h; simp at h⟩
      else
        have h2 : rawWeightList b.toList + sliceWeight raws k' + 1
            ≤ sliceWeight raws (j + 1) := hf.2.1
        have h3 : rawParsList b.toList + slicePars raws k'
            ≤ slicePars raws (j + 1) := hf.2.2
        let sigRaws := raws.extract (j + 1) (k' - 1)
        let params ← parseSig ctx (rawSrc sigRaws) pos
        return ⟨(some ⟨newName, params, trimRaws b, ⟨ctx.file, npos⟩⟩, k'), by
          refine ⟨show i ≤ k' by omega, ?_⟩
          intro cmd h
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨_, hg⟩ := Array.getElem?_eq_some_iff.mp hjr
          have hw := sliceWeight_here raws hjlt
          have hpz := slicePars_here raws hjlt
          rw [hg] at hw hpz
          simp only [rawWeight] at hw
          simp only [nestedPars] at hpz
          have h4 := sliceWeight_le raws hj
          have h5 := slicePars_le raws hj
          have h6 := trimRaws_weight_le b
          have h7 := trimRaws_pars_le b
          constructor
          · show rawWeightList (trimRaws b).toList + sliceWeight raws k' + 2
              ≤ sliceWeight raws i
            omega
          · show rawParsList (trimRaws b).toList + slicePars raws k'
              ≤ slicePars raws i
            omega⟩
    | none =>
      if structuralNames.contains newName then
        warnBuiltin
        return ⟨(none, raws.size), by
          refine ⟨show i ≤ raws.size by omega, ?_⟩
          intro _ h; simp at h⟩
      else
        diag ctx .E0303 s!"'\\define \\{newName}' is missing its \{body}" pos
        return ⟨(none, raws.size), by
          refine ⟨show i ≤ raws.size by omega, ?_⟩
          intro _ h; simp at h⟩
  | _ =>
    diag ctx .E0303 "expected '\\define \\name(...)  {body}'" pos
    return ⟨(none, j + 1), by
      refine ⟨show i ≤ j + 1 by omega, ?_⟩
      intro _ h; simp at h⟩

/-- Bind one document-defined command: it enters at the visibility
boundary `min limit user.size`, and the boundary advances past it, so the
walk sees exactly one more command — never the suffix beyond `limit`. One
door for the preamble fold and the body arm, so the two positions cannot
drift; `bindCmd_monotone` is the invariant every edit here must keep. -/
private def bindCmd (ctx : Ctx) (cmd : UserCmd) : Ctx :=
  let b := min ctx.limit ctx.user.size
  { ctx with
    user := (ctx.user.extract 0 b).push cmd ++ ctx.user.extract b ctx.user.size
    limit := b + 1 }

/-- Monotone visibility survives a body definition: a command the walk
cannot see — the one being expanded, standing at `j ≥ limit` — is after
the bind still the same command and still invisible, at its shifted
index. This is the statement the body-`\define` arm of 2026-09-19 01:56
(cffb141, `limit := ctx.user.size + 1`) would have failed to compile: it
re-exposed an expanding command to its own body, and a four-line document
looped forever while PLAN still said nontermination was impossible by
design. A termination guarantee is a theorem the build checks, never a
sentence in a plan (PLAN 2026-09-19). -/
private theorem bindCmd_monotone (ctx : Ctx) (cmd : UserCmd) {j : Nat}
    (hj : ctx.limit ≤ j) (hs : j < ctx.user.size) :
    (bindCmd ctx cmd).limit ≤ j + 1 ∧
      (bindCmd ctx cmd).user[j + 1]? = ctx.user[j]? := by
  simp only [bindCmd]
  have hb : min ctx.limit ctx.user.size ≤ j := by omega
  have hb' : min ctx.limit ctx.user.size ≤ ctx.user.size := by omega
  have hbs : ((ctx.user.extract 0 (min ctx.limit ctx.user.size)).push cmd).size
      = min ctx.limit ctx.user.size + 1 := by
    simp [Nat.min_eq_left hb']
  refine ⟨by omega, ?_⟩
  rw [Array.getElem?_append_right (by omega), hbs,
    show j + 1 - (min ctx.limit ctx.user.size + 1)
      = j - min ctx.limit ctx.user.size by omega,
    Array.getElem?_extract]
  rw [ite_eq_left (by simp; omega),
    show min ctx.limit ctx.user.size + (j - min ctx.limit ctx.user.size) = j by omega]

/-- What a body define adds to the visible sum is exactly its stored body,
which the walk paid a strictly heavier group for: across the bind, the
elabBlocks measure still falls. -/
private theorem bindCmd_visWeight (ctx : Ctx) (cmd : UserCmd) :
    visWeightGo (bindCmd ctx cmd).user (bindCmd ctx cmd).limit
      ≤ visWeightGo ctx.user ctx.limit + rawWeightList cmd.body.toList := by
  simp only [bindCmd]
  have hb' : min ctx.limit ctx.user.size ≤ ctx.user.size := by omega
  have hbs : ((ctx.user.extract 0 (min ctx.limit ctx.user.size)).push cmd).size
      = min ctx.limit ctx.user.size + 1 := by
    simp [Nat.min_eq_left hb']
  have hsame : ∀ m, m < min ctx.limit ctx.user.size →
      ((ctx.user.extract 0 (min ctx.limit ctx.user.size)).push cmd
        ++ ctx.user.extract (min ctx.limit ctx.user.size) ctx.user.size)[m]?
      = ctx.user[m]? := by
    intro m hm
    have hmu : m < ctx.user.size := by omega
    rw [Array.getElem?_append_left (by simp; omega),
      Array.getElem?_push_lt (by simp; omega), Array.getElem?_eq_getElem hmu]
    simp [Array.getElem_extract]
  have hat : ((ctx.user.extract 0 (min ctx.limit ctx.user.size)).push cmd
      ++ ctx.user.extract (min ctx.limit ctx.user.size) ctx.user.size)[
        min ctx.limit ctx.user.size]? = some cmd := by
    rw [Array.getElem?_append_left (by simp), Array.getElem?_push]
    simp
  simp only [visWeightGo]
  obtain ⟨hlt, hcmd⟩ := Array.getElem?_eq_some_iff.mp hat
  rw [visWeightGo_congr fun m hm => hsame m hm]
  simp only [hlt, dite_true, hcmd]
  have := visWeightGo_mono ctx.user (show min ctx.limit ctx.user.size ≤ ctx.limit by omega)
  omega

/-- The pars mirror of `bindCmd_visWeight`: a body define adds exactly its
stored body's pars to the visible sum. -/
private theorem bindCmd_visPars (ctx : Ctx) (cmd : UserCmd) :
    visParsGo (bindCmd ctx cmd).user (bindCmd ctx cmd).limit
      ≤ visParsGo ctx.user ctx.limit + rawParsList cmd.body.toList := by
  simp only [bindCmd]
  have hb' : min ctx.limit ctx.user.size ≤ ctx.user.size := by omega
  have hbs : ((ctx.user.extract 0 (min ctx.limit ctx.user.size)).push cmd).size
      = min ctx.limit ctx.user.size + 1 := by
    simp [Nat.min_eq_left hb']
  have hsame : ∀ m, m < min ctx.limit ctx.user.size →
      ((ctx.user.extract 0 (min ctx.limit ctx.user.size)).push cmd
        ++ ctx.user.extract (min ctx.limit ctx.user.size) ctx.user.size)[m]?
      = ctx.user[m]? := by
    intro m hm
    have hmu : m < ctx.user.size := by omega
    rw [Array.getElem?_append_left (by simp; omega),
      Array.getElem?_push_lt (by simp; omega), Array.getElem?_eq_getElem hmu]
    simp [Array.getElem_extract]
  have hat : ((ctx.user.extract 0 (min ctx.limit ctx.user.size)).push cmd
      ++ ctx.user.extract (min ctx.limit ctx.user.size) ctx.user.size)[
        min ctx.limit ctx.user.size]? = some cmd := by
    rw [Array.getElem?_append_left (by simp), Array.getElem?_push]
    simp
  simp only [visParsGo]
  obtain ⟨hlt, hcmd⟩ := Array.getElem?_eq_some_iff.mp hat
  rw [visParsGo_congr fun m hm => hsame m hm]
  simp only [hlt, dite_true, hcmd]
  have := visParsGo_mono ctx.user (show min ctx.limit ctx.user.size ≤ ctx.limit by omega)
  omega

/-- The note component of the block knot's measure: draining a frame's
stashed notes elaborates bodies that came from the state, not from the
slice, so no weight fact covers that edge — instead the walk is `2`
outside a note body, the drain runs at `1`, and the note-body walk it
opens runs at `0`. Inside a note body the drain is refused (E0359), so
the flag never needs to rise. -/
private def noteFlag (ctx : Ctx) : Nat :=
  match ctx.noteBody with
  | true => 0
  | false => 2


/-- One lexicographic fall in the block knot's six-component measure,
stated so `omega` can discharge each edge from the `have` facts standing
beside the call. -/
private theorem lex6_of {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ : Nat}
    (h : a₁ < a₂ ∨ (a₁ = a₂ ∧ (b₁ < b₂ ∨ (b₁ = b₂ ∧ (c₁ < c₂ ∨ (c₁ = c₂ ∧
      (d₁ < d₂ ∨ (d₁ = d₂ ∧ (e₁ < e₂ ∨ (e₁ = e₂ ∧ f₁ < f₂)))))))))) :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·)
      (Prod.Lex (· < ·) (· < ·)))))
      (a₁, b₁, c₁, d₁, e₁, f₁) (a₂, b₂, c₂, d₂, e₂, f₂) := by
  rcases h with h | ⟨rfl, h⟩
  · exact .left _ _ h
  rcases h with h | ⟨rfl, h⟩
  · exact .right _ (.left _ _ h)
  rcases h with h | ⟨rfl, h⟩
  · exact .right _ (.right _ (.left _ _ h))
  rcases h with h | ⟨rfl, h⟩
  · exact .right _ (.right _ (.right _ (.left _ _ h)))
  rcases h with h | ⟨rfl, h⟩
  · exact .right _ (.right _ (.right _ (.right _ (.left _ _ h))))
  · exact .right _ (.right _ (.right _ (.right _ (.right _ h))))

/-- Discharges the block knot's termination goals: reduce the measure
tuple, then let `omega` combine the `have` facts standing beside each
recursive call into the lexicographic fall. -/
macro "blocks_dec" : tactic =>
  `(tactic| (
    simp_wf
    <;> (first
      | omega
      | (apply lex6_of; omega))))

private theorem rawWeightList_push (a : Array Raw) (r : Raw) :
    rawWeightList (a.push r).toList = rawWeightList a.toList + rawWeight r := by
  simp [Array.toList_push, rawWeightList_append, rawWeightList]

-- conserves: none — a termination measure, not a content walk
private def itemsW : List (Array Raw) → Nat
  | [] => 0
  | it :: rest => rawWeightList it.toList + itemsW rest

-- conserves: none — a termination measure, not a content walk
private def itemsP : List (Array Raw) → Nat
  | [] => 0
  | it :: rest => nestedParsList it.toList + itemsP rest

private theorem itemsW_append (a b : List (Array Raw)) :
    itemsW (a ++ b) = itemsW a + itemsW b := by
  induction a with
  | nil => simp [itemsW]
  | cons x xs ih => simp [itemsW, ih]; omega

private theorem itemsP_append (a b : List (Array Raw)) :
    itemsP (a ++ b) = itemsP a + itemsP b := by
  induction a with
  | nil => simp [itemsP]
  | cons x xs ih => simp [itemsP, ih]; omega

private theorem itemsW_push (a : Array (Array Raw)) (it : Array Raw) :
    itemsW (a.push it).toList = itemsW a.toList + rawWeightList it.toList := by
  simp [Array.toList_push, itemsW_append, itemsW]

private theorem itemsP_push (a : Array (Array Raw)) (it : Array Raw) :
    itemsP (a.push it).toList = itemsP a.toList + nestedParsList it.toList := by
  simp [Array.toList_push, itemsP_append, itemsP]

private theorem itemsW_mem_le {l : List (Array Raw)} {it : Array Raw}
    (h : it ∈ l) : rawWeightList it.toList ≤ itemsW l := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [itemsW]
    rcases List.mem_cons.mp h with h | h
    · subst h; omega
    · have := ih h; omega

private theorem itemsP_mem_le {l : List (Array Raw)} {it : Array Raw}
    (h : it ∈ l) : nestedParsList it.toList ≤ itemsP l := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [itemsP]
    rcases List.mem_cons.mp h with h | h
    · subst h; omega
    · have := ih h; omega

private theorem itemsW_elem_le {a : Array (Array Raw)} {m : Nat}
    {it : Array Raw} (h : a[m]? = some it) :
    rawWeightList it.toList ≤ itemsW a.toList := by
  obtain ⟨hm, hget⟩ := Array.getElem?_eq_some_iff.mp h
  exact itemsW_mem_le (hget ▸ Array.getElem_mem_toList hm)

private theorem itemsP_elem_le {a : Array (Array Raw)} {m : Nat}
    {it : Array Raw} (h : a[m]? = some it) :
    nestedParsList it.toList ≤ itemsP a.toList := by
  obtain ⟨hm, hget⟩ := Array.getElem?_eq_some_iff.mp h
  exact itemsP_mem_le (hget ▸ Array.getElem_mem_toList hm)

/-- The frame body past its options and title group: `\frametitle{...}`
pairs consumed into the running title (the last one wins, named W0311),
everything else kept in order — explicit recursion carrying the kept run's
weight and pars bounds, the facts the frame arm's recursion into the kept
content stands on. -/
private def frameRestGo (ctx : Ctx) (body : Array Raw) (j : Nat)
    (title : Array Inline) (rest : Array Raw) (bound pbound : Nat)
    (hw : rawWeightList rest.toList + sliceWeight body j ≤ bound)
    (hp : nestedParsList rest.toList + slicePars body j ≤ pbound) :
    EM (Array Inline × { rest : Array Raw //
      rawWeightList rest.toList ≤ bound ∧ nestedParsList rest.toList ≤ pbound }) := do
  if h : j < body.size then
    match hj : body[j], body[j + 1]? with
    | .ctrl "frametitle" fpos, some (.group t _) =>
      -- The last title wins, as in beamer, but never silently: the
      -- author wrote two and only one can show.
      unless title.isEmpty do
        diag ctx .W0311 "this '\\frametitle' replaces the frame's earlier title"
          (some fpos) (help := "the last one wins; remove the other '\\frametitle'")
      let title ← elabInlines ctx t
      frameRestGo ctx body (j + 2) title rest bound pbound
        (by have := sliceWeight_le body (show j ≤ j + 2 by omega); omega)
        (by have := slicePars_le body (show j ≤ j + 2 by omega); omega)
    | r', _ =>
      frameRestGo ctx body (j + 1) title (rest.push r') bound pbound
        (by
          have h1 := sliceWeight_here body h
          rw [hj] at h1
          rw [rawWeightList_push]
          omega)
        (by
          have h1 := slicePars_here body h
          rw [hj] at h1
          rw [nestedParsList_push]
          have h2 := rawPars_split r'
          have h3 := nestedParsList_le rest.toList
          omega)
  else
    have h1 := sliceWeight_end body (show body.size ≤ j by omega)
    have h2 := slicePars_end body (show body.size ≤ j by omega)
    return (title, ⟨rest, by omega, by omega⟩)
termination_by body.size - j

/-- A subfigure body past its width group: `\caption` consumed into the
sub-caption (last one wins, W0311) and `\centering` satisfied, everything
else kept — the subfigure mirror of `frameRestGo`, same bounds. -/
private def subRestGo (ctx : Ctx) (sn : String) (sbody : Array Raw) (q : Nat)
    (sCaption : Array Inline) (sCapAbove : Bool) (sRest : Array Raw)
    (bound pbound : Nat)
    (hw : rawWeightList sRest.toList + sliceWeight sbody q ≤ bound)
    (hp : nestedParsList sRest.toList + slicePars sbody q ≤ pbound) :
    EM (Array Inline × Bool × { sRest : Array Raw //
      rawWeightList sRest.toList ≤ bound ∧ nestedParsList sRest.toList ≤ pbound }) := do
  if h : q < sbody.size then
    match hq : sbody[q] with
    | .ctrl "caption" cpos =>
      let (⟨q2, hq2⟩, _, _) ← skipOptArg ctx "caption" sbody (q + 1) cpos
      let q3 := skipSpaces sbody q2
      have hq3 := skipSpaces_ge sbody q2
      have hadv : sliceWeight sbody q3 ≤ sliceWeight sbody q :=
        sliceWeight_le sbody (by omega)
      have hadvp : slicePars sbody q3 ≤ slicePars sbody q :=
        slicePars_le sbody (by omega)
      match sbody[q3]? with
      | some (.group t _) =>
        unless sCaption.isEmpty do
          diag ctx .W0311
            s!"this '\\caption' replaces the {sn}'s earlier caption"
            (some cpos)
            (help := "the last one wins; remove the other '\\caption'")
        let sCaption ← elabInlines ctx t
        let sCapAbove := sRest.all isSpaceOrPar
        subRestGo ctx sn sbody (q3 + 1) sCaption sCapAbove sRest bound pbound
          (by have := sliceWeight_le sbody (show q3 ≤ q3 + 1 by omega); omega)
          (by have := slicePars_le sbody (show q3 ≤ q3 + 1 by omega); omega)
      | _ =>
        diag ctx .E0304 "'\\caption' needs a {text} group" cpos
        subRestGo ctx sn sbody q3 sCaption sCapAbove sRest bound pbound
          (by omega) (by omega)
    | .ctrl "centering" _ =>
      subRestGo ctx sn sbody (q + 1) sCaption sCapAbove sRest bound pbound
        (by have := sliceWeight_le sbody (show q ≤ q + 1 by omega); omega)
        (by have := slicePars_le sbody (show q ≤ q + 1 by omega); omega)
    | r' =>
      subRestGo ctx sn sbody (q + 1) sCaption sCapAbove (sRest.push r') bound pbound
        (by
          have h1 := sliceWeight_here sbody h
          rw [hq] at h1
          rw [rawWeightList_push]
          omega)
        (by
          have h1 := slicePars_here sbody h
          rw [hq] at h1
          rw [nestedParsList_push]
          have h2 := rawPars_split r'
          omega)
  else
    have h1 := sliceWeight_end sbody (show sbody.size ≤ q by omega)
    have h2 := slicePars_end sbody (show sbody.size ≤ q by omega)
    return (sCaption, sCapAbove, ⟨sRest, by omega, by omega⟩)
termination_by sbody.size - q
decreasing_by all_goals omega

/-- A float's alignment grouping is transparent: a `center` (or
`centering`) environment child of a float body is spliced into the body
before the float walk, so the `\caption` and `\label` inside it are the
float's own — LaTeX's manual spells the figure idiom
`\begin{figure}\begin{center} … \caption{…} \end{center}\end{figure}`, and
inside a float the group adds no box: the float centres already, as the
`\centering` arm of `figureGo` says. The bounds returned are what the
float walk's own invariant reads: splicing only ever drops wrapper
weight. -/
-- conserves: none — deliberately drops the grouping wrapper; the float
-- walk's census facts stand over the spliced body
private def spliceCenterGo (l : List Raw) (acc : Array Raw)
    (bound pbound : Nat)
    (hw : rawWeightList acc.toList + rawWeightList l ≤ bound)
    (hp : nestedParsList acc.toList + nestedParsList l ≤ pbound) :
    { a : Array Raw // rawWeightList a.toList ≤ bound ∧
        nestedParsList a.toList ≤ pbound } :=
  match l with
  | [] =>
    ⟨acc, by simp [rawWeightList] at hw; omega,
      by simp [nestedParsList] at hp; omega⟩
  | .env en ebody epos :: rest =>
    if en == "center" || en == "centering" then
      spliceCenterGo (ebody.toList ++ rest) acc bound pbound
        (by
          rw [rawWeightList_append]
          simp only [rawWeightList, rawWeight] at hw
          omega)
        (by
          rw [nestedParsList_append]
          have hle := nestedParsList_le ebody.toList
          simp only [nestedParsList, nestedPars] at hp
          omega)
    else
      spliceCenterGo rest (acc.push (.env en ebody epos)) bound pbound
        (by
          rw [rawWeightList_push]
          simp only [rawWeightList] at hw
          omega)
        (by
          rw [nestedParsList_push]
          simp only [nestedParsList] at hp
          omega)
  | r :: rest =>
    spliceCenterGo rest (acc.push r) bound pbound
      (by
        rw [rawWeightList_push]
        simp only [rawWeightList] at hw
        omega)
      (by
        rw [nestedParsList_push]
        simp only [nestedParsList] at hp
        omega)
termination_by rawWeightList l
decreasing_by
  · simp only [rawWeightList, rawWeight, rawWeightList_append]; omega
  · simp only [rawWeightList, rawWeight]; omega
  · simp only [rawWeightList]; have := rawWeight_pos r; omega

/-- The list split at its `\item`s: items with their overlay steps and the
`\pause` count standing before each, the warnings of the old in-loop split
fired at the same points — explicit recursion so the split's conservation
(no item outweighs the body) is a fact the item elaboration stands on. -/
private def itemSplitGo (ctx : Ctx) (body : Array Raw) (pos : Pos) (j : Nat)
    (items : Array (Array Raw)) (steps : Array (Option (Nat × Option Nat)))
    (itemPauses : Array Nat) (pauses : Nat) (curItem : Array Raw)
    (curStep : Option (Nat × Option Nat)) (curPauses : Nat)
    (awaitSpec inOpt seen strayDiagged : Bool) (bound pbound : Nat)
    (hw : itemsW items.toList + rawWeightList curItem.toList
      + sliceWeight body j ≤ bound)
    (hp : itemsP items.toList + nestedParsList curItem.toList
      + slicePars body j ≤ pbound) :
    EM { r : Array (Array Raw) × Array (Option (Nat × Option Nat)) × Array Nat //
      itemsW r.1.toList ≤ bound ∧ itemsP r.1.toList ≤ pbound } := do
  if h : j < body.size then
    match body[j] with
    | .ctrl "item" _ =>
      if seen then
        itemSplitGo ctx body pos (j + 1) (items.push curItem)
          (steps.push curStep) (itemPauses.push curPauses) pauses #[]
          none pauses true inOpt true strayDiagged bound pbound
          (by
            have hwj := sliceWeight_here body h
            have hw1 := rawWeight_pos body[j]
            rw [itemsW_push]; simp [rawWeightList]; omega)
          (by
            have hpj := slicePars_here body h
            rw [itemsP_push]; simp [nestedParsList]; omega)
      else
        itemSplitGo ctx body pos (j + 1) items steps itemPauses pauses #[]
          none pauses true inOpt true strayDiagged bound pbound
          (by
            have hwj := sliceWeight_here body h
            have hw1 := rawWeight_pos body[j]
            simp [rawWeightList]; omega)
          (by
            have hpj := slicePars_here body h
            simp [nestedParsList]; omega)
    | .ctrl "pause" _ =>
      -- Counted for the items that follow; kept in the item so a
      -- mid-item pause still steps the item's own remaining blocks.
      if seen then
        itemSplitGo ctx body pos (j + 1) items steps itemPauses (pauses + 1)
          (curItem.push body[j]) curStep curPauses awaitSpec inOpt seen
          strayDiagged bound pbound
          (by
            have hwj := sliceWeight_here body h
            rw [rawWeightList_push]; omega)
          (by
            have hpj := slicePars_here body h
            have h2 := rawPars_split body[j]
            rw [nestedParsList_push]; omega)
      else
        itemSplitGo ctx body pos (j + 1) items steps itemPauses (pauses + 1)
          curItem curStep curPauses awaitSpec inOpt seen strayDiagged bound pbound
          (by
            have hwj := sliceWeight_here body h
            have hw1 := rawWeight_pos body[j]
            omega)
          (by
            have hpj := slicePars_here body h
            have h2 := rawPars_split body[j]
            omega)
    | item =>
      -- Inside a consumed `\item[...]` override: dropped through its
      -- closing bracket.
      if inOpt then
        let inOpt := !(item matches .sym ']' _)
        itemSplitGo ctx body pos (j + 1) items steps itemPauses pauses curItem
          curStep curPauses awaitSpec inOpt seen strayDiagged bound pbound
          (by
            have hwj := sliceWeight_here body h
            have hw1 := rawWeight_pos body[j]
            omega)
          (by
            have hpj := slicePars_here body h
            have h2 := rawPars_split body[j]
            omega)
      else
      -- `\item<2->`: the spec directly after the item names the step its
      -- content reveals at, dim-not-hide (PLAN M5). `\item[marker]` is
      -- enumitem's per-item override: consumed and named (W0110).
      if seen && awaitSpec && !isSpace item then
        if item matches .sym '[' _ then
          warnOnce ctx "item:marker" .W0110
            "'\\item' [marker] override is not modelled; the level's marker stands" pos
            (help := "\\style{itemize}{ marker = {...} } declares a level's marker")
          itemSplitGo ctx body pos (j + 1) items steps itemPauses pauses curItem
            curStep curPauses false true seen strayDiagged bound pbound
            (by
              have hwj := sliceWeight_here body h
              have hw1 := rawWeight_pos body[j]
              omega)
            (by
              have hpj := slicePars_here body h
              have h2 := rawPars_split body[j]
              omega)
        else if let some w := specWord? item then
          let curStep ← match overlayFrom w with
            | some s => pure (some s)
            | none => do
              warnOnce ctx "spec:overlay" .W0105
                s!"overlay specification '{w}' does not name a step; its \
content is shown on every step" pos
                (help := "write a numbered spec: <2>, <2->, or <2-3>; incremental \
specs are not modelled")
              pure curStep
          itemSplitGo ctx body pos (j + 1) items steps itemPauses pauses curItem
            curStep curPauses awaitSpec inOpt seen strayDiagged bound pbound
            (by
              have hwj := sliceWeight_here body h
              have hw1 := rawWeight_pos body[j]
              omega)
            (by
              have hpj := slicePars_here body h
              have h2 := rawPars_split body[j]
              omega)
        else
          itemSplitGo ctx body pos (j + 1) items steps itemPauses pauses
            (curItem.push body[j]) curStep curPauses false inOpt seen strayDiagged
            bound pbound
            (by
              have hwj := sliceWeight_here body h
              rw [rawWeightList_push]
              omega)
            (by
              have hpj := slicePars_here body h
              have h2 := rawPars_split body[j]
              rw [nestedParsList_push]
              omega)
      else if seen then
        itemSplitGo ctx body pos (j + 1) items steps itemPauses pauses
          (curItem.push body[j]) curStep curPauses awaitSpec inOpt seen strayDiagged
          bound pbound
          (by
            have hwj := sliceWeight_here body h
            rw [rawWeightList_push]
            omega)
          (by
            have hpj := slicePars_here body h
            have h2 := rawPars_split body[j]
            rw [nestedParsList_push]
            omega)
      else do
        if !isSpaceOrPar item && !strayDiagged then
          diag ctx .E0310 s!"content before the first '\\item'" pos
        itemSplitGo ctx body pos (j + 1) items steps itemPauses pauses curItem
          curStep curPauses awaitSpec inOpt seen
          (strayDiagged || !isSpaceOrPar item) bound pbound
          (by
            have hwj := sliceWeight_here body h
            have hw1 := rawWeight_pos body[j]
            omega)
          (by
            have hpj := slicePars_here body h
            have h2 := rawPars_split body[j]
            omega)
  else
    have h1 := sliceWeight_end body (show body.size ≤ j by omega)
    have h2 := slicePars_end body (show body.size ≤ j by omega)
    if seen then
      return ⟨(items.push curItem, steps.push curStep, itemPauses.push curPauses),
        show itemsW (items.push curItem).toList ≤ bound by rw [itemsW_push]; omega,
        show itemsP (items.push curItem).toList ≤ pbound by rw [itemsP_push]; omega⟩
    else
      return ⟨(items, steps, itemPauses),
        show itemsW items.toList ≤ bound by omega,
        show itemsP items.toList ≤ pbound by omega⟩
termination_by body.size - j

/-- The block spine's per-iteration flow refresh: a body declaration
anywhere earlier in flow order — this scope or a nested one — reaches the
walk through the state; the generation guard makes the common
no-declaration path one Nat comparison. Named so the refresh provably
leaves every measure component alone (`flowCtx_measure`). -/
private def flowCtx (ctx : Ctx) (st : ESt) (gen : Nat) : Ctx :=
  if st.flowGen != gen then
    { ctx with palette := st.flowPalette.getD ctx.palette
               tokens := st.flowTokens.getD ctx.tokens }
  else ctx

private theorem flowCtx_measure (ctx : Ctx) (st : ESt) (gen : Nat) :
    (flowCtx ctx st gen).envLimit = ctx.envLimit
      ∧ noteFlag (flowCtx ctx st gen) = noteFlag ctx
      ∧ visParsGo (flowCtx ctx st gen).user (flowCtx ctx st gen).limit
        = visParsGo ctx.user ctx.limit
      ∧ visWeightGo (flowCtx ctx st gen).user (flowCtx ctx st gen).limit
        = visWeightGo ctx.user ctx.limit := by
  unfold flowCtx
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- A context sharing `ctx`'s measure components, the fact carried beside
it: what a knot edge needs to know about a context that changed only
fields the measure never reads. -/
private def MCtx (ctx : Ctx) := { c : Ctx // c.envLimit = ctx.envLimit
  ∧ noteFlag c = noteFlag ctx
  ∧ visParsGo c.user c.limit = visParsGo ctx.user ctx.limit
  ∧ visWeightGo c.user c.limit = visWeightGo ctx.user ctx.limit }

/-- The `{tabular}` arm, whole: no recursion into the block walk, so it
lives outside the knot to keep the pack small. -/
private def tabularArm (ctx : Ctx) (n : String) (body : Array Raw)
    (pos : Pos) (blocks : Array Block) : EM (Array Block) := do
  let mut blocks := blocks
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
  return blocks

/-- A display-math environment, outside the knot to keep the pack small. -/
private def displayMathArm (ctx : Ctx) (numbered : Bool) (body : Array Raw) (pos : Pos)
    (blocks : Array Block) : EM (Array Block) := do
  let mut blocks := blocks
  let (cleaned, keys, nonum) ← stripMathMeta ctx body
  let inl ← elabMathInline ctx true cleaned pos
  if numbered && !nonum then
    -- The display takes the next equation number (amsldoc §3);
    -- its labels bind to it, scoped to the environment as
    -- LaTeX's \refstepcounter group is.
    let num := (← get).eqNum + 1
    modify fun st => { st with eqNum := num }
    for key in keys do
      recordLabel ctx key (some (toString num)) pos
    let content := keys.map (Ir.Inline.label ·) |>.push inl
    blocks := blocks.push (.equation s!"({num})" content)
  else
    -- The unnumbered forms; a label here binds to whatever the
    -- flow last numbered, as LaTeX's \@currentlabel does.
    for key in keys do
      recordLabel ctx key (← get).refTarget pos
    let content := keys.map (Ir.Inline.label ·) |>.push inl
    blocks := blocks.push (.center #[.para content])
  return blocks

/-- An alignment environment, outside the knot: no recursion into the
block walk. Row numbers are still owed (W0015): a label here binds to
nothing, so a reference to it is the named ??, never a silently wrong
number. -/
private def alignEnvArm (ctx : Ctx) (n : String) (kind : Math.GridKind)
    (numbered : Bool) (body : Array Raw) (pos : Pos) (blocks : Array Block) :
    EM (Array Block) := do
  let (cleaned, keys, _) ← stripMathMeta ctx body
  for key in keys do
    recordLabel ctx key none pos
  let inl ← elabMathEnv ctx n kind numbered cleaned pos
  let content := keys.map (Ir.Inline.label ·) |>.push inl
  return blocks.push (.center #[.para content])

/-- The `{tikzpicture}` arm, outside the knot: the rendered subset —
shapes evaluate here, loops unrolled, expressions reduced, colours
resolved against the palette — and everything the subset cannot render is
a named loss beside the shapes that did (W0334 outside the subset, E0333
unreadable inside it), never one blanket W0307. Node-body math elaborates
through the same parser a paragraph's does; a formula the parser cannot
model degrades to source text, named (W0012), as it would in a paragraph. -/
private def tikzArm (ctx : Ctx) (body : Array Raw) (pos : Pos)
    (blocks : Array Block) : EM (Array Block) := do
  let mut blocks := blocks
  let mathOf (d : Bool) (raws : Array Parse.Raw) :
      Ir.Inline × Array Picture.PDiag :=
    let expanded := expandMathList ctx.user ctx.limit #[] raws.toList
    match MathParse.parseMath expanded with
    | .ok (l, _) => (.formula d (Parse.rawSrc raws) l, #[])
    | .error what => (.math d (Parse.rawSrc raws),
        #[(.W0012, s!"math with {what} is not rendered yet; the \
formula is set as source text")])
  let (pic, pdiags) := Picture.elabPicture ctx.palette body mathOf
  for (code, msg) in pdiags do
    warnOnce ctx ("picture:" ++ msg) code msg pos
      (help := "the rendered subset is \\fill...rectangle, \\node at, \
\\foreach, and \\pgfmath(truncate)setmacro")
  unless pic.shapes.isEmpty do
    blocks := blocks.push (.picture pic)
  -- An all-refused picture still owes the reader its place: the
  -- float around it would otherwise collapse to orphan captions.
  -- A placeholder box marks it, as an unloadable image's does.
  if pic.shapes.isEmpty && !pdiags.isEmpty then
    warnOnce ctx "picture:placeholder" .W0362
      "no part of this picture is inside the rendered subset; a \
placeholder box marks its place" pos
      (help := "the box holds the diagram's place; \\allow{W0362} \
accepts the loss")
    blocks := blocks.push (.picture (Picture.placeholder DiagCode.W0362.code))
  return blocks

/-- The `\maketitle`/`\titlepage` arm, outside the knot: no recursion
into the block walk. LaTeX typesets the title once: \maketitle disables
itself (classes.dtx, \global\let\maketitle\relax), which is also what
keeps the document to one level-0 heading — a second call warns and
produces nothing. -/
private def maketitleArm (ctx : Ctx) (n : String) (pos : Pos)
    (blocks : Array Block) : EM (Array Block) := do
  let mut blocks := blocks
  if (← get).titleDone then
    warnOnce ctx "ctrl:maketitle2" .W0322
      s!"a second '\\{n}' is ignored; the title is typeset once" pos
      (help := "LaTeX's \\maketitle disables itself after use (classes.dtx)")
    return blocks
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
    -- The flow classes centre the title block, as `\@maketitle`
    -- does — unless the `titlepage` style declares its matter
    -- ragged left, the same declaration the slides branch reads.
    modify fun st => { st with titleDone := true }
    let tps := (ctx.styles.find? "titlepage").getD {}
    let content := if tps.align == some "left" then inner else #[.center inner]
    blocks := blocks ++ content
  return blocks

/-- The `{nav}` optional argument's own facts — label, pin, offset,
reveal — parsed outside the knot. -/
private def navSpecOf (ctx : Ctx) (inner : String) (pos : Pos) :
    EM Ir.NavSpec := do
  let mut spec : Ir.NavSpec := {}
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
  return spec

/-- Flush the open paragraph, if any: the shared prelude of every
boundary arm. -/
private def flushPara (ctx : Ctx) (blocks : Array Block) (cur : Array Raw) :
    EM (Array Block) := do
  if !cur.isEmpty then
    if let some p ← mkPara ctx cur then
      return blocks.push p
  return blocks

-- The well-founded translation whnf-reduces through the knot's body when
-- it assembles the fixpoint and its equations; everything the arms call is
-- data to that process, never proof material, and unfolding it is what
-- blows the elaboration budget. Sealed for the knot, unsealed right after.
seal String.trimAscii Parse.rawSrc Parse.rawSrcOne Decl.splitEntries
seal Decl.splitEntry Decl.parseValue Decl.parseDecimal smartPunct
seal String.Slice.trimAscii String.Slice.trimAsciiStart String.Slice.trimAsciiEnd
seal String.Slice.dropWhile String.Slice.dropEndWhile String.Slice.skipPrefixWhile
seal takeArgs mkPara flushPara stripMathMeta
seal elabMathInline elabMathEnv applyPalette applyTokens parseColSpec
seal titleBlocks Picture.elabPicture MathParse.parseMath
seal Decl.parseBlock Decl.parseLength Decl.parseGlue skipOptArg takeTitleDecl
seal sectionNumber columnWidth cmidRange trimRawEdges
seal recordLabel refuseRedef dropEnvArgs skipReservedArgs takeDefine
seal secFmtDefine? secFmtOfBody applySecFmt applyCounter counterCtrl counterArm
seal theCounterLevel? String.toInt? String.toNat?
seal Ir.padTableRows Ir.setAltBlocks Ir.plainText
seal bodyIsBlock bodyIsBlockList bodyIsBlockOne overlayTakesBlocks
seal DiagCode.ofString? Diag.of renderedBuiltins structuralNames
seal declCtrl runningCtrl titleCtrls overlayCtrls blockEnvs reservedEnv
seal displayMathEnvs alignEnvs isMathEnv sectionLevel specWord? overlayFrom
seal lookupUser lookupUserEnv isArgument isCenteringRaw isParRaw splitAtPars
seal scanBracketArg Parse.inputEnvFile?

-- The block knot: the spine (`elabBlocksGo`), its two dispatch arms, the
-- loop members that recurse into accumulated content, and the redefinition
-- gate — mutually recursive, terminating by one six-component measure:
--
--   (envLimit, noteFlag, visPars + slicePars, visWeight + sliceWeight,
--    layer, scan)
--
-- A user-environment expansion falls in `envLimit`; a frame's note drain
-- falls in `noteFlag` (its bodies come from the state, so no weight fact
-- covers them); the par-splice falls in the pars sum; every other edge
-- falls in the weight sum — a define moves its body's weight from the
-- slice into the visible sum and pays the group wrapper (`takeDefine`'s
-- facts), an expansion moves it back out (`visWeight_expand`). `layer`
-- orders spine (2) over dispatch arms (1) over loop members (0) where the
-- sums tie, and `scan` is a loop member's own index.

mutual

/-- Rule (b), judged once at the definition — the gate both registration
doors (the preamble fold and the body walk) run on a parsed definition
before pushing it into `ctx.user`. A redefinition of a rendered built-in
wins only if its body elaborates: the body is expanded here under the
definition's own visibility — `ctx.limit` is exactly the prefix a call
site will see — with each parameter bound to a probe word, so a body that
only echoes its argument is non-empty. A block-shaped body is judged by
the block walk, the same walk its use would take. The expansion's
diagnostics are inspected and discarded: the verdict is recorded at the
definition, never doubled at a use. A loss in {dropped, pending, degraded}
means the body renders less than the built-in it shadows; config and info
losses are harmless and do not refuse. -/
private def gateRedefB (ctx : Ctx) (cmd : UserCmd) : EM Bool := do
  if !renderedBuiltins.contains cmd.name then return true
  let saved ← get
  set { saved with diags := #[], warnedUnknown := #[] }
  let ⟨checkCtx, hm⟩ : MCtx ctx ← pure ⟨{ ctx with
    args := cmd.params.map fun p => (p.name, some #[Inline.text "x"]) },
    rfl, rfl, rfl, rfl⟩
  let nonEmpty ←
    if bodyIsBlock cmd.body then do
      have hp1 : slicePars cmd.body 0 ≤ rawParsList cmd.body.toList := by
        rw [slicePars_zero]; exact nestedParsList_le _
      have hw1 : sliceWeight cmd.body 0 = rawWeightList cmd.body.toList :=
        sliceWeight_zero _
      let bs ← elabBlocksGo checkCtx cmd.body 0 #[] #[] (← get).flowGen
      pure !bs.isEmpty
    else do
      let xs ← elabInlines checkCtx cmd.body
      pure !xs.isEmpty
  let checkDiags := (← get).diags
  set saved
  let lossy (d : Diag) : Bool :=
    match DiagCode.ofString? d.code with
    | some c => c.loss == .dropped || c.loss == .pending || c.loss == .degraded
    | none => false
  match checkDiags.find? lossy with
  | some d =>
    refuseRedef cmd (.refused d)
    if cmd.name == "maketitle" then
      modify fun st => { st with refusedTitleBody := some cmd.body }
    return false
  | none =>
    if nonEmpty then return true
    else
      refuseRedef cmd .empty
      if cmd.name == "maketitle" then
        modify fun st => { st with refusedTitleBody := some cmd.body }
      return false
termination_by (ctx.envLimit, noteFlag ctx,
  visParsGo ctx.user ctx.limit + rawParsList cmd.body.toList,
  visWeightGo ctx.user ctx.limit + rawWeightList cmd.body.toList + 1, 0, 0)
decreasing_by all_goals blocks_dec

/-- A frame's stashed notes, drained to its end: the side channel stays
with its frame. The bodies came from the state, not from any slice, so
this edge falls in the measure's note component alone: the drain runs at
`1`, between the walk that called it (`2`) and the note-body walks it
opens (`0`). -/
private def drainNotesGo (ctx : Ctx) (stash : List (Array Raw × Pos))
    (inner : Array Block) : EM (Array Block) := do
  match stash with
  | [] => return inner
  | (nb, npos) :: rest =>
    let ⟨noteCtx, _hnf⟩ : { c : Ctx // c.envLimit = ctx.envLimit
        ∧ noteFlag c = 0 } ←
      pure ⟨{ ctx with noteBody := true, notePos := some npos }, rfl, rfl⟩
    let nblocks ← elabBlocksGo noteCtx nb 0 #[] #[] (← get).flowGen
    drainNotesGo ctx rest (inner.push (.note nblocks))
termination_by (ctx.envLimit, 1, 0, 0, 0, stash.length)
decreasing_by all_goals blocks_dec

/-- One list item after another, each elaborated under its accumulated
`\pause` base and wrapped in its overlay step — the item elaboration half
of the split `itemSplitGo` carried the conservation facts for. -/
private def elabItemsGo (ctx : Ctx) (items : Array (Array Raw))
    (steps : Array (Option (Nat × Option Nat))) (itemPauses : Array Nat)
    (m : Nat) (acc : Array (Array Block)) (bound pbound : Nat)
    (hb : itemsW items.toList < bound) (hpb : itemsP items.toList ≤ pbound) :
    EM (Array (Array Block)) := do
  if hm : m < items.size then
    let ⟨it, hit, hitp⟩ : { a : Array Raw //
        rawWeightList a.toList ≤ itemsW items.toList
          ∧ nestedParsList a.toList ≤ itemsP items.toList } ←
      pure ⟨items[m], itemsW_elem_le (Array.getElem?_eq_getElem hm),
        itemsP_elem_le (Array.getElem?_eq_getElem hm)⟩
    let st? := (steps[m]?).getD none
    let p := (itemPauses[m]?).getD 0
    have hw1 : sliceWeight it 0 = rawWeightList it.toList := sliceWeight_zero _
    have hp1 : slicePars it 0 = nestedParsList it.toList := slicePars_zero _
    let ⟨stepCtx, hm2⟩ : MCtx ctx ←
      pure ⟨{ ctx with stepBase := ctx.stepBase + p }, rfl, rfl, rfl, rfl⟩
    let inner ← elabBlocksGo stepCtx it 0 #[] #[] (← get).flowGen
    let acc := acc.push (match st? with
      | some (s, last) => #[.step s last inner]
      | none =>
        if p > 0 then #[.step (ctx.stepBase + p + 1) none inner]
        else inner)
    elabItemsGo ctx items steps itemPauses (m + 1) acc bound pbound hb hpb
  else return acc
termination_by (ctx.envLimit, noteFlag ctx,
  visParsGo ctx.user ctx.limit + pbound,
  visWeightGo ctx.user ctx.limit + bound, 0, items.size + 1 - m)
decreasing_by all_goals blocks_dec

/-- A float body, one element at a time: `\caption` into the caption slot
(last one wins, W0311), `\centering` satisfied, an `\hfill` between
subfigures absorbed as the gutter, a `{subfigure}`/`{subtable}` child a
`.sub` float in a column of its declared width — and everything else
accumulated to elaborate in place. The invariant carries what the
accumulated run weighs; the base case flushes it and ships the float. -/
private def figureGo (ctx : Ctx) (n : String) (kind : Ir.FloatKind)
    (body : Array Raw) (pos : Pos) (j : Nat) (innerBlocks : Array Block)
    (cols : Array (Option Nat × Array Block)) (rest : Array Raw)
    (caption : Array Inline) (capAbove : Bool) (blocks : Array Block)
    (hw : rawWeightList rest.toList + sliceWeight body j
      ≤ rawWeightList body.toList)
    (hp : nestedParsList rest.toList + slicePars body j
      ≤ nestedParsList body.toList) :
    EM (Array Block) := do
  if h : j < body.size then
    match hj : body[j] with
    | .ctrl "caption" cpos =>
      let (⟨j2, hj2⟩, _, _) ← skipOptArg ctx "caption" body (j + 1) cpos
      let j3 := skipSpaces body j2
      have hj3 := skipSpaces_ge body j2
      have hwa : sliceWeight body j3 ≤ sliceWeight body j :=
        sliceWeight_le body (by omega)
      have hpa : slicePars body j3 ≤ slicePars body j :=
        slicePars_le body (by omega)
      match body[j3]? with
      | some (.group t _) =>
        unless caption.isEmpty do
          diag ctx .W0311 s!"this '\\caption' replaces the {n}'s earlier caption"
            (some cpos) (help := "the last one wins; remove the other '\\caption'")
        let caption ← elabInlines ctx t
        let capAbove := innerBlocks.isEmpty && cols.isEmpty
          && rest.all isSpaceOrPar
        figureGo ctx n kind body pos (j3 + 1) innerBlocks cols rest caption
          capAbove blocks
          (by have := sliceWeight_le body (show j3 ≤ j3 + 1 by omega); omega)
          (by have := slicePars_le body (show j3 ≤ j3 + 1 by omega); omega)
      | _ =>
        diag ctx .E0304 "'\\caption' needs a {text} group" cpos
        figureGo ctx n kind body pos j3 innerBlocks cols rest caption
          capAbove blocks (by omega) (by omega)
    | .ctrl "centering" _ =>
      -- The float centres already; the declaration is satisfied.
      figureGo ctx n kind body pos (j + 1) innerBlocks cols rest caption
        capAbove blocks
        (by have := sliceWeight_le body (show j ≤ j + 1 by omega); omega)
        (by have := slicePars_le body (show j ≤ j + 1 by omega); omega)
    | .ctrl "hfill" _ =>
      -- Between two subfigures the fill is the gutter, which the columns
      -- layout distributes by itself; anywhere else it is ordinary content.
      if !cols.isEmpty && rest.all isSpaceOrPar then
        figureGo ctx n kind body pos (j + 1) innerBlocks cols rest caption
          capAbove blocks
          (by have := sliceWeight_le body (show j ≤ j + 1 by omega); omega)
          (by have := slicePars_le body (show j ≤ j + 1 by omega); omega)
      else
        figureGo ctx n kind body pos (j + 1) innerBlocks cols
          (rest.push body[j]) caption capAbove blocks
          (by
            have h1 := sliceWeight_here body h
            rw [rawWeightList_push]; omega)
          (by
            have h1 := slicePars_here body h
            have h2 := rawPars_split body[j]
            rw [nestedParsList_push]; omega)
    | .env sn sbody spos =>
      if sn == "subfigure" || sn == "subtable" then do
        have hbe : body[j]? = some (.env sn sbody spos) := by
          rw [Array.getElem?_eq_getElem h]; exact congrArg some hj
        have hew := elem_weight_le hbe (Nat.le_refl j)
        have hep := elem_pars_le hbe (Nat.le_refl j)
        have hew' : rawWeightList sbody.toList + 1 ≤ sliceWeight body j := by
          simp only [rawWeight] at hew; omega
        have hep' : rawParsList sbody.toList ≤ slicePars body j := by
          simp only [nestedPars] at hep; omega
        let (innerBlocks, cols) ←
          if rest.any (!isSpaceOrPar ·) then do
            let innerBlocks :=
              if cols.isEmpty then innerBlocks
              else innerBlocks.push (.columns cols)
            have hr0 : sliceWeight rest 0 = rawWeightList rest.toList :=
              sliceWeight_zero _
            have hr1 : slicePars rest 0 = nestedParsList rest.toList :=
              slicePars_zero _
            let rb ← elabBlocksGo ctx rest 0 #[] #[] (← get).flowGen
            pure (innerBlocks ++ rb, (#[] : Array (Option Nat × Array Block)))
          else pure (innerBlocks, cols)
        -- The minipage shape: `[pos]` baseline options are noted and
        -- ignored (the box stands top-aligned in its row), the `{width}`
        -- group is a fraction of the measure, exactly as a column's.
        let mut m := 0
        for _ in [0:3] do
          match scanBracketArg sbody m spos with
          | .took m' =>
            warnOnce ctx "subfigure:options" .N0102
              s!"'\{{sn}}' [pos] options are ignored: the box \
stands top-aligned in its row" spos
            m := m'
          | .unclosed bpos =>
            warnUnclosed ctx s!"'\\begin\{{sn}}'" bpos
            break
          | .content => break
        m := skipSpaces sbody m
        let mut width : Option Nat := none
        if let some (.group wRaws _) := sbody[m]? then
          m := m + 1
          let src := rawSrc wRaws
          width := columnWidth ctx src
          if width.isNone then
            warnOnce ctx "env:subfigure-width" .W0314
              s!"'\{{sn}}' width '{src}' is not a fraction of the \
text width; the box shares the leftover" spos
              (help := "write a factor like {0.48\\textwidth}")
        else
          diag ctx .E0304 s!"'\\begin\{{sn}}' needs a \{width} group" spos
        let (sCaption, sCapAbove, ⟨sRest, hsr⟩) ← subRestGo ctx sn sbody m
          #[] false #[] (sliceWeight sbody m) (slicePars sbody m)
          (by simp [rawWeightList]) (by simp [nestedParsList])
        have hsw : rawWeightList sRest.toList ≤ sliceWeight sbody m := hsr.1
        have hsp : nestedParsList sRest.toList ≤ slicePars sbody m := hsr.2
        have hsw2 : sliceWeight sbody m ≤ rawWeightList sbody.toList := by
          have := sliceWeight_le sbody (Nat.zero_le m)
          rw [sliceWeight_zero] at this; omega
        have hsp2 : slicePars sbody m ≤ nestedParsList sbody.toList := by
          have := slicePars_le sbody (Nat.zero_le m)
          rw [slicePars_zero] at this; omega
        have hsp3 := nestedParsList_le sbody.toList
        have hs0 : sliceWeight sRest 0 = rawWeightList sRest.toList :=
          sliceWeight_zero _
        have hs1 : slicePars sRest 0 = nestedParsList sRest.toList :=
          slicePars_zero _
        let mut sInner ← elabBlocksGo ctx sRest 0 #[] #[] (← get).flowGen
        unless sCaption.isEmpty do
          sInner := Ir.setAltBlocks (Ir.plainText sCaption) sInner
        figureGo ctx n kind body pos (j + 1) innerBlocks
          (cols.push (width, #[.float .sub none sCapAbove sInner sCaption]))
          #[] caption capAbove blocks
          (by
            have := sliceWeight_le body (show j ≤ j + 1 by omega)
            simp [rawWeightList]; omega)
          (by
            have := slicePars_le body (show j ≤ j + 1 by omega)
            simp [nestedParsList]; omega)
      else
        figureGo ctx n kind body pos (j + 1) innerBlocks cols
          (rest.push body[j]) caption capAbove blocks
          (by
            have h1 := sliceWeight_here body h
            rw [rawWeightList_push]; omega)
          (by
            have h1 := slicePars_here body h
            have h2 := rawPars_split body[j]
            rw [nestedParsList_push]; omega)
    | _ =>
      figureGo ctx n kind body pos (j + 1) innerBlocks cols
        (rest.push body[j]) caption capAbove blocks
        (by
          have h1 := sliceWeight_here body h
          rw [rawWeightList_push]; omega)
        (by
          have h1 := slicePars_here body h
          have h2 := rawPars_split body[j]
          rw [nestedParsList_push]; omega)
  else do
    let innerBlocks :=
      if cols.isEmpty then innerBlocks else innerBlocks.push (.columns cols)
    have hr0 : sliceWeight rest 0 = rawWeightList rest.toList :=
      sliceWeight_zero _
    have hr1 : slicePars rest 0 = nestedParsList rest.toList :=
      slicePars_zero _
    let rb ← elabBlocksGo ctx rest 0 #[] #[] (← get).flowGen
    let mut inner := innerBlocks ++ rb
    unless caption.isEmpty do
      inner := Ir.setAltBlocks (Ir.plainText caption) inner
    return blocks.push (.float kind none capAbove inner caption)
termination_by (ctx.envLimit, noteFlag ctx,
  visParsGo ctx.user ctx.limit + nestedParsList body.toList,
  visWeightGo ctx.user ctx.limit + rawWeightList body.toList + 1, 0,
  body.size + 1 - j)
decreasing_by all_goals blocks_dec

/-- The `{columns}` body: each `{column}` child a column of its declared
width, consecutive ones one `.columns` row, content standing outside any
column kept in place as ordinary blocks — never dropped. -/
private def columnsGo (ctx : Ctx) (body : Array Raw) (j : Nat)
    (cols : Array (Option Nat × Array Block)) (strayRaws : Array Raw)
    (blocks : Array Block)
    (hw : rawWeightList strayRaws.toList + sliceWeight body j
      ≤ rawWeightList body.toList)
    (hp : nestedParsList strayRaws.toList + slicePars body j
      ≤ nestedParsList body.toList) :
    EM (Array Block) := do
  if h : j < body.size then
    match hj : body[j] with
    | .env "column" cbody cpos =>
      have hbe : body[j]? = some (.env "column" cbody cpos) := by
        rw [Array.getElem?_eq_getElem h]; exact congrArg some hj
      have hew := elem_weight_le hbe (Nat.le_refl j)
      have hep := elem_pars_le hbe (Nat.le_refl j)
      have hew' : rawWeightList cbody.toList + 1 ≤ sliceWeight body j := by
        simp only [rawWeight] at hew; omega
      have hep' : rawParsList cbody.toList ≤ slicePars body j := by
        simp only [nestedPars] at hep; omega
      let (cols, blocks) ←
        if strayRaws.any (!isSpaceOrPar ·) then do
          let blocks := if cols.isEmpty then blocks
            else blocks.push (.columns cols)
          have hs0 : sliceWeight strayRaws 0
              = rawWeightList strayRaws.toList := sliceWeight_zero _
          have hs1 : slicePars strayRaws 0
              = nestedParsList strayRaws.toList := slicePars_zero _
          let sb ← elabBlocksGo ctx strayRaws 0 #[] #[] (← get).flowGen
          pure ((#[] : Array (Option Nat × Array Block)), blocks ++ sb)
        else pure (cols, blocks)
      let m := skipSpaces cbody 0
      let mut width : Option Nat := none
      let mut m2 := m
      if let some (.group wRaws _) := cbody[m]? then
        m2 := m + 1
        let src := rawSrc wRaws
        width := columnWidth ctx src
        if width.isNone then
          warnOnce ctx "env:column-width" .W0314
            s!"column width '{src}' is not a fraction of the text width; \
the column shares the leftover" cpos
            (help := "write a factor like {0.5\\textwidth}")
      have hce : rawWeightList (cbody.extract m2 cbody.size).toList
          ≤ rawWeightList cbody.toList := extract_weight_le ..
      have hcp : nestedParsList (cbody.extract m2 cbody.size).toList
          ≤ nestedParsList cbody.toList := extract_nested_le ..
      have hcp2 := nestedParsList_le cbody.toList
      have hc0 : sliceWeight (cbody.extract m2 cbody.size) 0
          = rawWeightList (cbody.extract m2 cbody.size).toList :=
        sliceWeight_zero _
      have hc1 : slicePars (cbody.extract m2 cbody.size) 0
          = nestedParsList (cbody.extract m2 cbody.size).toList :=
        slicePars_zero _
      let cinner ← elabBlocksGo ctx (cbody.extract m2 cbody.size) 0 #[] #[]
        (← get).flowGen
      columnsGo ctx body (j + 1) (cols.push (width, cinner)) #[] blocks
        (by
          have := sliceWeight_le body (show j ≤ j + 1 by omega)
          simp [rawWeightList]; omega)
        (by
          have := slicePars_le body (show j ≤ j + 1 by omega)
          simp [nestedParsList]; omega)
    | _ =>
      columnsGo ctx body (j + 1) cols (strayRaws.push body[j]) blocks
        (by
          have h1 := sliceWeight_here body h
          rw [rawWeightList_push]; omega)
        (by
          have h1 := slicePars_here body h
          have h2 := rawPars_split body[j]
          rw [nestedParsList_push]; omega)
  else do
    let blocks := if cols.isEmpty then blocks else blocks.push (.columns cols)
    if strayRaws.any (!isSpaceOrPar ·) then
      have hs0 : sliceWeight strayRaws 0 = rawWeightList strayRaws.toList :=
        sliceWeight_zero _
      have hs1 : slicePars strayRaws 0 = nestedParsList strayRaws.toList :=
        slicePars_zero _
      let sb ← elabBlocksGo ctx strayRaws 0 #[] #[] (← get).flowGen
      return blocks ++ sb
    else
      return blocks
termination_by (ctx.envLimit, noteFlag ctx,
  visParsGo ctx.user ctx.limit + nestedParsList body.toList,
  visWeightGo ctx.user ctx.limit + rawWeightList body.toList + 1, 0,
  body.size + 1 - j)
decreasing_by all_goals blocks_dec

/-- One environment at block level: the whole `.env` dispatch, from display
math through tables, frames, lists, floats and columns to defined wrappers
and the unknown-wrapper splice. The caller consumed the environment
itself; every recursion here descends into its body, so the weight sum
falls by at least the wrapper. -/
private def elabEnvArm (ctx : Ctx) (n : String) (body : Array Raw)
    (pos : Pos) (blocks : Array Block) : EM (Array Block) := do
  have hb0 : sliceWeight body 0 = rawWeightList body.toList := sliceWeight_zero _
  have hb1 : slicePars body 0 = nestedParsList body.toList := slicePars_zero _
  have hb2 := nestedParsList_le body.toList
  let mut blocks := blocks
  if let some f := Parse.inputEnvFile? n then
    -- An \input file's blocks, elaborated under its own name so a
    -- diagnostic points at the file that holds the construct.
    let ⟨fileCtx, hm⟩ : MCtx ctx ←
      pure ⟨{ ctx with file := f }, rfl, rfl, rfl, rfl⟩
    blocks := blocks ++ (← elabBlocksGo fileCtx body 0 #[] #[] (← get).flowGen)
  else if let some numbered := displayMathEnvs.lookup n then
    blocks ← displayMathArm ctx numbered body pos blocks
  else if let some (kind, numbered) := alignEnvs.lookup n then
    blocks ← alignEnvArm ctx n kind numbered body pos blocks
  else if n == "tabular" || n == "tabular*" then
    blocks ← tabularArm ctx n body pos blocks
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
    let (title2, ⟨rest, hrf⟩) ← frameRestGo ctx body k title #[]
      (sliceWeight body k) (slicePars body k)
      (by simp [rawWeightList]) (by simp [nestedParsList])
    title := title2
    have hrw : rawWeightList rest.toList ≤ sliceWeight body k := hrf.1
    have hrp : nestedParsList rest.toList ≤ slicePars body k := hrf.2
    have hrw2 : sliceWeight body k ≤ rawWeightList body.toList := by
      have := sliceWeight_le body (Nat.zero_le k); omega
    have hrp2 : slicePars body k ≤ nestedParsList body.toList := by
      have := slicePars_le body (Nat.zero_le k); omega
    have hr0 : sliceWeight rest 0 = rawWeightList rest.toList := sliceWeight_zero _
    have hr1 : slicePars rest 0 = nestedParsList rest.toList := slicePars_zero _
    -- Notes met inside the frame's inline content drain to the
    -- frame's end: the side channel stays with its frame. Inside a
    -- note's own body there is no side channel to drain into — a
    -- note is not slide content, so its frame cannot carry one —
    -- and the stashed notes are refused, named at the note that
    -- encloses them (E0359; the noteFlag decision, PLAN).
    modify fun st => { st with pendingNotes := #[] }
    let mut inner ← elabBlocksGo ctx rest 0 #[] #[] (← get).flowGen
    let stash := (← get).pendingNotes
    modify fun st => { st with pendingNotes := #[] }
    if hnb : ctx.noteBody then
      unless stash.isEmpty do
        diag ctx .E0359
          "a '\\note' inside this note's frame is dropped: one note cannot carry another"
          ctx.notePos
          (help := "move the inner '\\note' out of the enclosing '\\note', beside its frame")
    else
      have hnf : noteFlag ctx = 2 := by simp [noteFlag, hnb]
      inner ← drainNotesGo ctx stash.toList inner
    blocks := blocks.push (.frame title standout valign inner)
  else if n == "itemize" || n == "enumerate" then
    -- enumitem's per-instance `[keys]` are consumed and named: the
    -- engine styles lists per element, not per instance, and the
    -- old path let the bracket land as content before the first
    -- \item — a false E0310 error from a documented interface.
    let mut bodyFrom := 0
    match scanBracketArg body 0 pos with
    | .took k' =>
      warnOnce ctx ("env:" ++ n ++ ":opts") .N0102
        s!"'\{{n}}' [options] are not modelled per instance; the declared list style stands"
        pos
      bodyFrom := k'
    | .unclosed bpos =>
      warnUnclosed ctx s!"'\\begin\{{n}}'" bpos
    | .content => pure ()
    let ⟨lbody, hlw, hlp⟩ : { a : Array Raw //
        rawWeightList a.toList ≤ rawWeightList body.toList
          ∧ nestedParsList a.toList ≤ nestedParsList body.toList } ←
      pure ⟨body.extract bodyFrom body.size, extract_weight_le ..,
        extract_nested_le ..⟩
    -- `\pause` between items steps the rest of the LIST, not just
    -- the rest of an item's own blocks: each item records how many
    -- pauses stand before it and reveals one step after the last.
    let ⟨(items, steps, itemPauses), hsplit⟩ ← itemSplitGo ctx lbody pos 0
      #[] #[] #[] 0 #[] none 0 false false false false
      (sliceWeight lbody 0) (slicePars lbody 0)
      (by simp [itemsW, rawWeightList]) (by simp [itemsP, nestedParsList])
    have hiw : itemsW items.toList ≤ sliceWeight lbody 0 := hsplit.1
    have hip : itemsP items.toList ≤ slicePars lbody 0 := hsplit.2
    have hl0 : sliceWeight lbody 0 = rawWeightList lbody.toList :=
      sliceWeight_zero _
    have hl1 : slicePars lbody 0 = nestedParsList lbody.toList :=
      slicePars_zero _
    let elabItems ← elabItemsGo ctx items steps itemPauses 0 #[]
      (rawWeightList lbody.toList + 1) (nestedParsList lbody.toList)
      (by omega) (by omega)
    blocks := blocks.push (.list (n == "enumerate") elabItems)
  else if n == "center" then
    blocks := blocks.push (.center
      (← elabBlocksGo ctx body 0 #[] #[] (← get).flowGen))
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
      width := columnWidth ctx src
      if width.isNone then
        warnOnce ctx "env:minipage-width" .W0314
          s!"minipage width '{src}' is not a fraction of the text width; \
the box takes the whole measure" pos
          (help := "write a factor like {0.5\\textwidth}")
    else
      diag ctx .E0304 "'\\begin{minipage}' needs a {width} group" pos
    have hxw : rawWeightList (body.extract m2 body.size).toList
        ≤ rawWeightList body.toList := extract_weight_le ..
    have hxp : nestedParsList (body.extract m2 body.size).toList
        ≤ nestedParsList body.toList := extract_nested_le ..
    have hx0 : sliceWeight (body.extract m2 body.size) 0
        = rawWeightList (body.extract m2 body.size).toList := sliceWeight_zero _
    have hx1 : slicePars (body.extract m2 body.size) 0
        = nestedParsList (body.extract m2 body.size).toList := slicePars_zero _
    blocks := blocks.push
      (.columns #[(width, ← elabBlocksGo ctx (body.extract m2 body.size) 0
        #[] #[] (← get).flowGen)])
  else if n == "block" || n == "alertblock" || n == "exampleblock" then
    -- beamer's titled blocks (user guide §12.3): the {title} group on
    -- the `\begin` line is the title — beamer's own mandatory argument,
    -- so an empty group is the documented untitled block (no title bar)
    -- and a missing group is named (E0304). A paragraph break before a
    -- group makes it content, as the frame's title rule reads it.
    let kind : Ir.TitledKind :=
      if n == "alertblock" then .alert
      else if n == "exampleblock" then .example
      else .block
    let k := skipSpaces body 0
    let mut title : Array Inline := #[]
    let mut m := 0
    match body[k]? with
    | some (.group t _) =>
      title ← elabInlines ctx t
      m := k + 1
    | _ =>
      diag ctx .E0304 s!"'\\begin\{{n}}' needs a \{title} group" pos
        (help := "an empty group is an untitled block")
    have hxw : rawWeightList (body.extract m body.size).toList
        ≤ rawWeightList body.toList := extract_weight_le ..
    have hxp : nestedParsList (body.extract m body.size).toList
        ≤ nestedParsList body.toList := extract_nested_le ..
    have hx0 : sliceWeight (body.extract m body.size) 0
        = rawWeightList (body.extract m body.size).toList := sliceWeight_zero _
    have hx1 : slicePars (body.extract m body.size) 0
        = nestedParsList (body.extract m body.size).toList := slicePars_zero _
    blocks := blocks.push (.titled kind title
      (← elabBlocksGo ctx (body.extract m body.size) 0 #[] #[] (← get).flowGen))
  else if n == "quote" || n == "quotation" then
    -- One node for both: they differ only in \listparindent
    -- (quotation indents each paragraph's first line), and the
    -- engine sets no paragraph indent anywhere yet — see the
    -- constructor's docstring.
    blocks := blocks.push (.quote
      (← elabBlocksGo ctx body 0 #[] #[] (← get).flowGen))
  else if n == "abstract" then
    -- article's unnumbered titled block: quotation-shaped with a
    -- centred heading in the PDF, a <section> with a heading in
    -- HTML — see the constructor's docstring for the split.
    blocks := blocks.push (.abstract
      (← elabBlocksGo ctx body 0 #[] #[] (← get).flowGen))
  else if n == "figure" || n == "figure*" || n == "table" || n == "table*" then
    -- A single-pass engine has nowhere for a float to float: the
    -- float stands where written as a `.float`, `[placement]`
    -- ignored with a note saying so. Its caption keeps its source
    -- side — before the content it stands above, the table
    -- convention — and becomes the alt text of the images it
    -- captions; `numberFloats` assigns the number afterwards.
    -- A `{subfigure}`/`{subtable}` child (subcaption §2: a
    -- minipage-shaped box with its own caption, lettered under the
    -- parent's number) is a `.sub` float in a column of its
    -- declared width; consecutive ones share one `.columns` row so
    -- they stand side by side, and an `\hfill` between them is the
    -- gutter the columns layout already distributes.
    let kind : Ir.FloatKind :=
      if n == "table" || n == "table*" then .table else .figure
    -- A float's alignment grouping is transparent (`spliceCenterGo`): a
    -- `center` child is spliced before the walk, so its `\caption` and
    -- `\label` are the float's own.
    let ⟨fbody, hfw, hfp⟩ ← pure (spliceCenterGo body.toList #[]
      (rawWeightList body.toList) (nestedParsList body.toList)
      (by simp [rawWeightList]) (by simp [nestedParsList]))
    let mut k := 0
    for _ in [0:fbody.size] do
      match scanBracketArg fbody k pos with
      | .took k' =>
        warnOnce ctx "figure:placement" .N0102
          s!"'\{{n}}' [placement] is ignored: a single-pass engine \
has nowhere for a float to float" pos
        k := k'
      | .unclosed bpos =>
        warnUnclosed ctx s!"'\\begin\{{n}}'" bpos
        break
      | .content => break
    have hf0 : sliceWeight fbody 0 = rawWeightList fbody.toList :=
      sliceWeight_zero _
    have hf1 : slicePars fbody 0 = nestedParsList fbody.toList :=
      slicePars_zero _
    have hkw : sliceWeight fbody k ≤ rawWeightList fbody.toList := by
      have := sliceWeight_le fbody (Nat.zero_le k); omega
    have hkp : slicePars fbody k ≤ nestedParsList fbody.toList := by
      have := slicePars_le fbody (Nat.zero_le k); omega
    blocks ← figureGo ctx n kind fbody pos k #[] #[] #[] #[] false blocks
      (by simp [rawWeightList]; omega) (by simp [nestedParsList]; omega)
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
    have hkw : sliceWeight body k ≤ rawWeightList body.toList := by
      have := sliceWeight_le body (Nat.zero_le k); omega
    have hkp : slicePars body k ≤ nestedParsList body.toList := by
      have := slicePars_le body (Nat.zero_le k); omega
    blocks ← columnsGo ctx body k #[] #[] blocks
      (by simp [rawWeightList]; omega) (by simp [nestedParsList]; omega)
  else if n == "ifbackend" then
    -- `{ifbackend}{html,md}`: block content addressed to a subset
    -- of the backends. An unknown name is dropped from the set with
    -- W0323; a set that keeps no backend along its nesting path is
    -- E0334 — content nothing will emit. The body still elaborates
    -- and the node still carries it (the IR reflects the document);
    -- `Ir.keepFor` at each backend's entry is the one drop site,
    -- and `Ir.keepFor_covers` is why the diagnostic is sufficient.
    let j ← pure (skipSpaces body 0)
    match body[j]? with
    | some (.group g gpos) =>
      -- A backend conditional writes a per-medium decision by hand
      -- in content — the decision a construct or the class should
      -- carry (a nav becomes the print outline by itself, a note
      -- leaves the handout). Named where it stands, as a note: the
      -- escape hatch remains for the genuine remainder.
      diag ctx .N0019
        "content addressed per backend encodes a per-medium decision by hand" pos
        (help := "a construct carries its own medium answer (a nav, a note); \
prefer the construct or the class, and keep '\\begin{ifbackend}' for the true remainder")
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
      let ⟨backCtx, hm⟩ : MCtx ctx ←
        pure ⟨{ ctx with backendTargets := eff }, rfl, rfl, rfl, rfl⟩
      have hxw : rawWeightList (body.extract (j + 1) body.size).toList
          ≤ rawWeightList body.toList := extract_weight_le ..
      have hxp : nestedParsList (body.extract (j + 1) body.size).toList
          ≤ nestedParsList body.toList := extract_nested_le ..
      have hx0 : sliceWeight (body.extract (j + 1) body.size) 0
          = rawWeightList (body.extract (j + 1) body.size).toList :=
        sliceWeight_zero _
      have hx1 : slicePars (body.extract (j + 1) body.size) 0
          = nestedParsList (body.extract (j + 1) body.size).toList :=
        slicePars_zero _
      let inner ← elabBlocksGo backCtx (body.extract (j + 1) body.size) 0
        #[] #[] (← get).flowGen
      blocks := blocks.push (.only targets inner)
    | _ =>
      diag ctx .E0304 "'\\begin{ifbackend}' needs a {backends} group" pos
        (help := "write \\begin{ifbackend}{html} ... \\end{ifbackend}")
      blocks := blocks ++ (← elabBlocksGo ctx body 0 #[] #[] (← get).flowGen)
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
    match scanBracketArg body 0 pos with
    | .took k =>
      let j0 := skipSpaces body 0
      let inner := rawSrc (body.extract (j0 + 1) (k - 1))
      let spec ← navSpecOf ctx inner pos
      have hxw : rawWeightList (body.extract k body.size).toList
          ≤ rawWeightList body.toList := extract_weight_le ..
      have hxp : nestedParsList (body.extract k body.size).toList
          ≤ nestedParsList body.toList := extract_nested_le ..
      have hx0 : sliceWeight (body.extract k body.size) 0
          = rawWeightList (body.extract k body.size).toList := sliceWeight_zero _
      have hx1 : slicePars (body.extract k body.size) 0
          = nestedParsList (body.extract k body.size).toList := slicePars_zero _
      blocks := blocks.push (.nav spec (← elabBlocksGo ctx
        (body.extract k body.size) 0 #[] #[] (← get).flowGen))
    | _ =>
      blocks := blocks.push (.nav {}
        (← elabBlocksGo ctx body 0 #[] #[] (← get).flowGen))
  else if hle : (lookupUserEnv ctx n).isSome then
    -- A defined wrapper at block level: the halves and the content
    -- each contribute their blocks, in order. An inline half becomes
    -- its own paragraph beside block content — the splice that would
    -- merge them re-elaborates raws under two argument scopes.
    let ke := (lookupUserEnv ctx n).get hle
    have hle2 : lookupUserEnv ctx n = some ke := (Option.some_get hle).symm
    have hk : ke.1 < ctx.envLimit := lookupUserEnv_lt hle2
    let env := ke.2
    let (bindings, j) ← takeArgs ctx env.params n body 0 pos
    let ⟨envCtx, hke⟩ : { c : Ctx // c.envLimit = ke.1 } ←
      pure ⟨{ ctx with
        limit := env.cmdLimit, envLimit := ke.1, args := bindings }, rfl⟩
    blocks := blocks ++ (← elabBlocksGo envCtx env.beginBody 0 #[] #[]
      (← get).flowGen)
    have hxw : rawWeightList (body.extract j body.size).toList
        ≤ rawWeightList body.toList := extract_weight_le ..
    have hxp : nestedParsList (body.extract j body.size).toList
        ≤ nestedParsList body.toList := extract_nested_le ..
    have hx0 : sliceWeight (body.extract j body.size) 0
        = rawWeightList (body.extract j body.size).toList := sliceWeight_zero _
    have hx1 : slicePars (body.extract j body.size) 0
        = nestedParsList (body.extract j body.size).toList := slicePars_zero _
    blocks := blocks ++ (← elabBlocksGo ctx (body.extract j body.size) 0
      #[] #[] (← get).flowGen)
    blocks := blocks ++ (← elabBlocksGo envCtx env.endBody 0 #[] #[]
      (← get).flowGen)
  else if n == "tikzpicture" then
    blocks ← tikzArm ctx body pos blocks
  else if reservedEnv.contains n then
    warnOnce ctx ("env:" ++ n) .W0307
      s!"'\{{n}}' is not implemented yet; its content is not rendered" pos
  else
    -- An unknown wrapper's decoration is unknowable; its body is
    -- not. The arguments on the `\begin` line go with the wrapper.
    warnOnce ctx ("env:" ++ n) .W0302 s!"unknown environment '\{{n}}'; its body is kept" pos
      (help := "\\defineenv{name}(...) {begin} {end} declares one")
    let (keptFrom, unclosed, dropped) := dropEnvArgs body pos
    let ⟨kept, hxw, hxp⟩ : { a : Array Raw //
        rawWeightList a.toList ≤ rawWeightList body.toList
          ∧ nestedParsList a.toList ≤ nestedParsList body.toList } ←
      pure ⟨body.extract keptFrom body.size, extract_weight_le ..,
        extract_nested_le ..⟩
    if let some bpos := unclosed then
      warnUnclosed ctx s!"'\\begin\{{n}}'" bpos
    warnDroppedArgs ctx n dropped pos
    have hx0 : sliceWeight kept 0 = rawWeightList kept.toList := sliceWeight_zero _
    have hx1 : slicePars kept 0 = nestedParsList kept.toList := slicePars_zero _
    blocks := blocks ++ (← elabBlocksGo ctx kept 0 #[] #[] (← get).flowGen)
  return blocks
termination_by (ctx.envLimit, noteFlag ctx,
  visParsGo ctx.user ctx.limit + rawParsList body.toList,
  visWeightGo ctx.user ctx.limit + 1 + rawWeightList body.toList, 1, 0)
decreasing_by all_goals blocks_dec

/-- One general control word at block level, standing at `i`: native
declarations misplaced in the body, user-command expansion, block-level
overlays, title declarations, `\logo`, `\maketitle`, and the section
headings. Returns the walk's next index with its progress fact — every
path consumes at least the control word itself. -/
private def elabCtrlArm (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (h : i < raws.size) (n : String) (pos : Pos) (blocks : Array Block) :
    EM (Array Block × { j : Nat // i < j }) := do
  have hslw : sliceWeight raws (i + 1) < sliceWeight raws i :=
    sliceWeight_lt raws h (by omega)
  have hslp : slicePars raws (i + 1) ≤ slicePars raws i :=
    slicePars_le raws (by omega)
  let mut blocks := blocks
  if declCtrl.contains n then
    -- A native declaration met in the body is never "unknown": it
    -- is ours, misplaced. `\palette` and `\tokens` have arms above;
    -- the rest configure the whole document and are read only in
    -- the preamble, so the declaration is skipped with its block,
    -- named as what it is.
    warnOnce ctx ("ctrl:" ++ n) .W0340
      s!"'\\{n}' is a declaration; in the body it is ignored" pos
      (help := "declare it in the preamble, before '\\begin{document}'")
    let ju := skipReservedArgs raws (i + 1) pos (maxGroups := 2)
    have hj : i + 1 ≤ ju.1 := skipReservedArgs_ge raws (i + 1) pos 2
    if let some bpos := ju.2 then
      warnUnclosed ctx s!"'\\{n}'" bpos
    return (blocks, ⟨ju.1, by omega⟩)
  else if runningCtrl.contains n then
    -- Running head/foot in the body: ours, misplaced — never
    -- "unknown". The declaration carries content, so skipping it
    -- drops that content: an error, not a config warning.
    diag ctx .E0347 s!"'\\{n}' in the body is dropped with its content" pos
      (help := "declare it in the preamble, before '\\begin{document}'")
    let ju := skipReservedArgs raws (i + 1) pos
    have hj : i + 1 ≤ ju.1 := skipReservedArgs_ge raws (i + 1) pos 1
    if let some bpos := ju.2 then
      warnUnclosed ctx s!"'\\{n}'" bpos
    return (blocks, ⟨ju.1, by omega⟩)
  else
  match hlk : lookupUser ctx n with
  | some (k, cmd) =>
    -- Block-producing user command: bind its arguments, then
    -- elaborate the body as blocks so `\block` inside a definition
    -- works instead of reporting E0312. A parameterized command's
    -- expansion wraps in its name, as at the inline splice: the
    -- role survives at whichever level its content lives.
    let (bindings, ⟨j, hj⟩) ← takeArgsFrom ctx cmd.params 0 n raws (i + 1)
      pos #[]
    let ⟨callCtx, hm1, hm2, hvp, hvw⟩ : { c : Ctx // c.envLimit = ctx.envLimit
        ∧ noteFlag c = noteFlag ctx
        ∧ visParsGo c.user c.limit = visParsGo ctx.user k
        ∧ visWeightGo c.user c.limit = visWeightGo ctx.user k } ←
      pure ⟨{ ctx with limit := k, args := bindings }, rfl, rfl, rfl, rfl⟩
    have hpe := visPars_expand hlk
    have hwe := visWeight_expand hlk
    have hp1 : slicePars cmd.body 0 ≤ rawParsList cmd.body.toList := by
      rw [slicePars_zero]; exact nestedParsList_le _
    have hw1 : sliceWeight cmd.body 0 = rawWeightList cmd.body.toList :=
      sliceWeight_zero _
    have hpos : 0 < sliceWeight raws i := by
      have := sliceWeight_here raws h
      have := rawWeight_pos raws[i]
      omega
    let expanded ← elabBlocksGo callCtx cmd.body 0 #[] #[] (← get).flowGen
    if cmd.params.isEmpty then
      blocks := blocks ++ expanded
    else
      blocks := blocks.push (.role cmd.name expanded)
    return (blocks, ⟨j, by omega⟩)
  | none =>
  if overlayCtrls.contains n || n == "alt" then
    -- Block-level overlay: the step wrapper survives at block
    -- level, so a list or a multi-paragraph group inside
    -- \onslide<2->{...} steps whole — elaborated as blocks, never
    -- squeezed through a paragraph. A spec the model cannot number
    -- keeps the honest W0105 and the content stays shown. `\pause`
    -- inside the wrapped content counts from the wrapper's own
    -- step, so pending stays pending.
    let j := skipSpaces raws (i + 1)
    have hjge : i + 1 ≤ j := skipSpaces_ge raws (i + 1)
    let ⟨(spec, jg), hjg⟩ :
        { t : Option (Nat × Option Nat) × Nat // i + 1 ≤ t.2 } ←
      match raws[j]?.bind specWord? with
      | some w => do
        let jg := skipSpaces raws (j + 1)
        have h2 : i + 1 ≤ jg := by
          have := skipSpaces_ge raws (j + 1); omega
        match overlayFrom w with
        | some p => pure ⟨(some p, jg), h2⟩
        | none => do
          warnOnce ctx "spec:overlay" .W0105
            s!"overlay specification '{w}' does not name a step; its \
content is shown on every step" pos
            (help := "write a numbered spec: <2>, <2->, or <2-3>; incremental \
specs are not modelled")
          pure ⟨(none, jg), h2⟩
      | none => pure ⟨(none, j), hjge⟩
    have hjg2 : i + 1 ≤ jg := hjg
    if n == "alt" then
      let j3 := skipSpaces raws (jg + 1)
      have hj3 := skipSpaces_ge raws (jg + 1)
      match hga : raws[jg]?, hgb : raws[j3]? with
      | some (.group ga _), some (.group gb _) =>
        have hgaw : rawWeightList ga.toList + 1 ≤ sliceWeight raws jg := by
          have := elem_weight_le hga (Nat.le_refl jg)
          simp only [rawWeight] at this; omega
        have hgap : nestedParsList ga.toList ≤ slicePars raws jg := by
          have := elem_pars_le hga (Nat.le_refl jg)
          simp only [nestedPars] at this
          have := nestedParsList_le ga.toList; omega
        have hgbw : rawWeightList gb.toList + 1 ≤ sliceWeight raws j3 := by
          have := elem_weight_le hgb (Nat.le_refl j3)
          simp only [rawWeight] at this; omega
        have hgbp : nestedParsList gb.toList ≤ slicePars raws j3 := by
          have := elem_pars_le hgb (Nat.le_refl j3)
          simp only [nestedPars] at this
          have := nestedParsList_le gb.toList; omega
        have hga2 : sliceWeight raws jg ≤ sliceWeight raws i := by
          have := sliceWeight_le raws (show i ≤ jg by omega); omega
        have hgb2 : sliceWeight raws j3 ≤ sliceWeight raws i := by
          have := sliceWeight_le raws (show i ≤ j3 by omega); omega
        have hga3 : slicePars raws jg ≤ slicePars raws i := by
          have := slicePars_le raws (show i ≤ jg by omega); omega
        have hgb3 : slicePars raws j3 ≤ slicePars raws i := by
          have := slicePars_le raws (show i ≤ j3 by omega); omega
        have h0a : sliceWeight ga 0 = rawWeightList ga.toList := sliceWeight_zero _
        have h1a : slicePars ga 0 = nestedParsList ga.toList := slicePars_zero _
        have h0b : sliceWeight gb 0 = rawWeightList gb.toList := sliceWeight_zero _
        have h1b : slicePars gb 0 = nestedParsList gb.toList := slicePars_zero _
        match spec with
        | some (s, last) =>
          let ⟨stepCtx, hm⟩ : MCtx ctx ←
            pure ⟨{ ctx with stepBase := max ctx.stepBase (s - 1) },
              rfl, rfl, rfl, rfl⟩
          let ia ← elabBlocksGo stepCtx ga 0 #[] #[] (← get).flowGen
          let ib ← elabBlocksGo ctx gb 0 #[] #[] (← get).flowGen
          blocks := blocks.push (.step s last ia)
          blocks := blocks.push (.step 1 (some (s - 1)) ib)
          return (blocks, ⟨j3 + 1, by omega⟩)
        | none =>
          blocks := blocks ++ (← elabBlocksGo ctx ga 0 #[] #[] (← get).flowGen)
          blocks := blocks ++ (← elabBlocksGo ctx gb 0 #[] #[] (← get).flowGen)
          return (blocks, ⟨j3 + 1, by omega⟩)
      | _, _ =>
        diag ctx .E0304 "'\\alt' needs <spec>{content}{content}" pos
        return (blocks, ⟨i + 1, by omega⟩)
    else
      match hgg : raws[jg]? with
      | some (.group gbody _) =>
        have hgw : rawWeightList gbody.toList + 1 ≤ sliceWeight raws jg := by
          have := elem_weight_le hgg (Nat.le_refl jg)
          simp only [rawWeight] at this; omega
        have hgp : nestedParsList gbody.toList ≤ slicePars raws jg := by
          have := elem_pars_le hgg (Nat.le_refl jg)
          simp only [nestedPars] at this
          have := nestedParsList_le gbody.toList; omega
        have hg2 : sliceWeight raws jg ≤ sliceWeight raws i := by
          have := sliceWeight_le raws (show i ≤ jg by omega); omega
        have hg3 : slicePars raws jg ≤ slicePars raws i := by
          have := slicePars_le raws (show i ≤ jg by omega); omega
        have h0g : sliceWeight gbody 0 = rawWeightList gbody.toList :=
          sliceWeight_zero _
        have h1g : slicePars gbody 0 = nestedParsList gbody.toList :=
          slicePars_zero _
        match spec with
        | some (s, last) =>
          let ⟨stepCtx, hm⟩ : MCtx ctx ←
            pure ⟨{ ctx with stepBase := max ctx.stepBase (s - 1) },
              rfl, rfl, rfl, rfl⟩
          let inner ← elabBlocksGo stepCtx gbody 0 #[] #[] (← get).flowGen
          unless inner.isEmpty do
            blocks := blocks.push (.step s last inner)
          return (blocks, ⟨jg + 1, by omega⟩)
        | none =>
          blocks := blocks ++ (← elabBlocksGo ctx gbody 0 #[] #[]
            (← get).flowGen)
          return (blocks, ⟨jg + 1, by omega⟩)
      | _ =>
        -- The open form: the rest of this scope steps. Bare
        -- \onslide (no spec) ends stepping — the rest simply flows.
        match spec with
        | some (s, last) =>
          have hxw : rawWeightList (raws.extract jg raws.size).toList
              ≤ sliceWeight raws jg := extract_slice_le ..
          have hxp : nestedParsList (raws.extract jg raws.size).toList
              ≤ slicePars raws jg := extract_slice_pars_le ..
          have hg2 : sliceWeight raws jg < sliceWeight raws i := by
            have := sliceWeight_le raws (show i + 1 ≤ jg by omega); omega
          have hg3 : slicePars raws jg ≤ slicePars raws i := by
            have := slicePars_le raws (show i ≤ jg by omega); omega
          have h0x : sliceWeight (raws.extract jg raws.size) 0
              = rawWeightList (raws.extract jg raws.size).toList :=
            sliceWeight_zero _
          have h1x : slicePars (raws.extract jg raws.size) 0
              = nestedParsList (raws.extract jg raws.size).toList :=
            slicePars_zero _
          let ⟨stepCtx, hm⟩ : MCtx ctx ←
            pure ⟨{ ctx with stepBase := max ctx.stepBase (s - 1) },
              rfl, rfl, rfl, rfl⟩
          let inner ← elabBlocksGo stepCtx (raws.extract jg raws.size) 0
            #[] #[] (← get).flowGen
          unless inner.isEmpty do
            blocks := blocks.push (.step s last inner)
          return (blocks, ⟨raws.size, by omega⟩)
        | none =>
          return (blocks, ⟨jg, by omega⟩)
  else if titleCtrls.contains n then
    let (⟨j, hj⟩, junk) ← takeTitleDecl ctx n raws (i + 1) pos
    -- The malformed run of an unclosed bracket is content here.
    if let some p ← mkPara ctx junk then
      blocks := blocks.push p
    return (blocks, ⟨j, by omega⟩)
  else if n == "logo" then
    -- The declaration is legal in the body too, where beamer decks
    -- scope a logo to a frame (`\logo{...}` before it, `\logo{}`
    -- after): a stateful block the layout replays per page.
    let j := skipSpaces raws (i + 1)
    have hjge := skipSpaces_ge raws (i + 1)
    match raws[j]? with
    | some (.group gbody _) =>
      blocks := blocks.push (.logo (← elabInlines ctx gbody))
      return (blocks, ⟨j + 1, by omega⟩)
    | _ =>
      diag ctx .E0304 "'\\logo' needs one group of inline content" pos
      return (blocks, ⟨i + 1, by omega⟩)
  else if n == "maketitle" || n == "titlepage" then
    blocks ← maketitleArm ctx n pos blocks
    return (blocks, ⟨i + 1, by omega⟩)
  else
    let level := (sectionLevel n).getD 1
    let starred := raws[i + 1]? matches some (.word "*" _)
    let i1p : { x : Nat // i + 1 ≤ x } :=
      match raws[i + 1]? with
      | some (.word "*" _) => ⟨i + 2, by omega⟩
      | _ => ⟨i + 1, by omega⟩
    let i1 := i1p.1
    have hi1 : i + 1 ≤ i1 := i1p.2
    -- `\section[short]{long}`: the short form feeds furniture no
    -- backend consumes yet, and its bracket obeys the shared
    -- scanner. The malformed run of an unclosed bracket is content
    -- here, exactly as in the scanner's sibling paths.
    if let .took _ := scanBracketArg raws i1 pos then
      warnOnce ctx "section:short" .N0103
        s!"'\\{n}[short]' short title is unused: nothing consumes it yet" pos
    let (⟨j, hj⟩, recovered, junk) ← skipOptArg ctx n raws i1 pos
    if let some p ← mkPara ctx junk then
      blocks := blocks.push p
    match raws[j]? with
    | some (.group title _) =>
      blocks := blocks.push (.section level starred
        (← sectionNumber ctx level starred) (← elabInlines ctx title))
      return (blocks, ⟨j + 1, by omega⟩)
    | _ =>
      if recovered then
        warnSkippedDecl ctx n pos
        return (blocks, ⟨j, by omega⟩)
      else
        diag ctx .E0304 s!"'\\{n}' needs a \{title}" pos
        return (blocks, ⟨i + 1, by omega⟩)
termination_by (ctx.envLimit, noteFlag ctx,
  visParsGo ctx.user ctx.limit + slicePars raws i,
  visWeightGo ctx.user ctx.limit + sliceWeight raws i, 1, 0)
decreasing_by all_goals blocks_dec

/-- The block spine: one raw considered per call. A scope group holding a
paragraph end is spliced open first, so the `\par` inside it is the
boundary it is everywhere else; a non-boundary raw joins the open
paragraph; a boundary flushes it and dispatches. The flow state is re-read
each step (`flowCtx`), so a body declaration reaches the content after the
scope that made it. -/
private def elabBlocksGo (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (blocks : Array Block) (cur : Array Raw) (gen : Nat) :
    EM (Array Block) := do
  let stFlow ← get
  let ⟨ctx', hfm⟩ : MCtx ctx ←
    pure ⟨flowCtx ctx stFlow gen, flowCtx_measure ctx stFlow gen⟩
  let gen' ← pure stFlow.flowGen
  if h : i < raws.size then
    have hadv : sliceWeight raws (i + 1) < sliceWeight raws i :=
      sliceWeight_lt raws h (by omega)
    have hadvp : slicePars raws (i + 1) ≤ slicePars raws i :=
      slicePars_le raws (by omega)
    have hpos : 0 < sliceWeight raws i := by omega
    match hr : raws[i] with
    | .group body gpos =>
      have hre : raws[i]? = some (.group body gpos) := by
        rw [Array.getElem?_eq_getElem h]; exact congrArg some hr
      have hgw : rawWeightList body.toList + 1 ≤ sliceWeight raws i := by
        have := elem_weight_le hre (Nat.le_refl i)
        simp only [rawWeight] at this; omega
      have hgp : nestedParsList body.toList ≤ slicePars raws i := by
        have := elem_pars_le hre (Nat.le_refl i)
        simp only [nestedPars] at this
        have := nestedParsList_le body.toList; omega
      have hg0 : sliceWeight body 0 = rawWeightList body.toList :=
        sliceWeight_zero _
      have hg1 : slicePars body 0 = nestedParsList body.toList :=
        slicePars_zero _
      if hpp : body.any isParRaw && !isArgument cur then
        -- A scope group holding a paragraph end is spliced open first, so
        -- the `\par` inside it is the boundary it is everywhere else.
        have hpp2 : body.any isParRaw = true := by
          simp only [Bool.and_eq_true] at hpp; exact hpp.1
        have hdec := slicePars_splice h hr hpp2 ctx' gpos
        have hdec2 : slicePars (raws.extract 0 i
            ++ (splitAtPars ctx' body gpos ++ raws.extract (i + 1) raws.size)) i
            < slicePars raws i := by
          rw [← Array.append_assoc]; exact hdec
        elabBlocksGo ctx' (raws.extract 0 i
          ++ splitAtPars ctx' body gpos ++ raws.extract (i + 1) raws.size) i
          blocks cur gen'
      else if body.any isCenteringRaw && !isArgument cur then
        -- A scope group carrying a `\centering` declaration is a block
        -- scope: the declaration needs blocks to centre, and the group's
        -- edge is exactly how far it reaches. An argument group is the
        -- command's, as in the par splice above; its own block sequence,
        -- so the declaration stops at the closing brace.
        let blocks ← flushPara ctx' blocks cur
        let inner ← elabBlocksGo ctx' body 0 #[] #[] (← get).flowGen
        elabBlocksGo ctx' raws (i + 1) (blocks ++ inner) #[] gen'
      else
        elabBlocksGo ctx' raws (i + 1) blocks (cur.push raws[i]) gen'
    | .par _ =>
      let blocks ← flushPara ctx' blocks cur
      elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
    | .verb s _ =>
      let blocks ← flushPara ctx' blocks cur
      elabBlocksGo ctx' raws (i + 1) (blocks.push (.verbatim none s)) #[] gen'
    | .math display body mpos =>
      if display then
        -- A display formula: one centred block of its own, so it
        -- participates in the block machinery like any other line.
        -- `\[` never numbers (amsldoc §3), but a label inside it still
        -- binds to the flow's last number rather than degrading the
        -- formula to source text.
        let blocks ← flushPara ctx' blocks cur
        let (cleaned, keys, _) ← stripMathMeta ctx' body
        let inl ← elabMathInline ctx' true cleaned mpos
        for key in keys do
          recordLabel ctx' key (← get).refTarget mpos
        let content := keys.map (Ir.Inline.label ·) |>.push inl
        elabBlocksGo ctx' raws (i + 1)
          (blocks.push (.center #[.para content])) #[] gen'
      else
        elabBlocksGo ctx' raws (i + 1) blocks (cur.push raws[i]) gen'
    | .env n body epos =>
      have hre : raws[i]? = some (.env n body epos) := by
        rw [Array.getElem?_eq_getElem h]; exact congrArg some hr
      have hew : rawWeightList body.toList + 1 ≤ sliceWeight raws i := by
        have := elem_weight_le hre (Nat.le_refl i)
        simp only [rawWeight] at this; omega
      have hep : rawParsList body.toList ≤ slicePars raws i := by
        have := elem_pars_le hre (Nat.le_refl i)
        simp only [nestedPars] at this; omega
      let isB : Bool :=
        if (Parse.inputEnvFile? n).isSome then bodyIsBlock body
        else
          blockEnvs.contains n || isMathEnv n
            || n == "tabular" || n == "tabular*"
            || reservedEnv.contains n
            || (match lookupUserEnv ctx' n with
                | some (_, env) =>
                  bodyIsBlock env.beginBody || bodyIsBlock env.endBody
                | none => false)
            || bodyIsBlock body
      if isB then
        let blocks ← flushPara ctx' blocks cur
        let blocks ← elabEnvArm ctx' n body epos blocks
        elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else
        elabBlocksGo ctx' raws (i + 1) blocks (cur.push raws[i]) gen'
    | .ctrl n cpos =>
      let isB : Bool :=
        n == "par" || n == "block" || n == "centering" || n == "pause"
          || n == "framefoot" || n == "pagebreak" || n == "appendix"
          || n == "bibliography" || n == "bibliographystyle"
          || (n == "note" && cur.isEmpty)
          -- `\color{n}`'s block form: a flow ink declaration (the arm
          -- below). Mid-paragraph the marker keeps the inline reading —
          -- splitting the paragraph there would move text.
          || (cur.isEmpty && n.startsWith "@ink:")
          || (cur.isEmpty && n.startsWith "@lang:")
          || (n != "note" &&
            ((sectionLevel n).isSome
              || declCtrl.contains n || runningCtrl.contains n || n == "define"
              || counterCtrl n
              || (match lookupUser ctx' n with
                  | some (_, cmd) => bodyIsBlock cmd.body
                  | none =>
                    ((overlayCtrls.contains n || n == "alt") &&
                      overlayTakesBlocks raws i cur.isEmpty (n == "alt")) ||
                    titleCtrls.contains n || n == "maketitle"
                      || n == "titlepage" || n == "logo")))
      if !isB then
        elabBlocksGo ctx' raws (i + 1) blocks (cur.push raws[i]) gen'
      else
      let blocks ← flushPara ctx' blocks cur
      if n == "par" then
        elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else if n == "centering" then
        -- The declaration form of \begin{center}: the rest of this scope
        -- centres. Text flushed just above stays uncentred — LaTeX would
        -- re-align the whole broken paragraph; this engine centres from
        -- the declaration on.
        have hxw : rawWeightList (raws.extract (i + 1) raws.size).toList
            ≤ sliceWeight raws (i + 1) := extract_slice_le ..
        have hxp : nestedParsList (raws.extract (i + 1) raws.size).toList
            ≤ slicePars raws (i + 1) := extract_slice_pars_le ..
        have hx0 : sliceWeight (raws.extract (i + 1) raws.size) 0
            = rawWeightList (raws.extract (i + 1) raws.size).toList :=
          sliceWeight_zero _
        have hx1 : slicePars (raws.extract (i + 1) raws.size) 0
            = nestedParsList (raws.extract (i + 1) raws.size).toList :=
          slicePars_zero _
        let inner ← elabBlocksGo ctx' (raws.extract (i + 1) raws.size) 0
          #[] #[] (← get).flowGen
        let blocks := if inner.isEmpty then blocks
          else blocks.push (.center inner)
        have hend : sliceWeight raws raws.size = 0 :=
          sliceWeight_end raws (Nat.le_refl _)
        have hendp : slicePars raws raws.size = 0 :=
          slicePars_end raws (Nat.le_refl _)
        elabBlocksGo ctx' raws raws.size blocks #[] gen'
      else if n.startsWith "@lang:" then
        -- The language switch, block form: from here forward in flow
        -- order (the `\appendix` scope model).
        modify (flowLangUpdate ctx' n)
        elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else if n == "appendix" then
        -- Not a heading: a declaration affecting every heading after it,
        -- from here forward in flow order (the scope model body \palette
        -- landed) — the counter restarts and level-1 numbers letter.
        modify fun st => { st with inAppendix := true, secNums := (0, 0, 0) }
        elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else if n == "pause" then
        -- The rest of this scope reveals one step later. Numbering is
        -- cumulative through nesting: each pause raises the base its
        -- successors count from, so pending content stays pending.
        have hxw : rawWeightList (raws.extract (i + 1) raws.size).toList
            ≤ sliceWeight raws (i + 1) := extract_slice_le ..
        have hxp : nestedParsList (raws.extract (i + 1) raws.size).toList
            ≤ slicePars raws (i + 1) := extract_slice_pars_le ..
        have hx0 : sliceWeight (raws.extract (i + 1) raws.size) 0
            = rawWeightList (raws.extract (i + 1) raws.size).toList :=
          sliceWeight_zero _
        have hx1 : slicePars (raws.extract (i + 1) raws.size) 0
            = nestedParsList (raws.extract (i + 1) raws.size).toList :=
          slicePars_zero _
        let ⟨stepCtx, hm⟩ : MCtx ctx' ←
          pure ⟨{ ctx' with stepBase := ctx'.stepBase + 1 }, rfl, rfl, rfl, rfl⟩
        let inner ← elabBlocksGo stepCtx (raws.extract (i + 1) raws.size) 0
          #[] #[] (← get).flowGen
        let blocks := if inner.isEmpty then blocks
          else blocks.push (.step (ctx'.stepBase + 2) none inner)
        have hend : sliceWeight raws raws.size = 0 :=
          sliceWeight_end raws (Nat.le_refl _)
        have hendp : slicePars raws raws.size = 0 :=
          slicePars_end raws (Nat.le_refl _)
        elabBlocksGo ctx' raws raws.size blocks #[] gen'
      else if n == "note" then
        -- \note[placement]<spec>{...}: the placement and the spec are
        -- ignored with a note saying so; the body is the side channel,
        -- never slide content.
        if let .took _ := scanBracketArg raws (i + 1) cpos then
          warnOnce ctx' "note:options" .N0102
            "'\\note' placement and overlay options are ignored: the note is \
a side channel, never slide content" cpos
        let (⟨j, hj⟩, _, _) ← skipOptArg ctx' "note" raws (i + 1) cpos
        let js := skipSpaces raws j
        have hjs := skipSpaces_ge raws j
        let ⟨i2, hi2⟩ : { x : Nat // i + 1 ≤ x } ←
          if (raws[js]?.bind specWord?).isSome then do
            warnOnce ctx' "note:options" .N0102
              "'\\note' placement and overlay options are ignored: the note is \
a side channel, never slide content" cpos
            pure ⟨js + 1, by omega⟩
          else pure ⟨j, by omega⟩
        let ⟨j2, hj2⟩ : { x : Nat // i2 ≤ x } ←
          pure ⟨skipSpaces raws i2, skipSpaces_ge raws i2⟩
        match hg2 : raws[j2]? with
        | some (.group nbody _) =>
          have hnw : rawWeightList nbody.toList + 1 ≤ sliceWeight raws j2 := by
            have := elem_weight_le hg2 (Nat.le_refl j2)
            simp only [rawWeight] at this; omega
          have hnp : nestedParsList nbody.toList ≤ slicePars raws j2 := by
            have := elem_pars_le hg2 (Nat.le_refl j2)
            simp only [nestedPars] at this
            have := nestedParsList_le nbody.toList; omega
          have hn2 : sliceWeight raws j2 ≤ sliceWeight raws i := by
            have := sliceWeight_le raws (show i ≤ j2 by omega); omega
          have hn3 : slicePars raws j2 ≤ slicePars raws i := by
            have := slicePars_le raws (show i ≤ j2 by omega); omega
          have hn0 : sliceWeight nbody 0 = rawWeightList nbody.toList :=
            sliceWeight_zero _
          have hn1 : slicePars nbody 0 = nestedParsList nbody.toList :=
            slicePars_zero _
          let ⟨noteCtx, hnc⟩ : { c : Ctx // c.envLimit = ctx'.envLimit
              ∧ noteFlag c = 0
              ∧ visParsGo c.user c.limit = visParsGo ctx'.user ctx'.limit
              ∧ visWeightGo c.user c.limit = visWeightGo ctx'.user ctx'.limit } ←
            pure ⟨{ ctx' with noteBody := true, notePos := some cpos },
              rfl, rfl, rfl, rfl⟩
          let inner ← elabBlocksGo noteCtx nbody 0 #[] #[] (← get).flowGen
          have ht1 : sliceWeight raws (j2 + 1) < sliceWeight raws i :=
            sliceWeight_lt raws h (by omega)
          have ht2 : slicePars raws (j2 + 1) ≤ slicePars raws i :=
            slicePars_le raws (by omega)
          elabBlocksGo ctx' raws (j2 + 1)
            (blocks.push (.note inner)) #[] gen'
        | _ =>
          warnSkippedDecl ctx' "note" cpos
          have ht1 : sliceWeight raws i2 < sliceWeight raws i :=
            sliceWeight_lt raws h (by omega)
          have ht2 : slicePars raws i2 ≤ slicePars raws i :=
            slicePars_le raws (by omega)
          elabBlocksGo ctx' raws i2 blocks #[] gen'
      else if n == "framefoot" then
        -- The per-frame footer note (beamer's `frame footer` template,
        -- through compat): sets the chrome footer's left slot for the
        -- frames that follow; an empty group clears it.
        let ⟨j, hjge⟩ : { x : Nat // i + 1 ≤ x } ←
          pure ⟨skipSpaces raws (i + 1), skipSpaces_ge raws (i + 1)⟩
        match raws[j]? with
        | some (.group fbody _) =>
          let blocks := blocks.push (.framefoot (← elabInlines ctx' fbody))
          have ht1 : sliceWeight raws (j + 1) < sliceWeight raws i :=
            sliceWeight_lt raws h (by omega)
          have ht2 : slicePars raws (j + 1) ≤ slicePars raws i :=
            slicePars_le raws (by omega)
          elabBlocksGo ctx' raws (j + 1) blocks #[] gen'
        | _ =>
          diag ctx' .E0304 "'\\framefoot' needs one group of inline content" cpos
          elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else if n.startsWith "@ink:" then
        -- xcolor's `\color{n}` at block level colours to the end of the
        -- enclosing group (xcolor manual §2.6.4), and at the flow's top
        -- level that is the rest of the document — the default ink
        -- itself. It routes through the palette's one resolving site:
        -- the flow palette's `fg` is declared (`inkFlowDecl`), so the
        -- resolved design, both backends, and the contrast judge all see
        -- the declared body colour instead of a silently defaulted pure
        -- black. (In a nested body the flow scope is the same
        -- approximation `\palette` makes: no brace revert.) A bare
        -- palette name keeps its documented reading — rest of the group —
        -- and never reaches here.
        let pal? ← inkFlowDecl ctx' n cpos
        let ⟨palCtx, hm⟩ : MCtx ctx' ←
          pure ⟨{ ctx' with palette := pal?.getD ctx'.palette }, rfl, rfl, rfl, rfl⟩
        have ht1 : sliceWeight raws (i + 1) < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        have ht2 : slicePars raws (i + 1) ≤ slicePars raws i :=
          slicePars_le raws (by omega)
        elabBlocksGo palCtx raws (i + 1)
          (match pal? with
            | some pal => blocks.push (.setPalette pal)
            | none => blocks) #[] ((← get).flowGen)
      else if n == "palette" then
        -- Legal in the body as in LaTeX (`\colorlet` rewrites to it):
        -- the entries apply from here on, and the document palette both
        -- backends and the contrast checks read carries them.
        let j0 := skipSpaces raws (i + 1)
        have hj0 : i + 1 ≤ j0 := skipSpaces_ge raws (i + 1)
        let ⟨(decorative, skipBlock, jf), hjf⟩ :
            { t : Bool × Bool × Nat // i + 1 ≤ t.2.2 } ←
          if let some (.sym '[' _) := raws[j0]? then do
            let ⟨(opt, k), hk⟩ : { t : Array Raw × Nat // i + 1 ≤ t.2 } :=
              match hc : closeBracketFrom raws (j0 + 1) with
              | some c => ⟨(raws.extract (j0 + 1) c, c + 1), by
                  have := closeBracketFrom_ge hc; omega⟩
              | none => ⟨(raws.extract (j0 + 1) raws.size, raws.size), by omega⟩
            have hk2 : i + 1 ≤ k := hk
            let mut decorative := false
            let mut skipBlock := false
            for e in Decl.splitEntries (rawSrc opt) do
              if e == "decorative" then
                decorative := true
              else
                diag ctx' .W0316
                  s!"unknown option in '\\palette': {e.quote}; block skipped" cpos
                  (help := "options: decorative")
                skipBlock := true
            pure ⟨(decorative, skipBlock, skipSpaces raws k), by
              have := skipSpaces_ge raws k
              show i + 1 ≤ skipSpaces raws k
              omega⟩
          else
            pure ⟨(false, false, j0), hj0⟩
        have hjf2 : i + 1 ≤ jf := hjf
        match raws[jf]? with
        | some (.group gbody _) =>
          have ht1 : sliceWeight raws (jf + 1) < sliceWeight raws i :=
            sliceWeight_lt raws h (by omega)
          have ht2 : slicePars raws (jf + 1) ≤ slicePars raws i :=
            slicePars_le raws (by omega)
          if skipBlock then
            elabBlocksGo ctx' raws (jf + 1) blocks #[] gen'
          else
            let pal ← applyPalette ctx' ctx'.palette (rawSrc gbody) cpos
              (decorative := decorative)
            let ⟨palCtx, hm⟩ : MCtx ctx' ←
              pure ⟨{ ctx' with palette := pal }, rfl, rfl, rfl, rfl⟩
            -- The declaration rides the IR in flow order: both backends
            -- replay it where it stands, and the flow state carries it
            -- past this scope's close (no brace revert).
            modify fun st => { st with flowPalette := some pal
                                       flowGen := st.flowGen + 1 }
            elabBlocksGo palCtx raws (jf + 1)
              (blocks.push (.setPalette pal)) #[] ((← get).flowGen)
        | _ =>
          diag ctx' .E0304 "'\\palette' needs a {...} block" cpos
          elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else if n == "tokens" then
        -- `\setlength` mid-document rewrites here; same door as above.
        let ⟨j, hjge⟩ : { x : Nat // i + 1 ≤ x } ←
          pure ⟨skipSpaces raws (i + 1), skipSpaces_ge raws (i + 1)⟩
        match raws[j]? with
        | some (.group gbody _) =>
          let tk ← applyTokens ctx' ctx'.tokens (rawSrc gbody) cpos
            (engine := ctx'.engineTokens)
          let ⟨tokCtx, hm⟩ : MCtx ctx' ←
            pure ⟨{ ctx' with tokens := tk }, rfl, rfl, rfl, rfl⟩
          modify fun st => { st with flowTokens := some tk
                                     flowGen := st.flowGen + 1 }
          have ht1 : sliceWeight raws (j + 1) < sliceWeight raws i :=
            sliceWeight_lt raws h (by omega)
          have ht2 : slicePars raws (j + 1) ≤ slicePars raws i :=
            slicePars_le raws (by omega)
          elabBlocksGo tokCtx raws (j + 1)
            (blocks.push (.setTokens tk)) #[] ((← get).flowGen)
        | _ =>
          diag ctx' .E0304 "'\\tokens' needs a {...} block" cpos
          elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else if n == "define" then
        -- A definition in the body, legal as in LaTeX (`\newcommand`
        -- rewrites here): it binds through the shared door the preamble
        -- uses and applies to the rest of this walk. Inline positions
        -- (inside a paragraph or an argument) keep the E0312 refusal,
        -- except the heading-number format, legal anywhere.
        let ⟨(cmd?, k), hdef⟩ ← takeDefine ctx' raws (i + 1) cpos
        have hk : i + 1 ≤ k := hdef.1
        have hks : sliceWeight raws k ≤ sliceWeight raws (i + 1) :=
          sliceWeight_le raws hk
        have hkp : slicePars raws k ≤ slicePars raws (i + 1) :=
          slicePars_le raws hk
        match hcm : cmd? with
        | some cmd =>
          if let some (lvl, parts) := secFmtDefine? cmd then
            -- Not a macro: a heading-number format declaration
            -- (`secFmtDefine?`), applied from where it stands.
            applySecFmt lvl parts
            elabBlocksGo ctx' raws k blocks #[] gen'
          else
            have h2 : rawWeightList cmd.body.toList + sliceWeight raws k + 2
                ≤ sliceWeight raws (i + 1) := (hdef.2 cmd hcm).1
            have h3 : rawParsList cmd.body.toList + slicePars raws k
                ≤ slicePars raws (i + 1) := (hdef.2 cmd hcm).2
            let keep ← gateRedefB ctx' cmd
            if keep then
              -- The definition binds at the visibility boundary
              -- (`bindCmd`): the rest of this walk sees exactly one more
              -- command, never the suffix beyond `limit`. Monotone
              -- visibility is the expansion's whole termination argument
              -- (`Ctx.limit`, `bindCmd_monotone`); raising `limit` to the
              -- array's end here re-exposed a command being expanded to its
              -- own body, and a venue file's `\maketitle` — which renews
              -- `\thefootnote` and then names itself in `\let` — diverged.
              have hbp := bindCmd_visPars ctx' cmd
              have hbw := bindCmd_visWeight ctx' cmd
              have hbe : (bindCmd ctx' cmd).envLimit = ctx'.envLimit
                  ∧ noteFlag (bindCmd ctx' cmd) = noteFlag ctx' := ⟨rfl, rfl⟩
              elabBlocksGo (bindCmd ctx' cmd) raws k blocks #[] gen'
            else
              elabBlocksGo ctx' raws k blocks #[] gen'
        | none =>
          elabBlocksGo ctx' raws k blocks #[] gen'
      else if counterCtrl n then
        let ⟨j2, hj2⟩ ← counterArm ctx' raws (i + 1) n cpos
        have ht1 : sliceWeight raws j2 < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        have ht2 : slicePars raws j2 ≤ slicePars raws i :=
          slicePars_le raws (by omega)
        elabBlocksGo ctx' raws j2 blocks #[] gen'
      else if n == "bibliographystyle" then
        -- The declared style rides the state to the `\bibliography`
        -- marker; resolution reads it from the block (W0353 there names
        -- an unknown one).
        let ⟨j, hjge⟩ : { x : Nat // i + 1 ≤ x } ←
          pure ⟨skipSpaces raws (i + 1), skipSpaces_ge raws (i + 1)⟩
        match raws[j]? with
        | some (.group body _) =>
          modify fun st => { st with
            bibStyle := some (rawSrc body).trimAscii.toString }
          have ht1 : sliceWeight raws (j + 1) < sliceWeight raws i :=
            sliceWeight_lt raws h (by omega)
          have ht2 : slicePars raws (j + 1) ≤ slicePars raws i :=
            slicePars_le raws (by omega)
          elabBlocksGo ctx' raws (j + 1) blocks #[] gen'
        | some (.word w _) =>
          modify fun st => { st with bibStyle := some w }
          have ht1 : sliceWeight raws (j + 1) < sliceWeight raws i :=
            sliceWeight_lt raws h (by omega)
          have ht2 : slicePars raws (j + 1) ≤ slicePars raws i :=
            slicePars_le raws (by omega)
          elabBlocksGo ctx' raws (j + 1) blocks #[] gen'
        | _ =>
          diag ctx' .E0304 "'\\bibliographystyle' needs a {style} group" cpos
          elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else if n == "bibliography" then
        -- The reference list marker: an unnumbered References section
        -- (classes.dtx: thebibliography opens with \section*{\refname})
        -- and the empty list the driver's `.bib` effect fills
        -- (`Ir.bibRefs` is the request, `Bib.apply` the fulfilment).
        let ⟨j, hjge⟩ : { x : Nat // i + 1 ≤ x } ←
          pure ⟨skipSpaces raws (i + 1), skipSpaces_ge raws (i + 1)⟩
        match raws[j]? with
        | some (.group body _) =>
          let src := (rawSrc body).trimAscii.toString
          let style := (← get).bibStyle
          -- \refname is locale data (babel ini captions): the heading is
          -- worded in the document's declared language.
          let blocks := blocks.push
            (.section 1 true none #[.text ctx'.locale.references])
          let blocks := blocks.push (.bibliography src style #[])
          have ht1 : sliceWeight raws (j + 1) < sliceWeight raws i :=
            sliceWeight_lt raws h (by omega)
          have ht2 : slicePars raws (j + 1) ≤ slicePars raws i :=
            slicePars_le raws (by omega)
          elabBlocksGo ctx' raws (j + 1) blocks #[] gen'
        | _ =>
          diag ctx' .E0304 "'\\bibliography' needs a {file} group" cpos
          elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else if n == "pagebreak" then
        -- The declared page boundary; adjacent boundaries never make a
        -- blank page (the page builder closes only pages that hold
        -- something).
        elabBlocksGo ctx' raws (i + 1) (blocks.push .pagebreak) #[] gen'
      else if n == "block" then
        -- \block[before = <len>]{content}
        let j0 := skipSpaces raws (i + 1)
        have hj0 : i + 1 ≤ j0 := skipSpaces_ge raws (i + 1)
        let ⟨(before, jf), hjf⟩ : { t : SymGlue × Nat // i + 1 ≤ t.2 } ←
          if let some (.sym '[' _) := raws[j0]? then do
            let ⟨(optSrc, k), hk⟩ : { t : Array Raw × Nat // i + 1 ≤ t.2 } :=
              match hc : closeBracketFrom raws (j0 + 1) with
              | some c => ⟨(raws.extract (j0 + 1) c, c + 1), by
                  have := closeBracketFrom_ge hc; omega⟩
              | none => ⟨(raws.extract (j0 + 1) raws.size, raws.size), by omega⟩
            have hk2 : i + 1 ≤ k := hk
            let (opts, ds) := Decl.parseBlock ctx'.file (rawSrc optSrc) cpos
              "block" ctx'.tokens.entries
            modify fun st => { st with diags := st.diags ++ ds }
            let mut before : SymGlue := {}
            for e in opts do
              match e.key, e.value with
              | "before", .glue g => before := g
              | "before", .dim d => before := { width := Dim.Length.ofSp d }
              | key, v =>
                if key == "before" then
                  modify fun st => { st with
                    diags := st.diags.push (Decl.wrongType ctx'.file "block" key
                      "a length" v cpos) }
                else
                  modify fun st => { st with
                    diags := st.diags.push (Decl.unknownKey ctx'.file "block" key
                      ["before"] cpos) }
            pure ⟨(before, skipSpaces raws k), by
              have := skipSpaces_ge raws k
              show i + 1 ≤ skipSpaces raws k
              omega⟩
          else
            pure ⟨({}, j0), hj0⟩
        have hjf2 : i + 1 ≤ jf := hjf
        match hgf : raws[jf]? with
        | some (.group body _) =>
          have hbw : rawWeightList body.toList + 1 ≤ sliceWeight raws jf := by
            have := elem_weight_le hgf (Nat.le_refl jf)
            simp only [rawWeight] at this; omega
          have hbp : nestedParsList body.toList ≤ slicePars raws jf := by
            have := elem_pars_le hgf (Nat.le_refl jf)
            simp only [nestedPars] at this
            have := nestedParsList_le body.toList; omega
          have hb2 : sliceWeight raws jf ≤ sliceWeight raws i := by
            have := sliceWeight_le raws (show i ≤ jf by omega); omega
          have hb3 : slicePars raws jf ≤ slicePars raws i := by
            have := slicePars_le raws (show i ≤ jf by omega); omega
          have hb0 : sliceWeight body 0 = rawWeightList body.toList :=
            sliceWeight_zero _
          have hb1 : slicePars body 0 = nestedParsList body.toList :=
            slicePars_zero _
          let inner ← elabBlocksGo ctx' body 0 #[] #[] (← get).flowGen
          have ht1 : sliceWeight raws (jf + 1) < sliceWeight raws i :=
            sliceWeight_lt raws h (by omega)
          have ht2 : slicePars raws (jf + 1) ≤ slicePars raws i :=
            slicePars_le raws (by omega)
          elabBlocksGo ctx' raws (jf + 1)
            (blocks.push (.spaced before inner)) #[] gen'
        | _ =>
          diag ctx' .E0304 "'\\block' needs a {body}" cpos
          elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else
        let (blocks, ⟨j, hij⟩) ← elabCtrlArm ctx' raws i h n cpos blocks
        have ht1 : sliceWeight raws j < sliceWeight raws i :=
          sliceWeight_lt raws h hij
        have ht2 : slicePars raws j ≤ slicePars raws i :=
          slicePars_le raws (by omega)
        elabBlocksGo ctx' raws j blocks #[] gen'
    | _ =>
      if cur.isEmpty && isSpaceOrPar raws[i] then
        elabBlocksGo ctx' raws (i + 1) blocks cur gen'
      else
        elabBlocksGo ctx' raws (i + 1) blocks (cur.push raws[i]) gen'
  else
    flushPara ctx' blocks cur
termination_by (ctx.envLimit, noteFlag ctx,
  visParsGo ctx.user ctx.limit + slicePars raws i,
  visWeightGo ctx.user ctx.limit + sliceWeight raws i, 2, 0)
decreasing_by all_goals blocks_dec

end

/-- Elaborate raw items as a block sequence. -/
def elabBlocks (ctx : Ctx) (raws : Array Raw) : EM (Array Block) := do
  elabBlocksGo ctx raws 0 #[] #[] (← get).flowGen

/-- Elaboration terminates — not a sentence in a plan: `takeArgs`,
`elabInlines`, and `elabBlocks` are total functions of this file, so a
change that reintroduces nontermination fails the termination checker at
its own commit, never a document build (PLAN 2026-09-19; the sentence with
no checker that hid the bindCmd bug for twelve hours — `bindCmd_monotone`
holds the monotone-visibility half). The block knot's measure is
(envLimit, noteFlag, visPars + slicePars, visWeight + sliceWeight, layer,
scan); the inline knot's is (envLimit, limit, slice weight). The statement
below is deliberately the weakest sufficient form — evaluation is
defined — because the guarantee's force lives in the definitions the
checker verified and in the pre-commit gate that keeps the escape-keyword
allowance at none; the name exists so the plan's claim has a checker to
cite. -/
theorem elaboration_total (ctx : Ctx) (raws : Array Raw) (st : ESt) :
    ∃ r, (elabBlocks ctx raws).run st = r :=
  ⟨_, rfl⟩

unseal String.trimAscii Parse.rawSrc Parse.rawSrcOne Decl.splitEntries
unseal Decl.splitEntry Decl.parseValue Decl.parseDecimal smartPunct
unseal String.Slice.trimAscii String.Slice.trimAsciiStart String.Slice.trimAsciiEnd
unseal String.Slice.dropWhile String.Slice.dropEndWhile String.Slice.skipPrefixWhile
unseal takeArgs mkPara flushPara stripMathMeta
unseal elabMathInline elabMathEnv applyPalette applyTokens parseColSpec
unseal titleBlocks Picture.elabPicture MathParse.parseMath
unseal Decl.parseBlock Decl.parseLength Decl.parseGlue skipOptArg takeTitleDecl
unseal sectionNumber columnWidth cmidRange trimRawEdges
unseal recordLabel refuseRedef dropEnvArgs skipReservedArgs takeDefine
unseal secFmtDefine? secFmtOfBody applySecFmt applyCounter counterCtrl counterArm
unseal theCounterLevel? String.toInt? String.toNat?
unseal Ir.padTableRows Ir.setAltBlocks Ir.plainText
unseal bodyIsBlock bodyIsBlockList bodyIsBlockOne overlayTakesBlocks
unseal DiagCode.ofString? Diag.of renderedBuiltins structuralNames
unseal declCtrl runningCtrl titleCtrls overlayCtrls blockEnvs reservedEnv
unseal displayMathEnvs alignEnvs isMathEnv sectionLevel specWord? overlayFrom
unseal lookupUser lookupUserEnv isArgument isCenteringRaw isParRaw splitAtPars
unseal scanBracketArg Parse.inputEnvFile?

/-- A declared value as its author would rewrite it: what W0343 quotes back
when a later declaration overwrites it. -/
private def renderValue : Decl.Value → String
  | .str s => s
  | .dim sp => s!"{sp.toPtString}pt"
  | .int n => toString n
  | .ident s => s
  | .block src => "{" ++ src ++ "}"
  | .color r g b => s!"#{Color.hexByte r}{Color.hexByte g}{Color.hexByte b}"
  | .cmyk c m y k => s!"cmyk({c}, {m}, {y}, {k})"
  | .glue g => Ir.dumpGlue g

/-- One scalar setting was declared: warn (W0343) when this `(decl, key)`
was already given a *different* value — the earlier write is dead
configuration, and silence here is how `\fonts` faces stayed first-wins for
so long — then record the new value, the one that wins. A repeat of the
same value stays silent: it changes nothing and is often synthesized
(a class option beside its `\usepackage` spelling). Keyed-merge stores
(tokens, palette, styles) never come through here: redeclare-to-override is
their layering mechanism, not a conflict. -/
private def noteScalar (ctx : Ctx) (decl key value : String) (pos : Pos) : EM Unit :=
  modify fun st => applyEvent ctx st (.scalar decl key value pos)

private def applyPage (ctx : Ctx) (spec : PageSpec) (entries : Array Decl.Entry)
    (pos : Pos) : PageSpec × Array PEvent := Id.run do
  -- A page dimension may be a declared token or an expression over them
  -- (`\geometry{paperheight=\bleedingheight}`), which parses as glue: it
  -- is a dimension when nothing font-relative or infinite rides in it —
  -- the page exists before any font is chosen.
  let asDim : Decl.Value → Option Sp
    | .dim d => some d
    | .glue g =>
      if g.width.em == 0 && g.width.ex == 0 && !g.fil then some g.width.sp else none
    | _ => none
  let say (evs : Array PEvent) (code : DiagCode) (msg : String)
      (help : Option String := none) : Array PEvent :=
    evs.push (.say (diagOf ctx code msg (some pos) help))
  let mut spec := spec
  let mut evs : Array PEvent := #[]
  for e in entries do
    let before := evs.size
    match e.key, e.value with
    | "size", .ident name =>
      match pageSizes.lookup name.toLower with
      | some (w, h) => spec := { spec with width := w, height := h }
      | none =>
        evs := say evs .E0324 s!"unknown page size '{name}'"
          (help := s!"known sizes: {String.intercalate ", " (pageSizes.map (·.1))}")
    | "width", v =>
      if let some d := asDim v then spec := { spec with width := d }
      else evs := evs.push (.say (Decl.wrongType ctx.file "page" "width" "a dimension" v pos))
    | "height", v =>
      if let some d := asDim v then spec := { spec with height := d }
      else evs := evs.push (.say (Decl.wrongType ctx.file "page" "height" "a dimension" v pos))
    | "margin", v =>
      if let some d := asDim v then spec := { spec with vmargin := d, hmargin := d }
      else evs := evs.push (.say (Decl.wrongType ctx.file "page" "margin" "a dimension" v pos))
    | "vmargin", v =>
      if let some d := asDim v then spec := { spec with vmargin := d }
      else evs := evs.push (.say (Decl.wrongType ctx.file "page" "vmargin" "a dimension" v pos))
    | "hmargin", v =>
      if let some d := asDim v then spec := { spec with hmargin := d }
      else evs := evs.push (.say (Decl.wrongType ctx.file "page" "hmargin" "a dimension" v pos))
    -- The geometry manual's text-block spelling (§5.2: `textwidth`/
    -- `textheight` size the body). The engine's page model has one margin
    -- per axis, so the block centres — geometry's own oneside horizontal
    -- default (`hmarginratio` 1:1); its 2:3 vertical ratio and an explicit
    -- `top=` are not representable and stay named (W0101 at the compat
    -- door). Resolved against the page dimension in force where the entry
    -- stands, as geometry sizes the body against the current paper.
    | "textwidth", v =>
      if let some d := asDim v then
        if 0 < d && d ≤ spec.width then
          spec := { spec with hmargin := (spec.width - d) / 2 }
        else
          evs := say evs .E0323
            "'textwidth' in '\\page' expects a dimension between zero and the page width"
      else evs := evs.push (.say (Decl.wrongType ctx.file "page" "textwidth" "a dimension" v pos))
    | "textheight", v =>
      if let some d := asDim v then
        if 0 < d && d ≤ spec.height then
          spec := { spec with vmargin := (spec.height - d) / 2 }
        else
          evs := say evs .E0323
            "'textheight' in '\\page' expects a dimension between zero and the page height"
      else evs := evs.push (.say (Decl.wrongType ctx.file "page" "textheight" "a dimension" v pos))
    | "leading", .int n => spec := { spec with leading := n.toNat * 1000 }
    | "leading", .dim d =>
      -- A bare decimal like 1.04 reads as a dimension in points; the factor
      -- is what was meant.
      spec := { spec with leading := (d * 1000 / pt 1).toNat }
    | "leading", .ident f =>
      -- ...and one without a unit reaches here as a name.
      match Decl.parseDecimal f with
      | some (m, s) => spec := { spec with leading := (m * 1000 / s).toNat }
      | none => evs := say evs .E0323 s!"'leading' in '\\page' expects a factor like 1.04, got '{f}'"
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
        evs := say evs .E0323 "'fontsize' in '\\page' expects a dimension of at least 1pt"
    | "measure", .ident v =>
      -- `free`: the document takes responsibility for its line length, and
      -- the readable-band diagnostic (W0201) stays quiet.
      match v with
      | "free" => spec := { spec with measureChecked := false }
      | "checked" => spec := { spec with measureChecked := true }
      | _ =>
        evs := say evs .E0323 s!"'measure' in '\\page' expects 'checked' or 'free', got '{v}'"
    | "bleed", .int 0 => spec := { spec with bleed := 0 }
    | "bleed", v =>
      if let some d := asDim v then spec := { spec with bleed := d }
      else evs := evs.push (.say (Decl.wrongType ctx.file "page" "bleed" "a dimension" v pos))
    | "hyphenate", .ident v =>
      match v with
      | "on" | "true" => spec := { spec with hyphenate := some true }
      | "off" | "false" => spec := { spec with hyphenate := some false }
      | _ =>
        evs := say evs .E0323 s!"'hyphenate' in '\\page' expects on or off, got '{v}'"
    | "justify", .ident v =>
      match v with
      | "on" | "true" => spec := { spec with justify := some true }
      | "off" | "false" => spec := { spec with justify := some false }
      | _ =>
        evs := say evs .E0323 s!"'justify' in '\\page' expects on or off, got '{v}'"
    | "protrusion", .ident v =>
      match v with
      | "on" | "true" => spec := { spec with protrude := some true }
      | "off" | "false" => spec := { spec with protrude := some false }
      | _ =>
        evs := say evs .E0323 s!"'protrusion' in '\\page' expects on or off, got '{v}'"
    | "expansion", .ident v =>
      match v with
      | "on" | "true" => spec := { spec with expand := some true }
      | "off" | "false" => spec := { spec with expand := some false }
      | _ =>
        evs := say evs .E0323 s!"'expansion' in '\\page' expects on or off, got '{v}'"
    | "numbers", .ident v =>
      match v with
      | "on" | "true" => spec := { spec with numbers := some true }
      | "off" | "false" => spec := { spec with numbers := some false }
      | _ =>
        evs := say evs .E0323 s!"'numbers' in '\\page' expects on or off, got '{v}'"
    -- The furniture gaps: the native key speaks in ink terms and sets both
    -- sides; the LaTeX spellings carry their baseline semantics to the one
    -- correction site in Layout (`furnGapOfSep`).
    | "furnituregap", v =>
      if let some d := asDim v then spec := { spec with furnitureGap := some d }
      else evs := evs.push (.say (Decl.wrongType ctx.file "page" "furnituregap" "a dimension" v pos))
    | "headsep", v =>
      if let some d := asDim v then spec := { spec with headsep := some d }
      else evs := evs.push (.say (Decl.wrongType ctx.file "page" "headsep" "a dimension" v pos))
    | "footskip", v =>
      if let some d := asDim v then spec := { spec with footskip := some d }
      else evs := evs.push (.say (Decl.wrongType ctx.file "page" "footskip" "a dimension" v pos))
    | key, v =>
      if key == "header" || key == "footer" then
        -- The feature exists, just not as a page key: running content is
        -- inline content, which a key/value block cannot carry.
        let cmd := if key == "header" then "\\runninghead" else "\\runningfoot"
        evs := say evs .E0327 s!"'{key}' is not a '\\page' key"
          (help := s!"{cmd}\{...} declares it; \\hfill pushes content to the right")
      else if pageKeys.contains key then
        let expected := if key == "size" then "a page size name"
          else if key == "measure" then "'checked' or 'free'"
          else if key == "hyphenate" || key == "justify" || key == "protrusion"
            || key == "expansion" || key == "numbers" then "on or off"
          else "a dimension"
        evs := evs.push (.say (Decl.wrongType ctx.file "page" key expected v pos))
      else
        -- The help names the native surface; `headsep`/`footskip` stay
        -- accepted as the LaTeX spellings of `furnituregap` (read through
        -- the baseline-to-ink correction), and `textwidth`/`textheight`
        -- as geometry's spellings of the block size the native
        -- width/height + margin surface already covers — accepted, not
        -- advertised beside it.
        evs := evs.push (.say (Decl.unknownKey ctx.file "page" key
          (pageKeys.filter
            (!["headsep", "footskip", "textwidth", "textheight"].contains ·)) pos))
    -- Every failing arm above records a diagnostic, so a clean count means
    -- the entry applied: record it, and warn if it overwrote (W0343).
    if evs.size == before then
      evs := evs.push (.scalar "page" e.key (renderValue e.value) pos)
  return (spec, evs)

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
    (pos : Pos) : FontSpec × Array PEvent := Id.run do
  let mut spec := spec
  let mut evs : Array PEvent := #[]
  for e in entries do
    let before := evs.size
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
        spec := spec.declareFace variant f
      | some _, _ =>
        evs := evs.push (.say (Decl.wrongType ctx.file "fonts" key "a quoted face name" v pos))
      | none, _ =>
        if fontKeys.contains key then
          let expected := if key == "dir" then "a quoted directory" else "a quoted family name"
          evs := evs.push (.say (Decl.wrongType ctx.file "fonts" key expected v pos))
        else
          evs := evs.push (.say (Decl.unknownKey ctx.file "fonts" key
            (fontKeys ++ ["<slot>.upright/.bold/.italic/.bolditalic"]) pos))
    -- A family slot is a scalar; `dir` is a list and a dotted face is
    -- fontspec's own replace idiom, so only the families report an
    -- overwrite. The aliases fold onto the slot they name: `rm` after
    -- `body` is the same setting twice.
    if evs.size == before then
      let aliases := [("rm", "body"), ("sf", "sans"), ("tt", "mono")]
      let canonical := (aliases.lookup e.key).getD e.key
      if ["body", "sans", "mono", "math"].contains canonical then
        evs := evs.push (.scalar "fonts" canonical (renderValue e.value) pos)
  return (spec, evs)

def styleKeys : List String :=
  ["font", "before", "after", "rule", "marker", "indent", "gap",
   "align", "separator", "rule-above", "rule-above-skip", "rule-above-gap",
   "rule-below", "rule-below-gap", "rule-below-skip", "author-font",
   "author-strut", "hover", "focus", "motion"]

/-- `\style{element}{...}`: how an element kind looks. `font` and `marker`
are inline content and elaborate as such; the rest are lengths and a palette
colour. A length may name a token, so the entries are read one at a time
against the tokens declared so far. -/
private def applyStyle (ctx : Ctx) (styles : Styles) (element src : String) (pos : Pos) :
    EM Styles := do
  -- A `\define`d name is styleable too: the role survives as a class hook
  -- (`u-<name>` in HTML, `Block.role` on the page), so its rhythm and
  -- format are declared once, upstream, instead of leaking into every use
  -- site. Positional, like every declaration: the `\define` stands first.
  unless styleableElements.contains element || ctx.user.any (·.name == element) do
    -- The per-level list spellings are elided from the help (a family, not
    -- eleven names) to keep it inside the message-length lint.
    let named := styleableElements.filter fun e =>
      !(e.startsWith "itemize" && e != "itemize") &&
        !(e.startsWith "enumerate" && e != "enumerate")
    diag ctx .E0328 s!"'{element}' is not a styleable element or a '\\define'd name" pos
      (help := s!"elements: {String.intercalate ", " named}; \
a list level styles as itemize2..4 / enumerate2..4")
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
      | "rule-above" => st := { st with ruleAbove := ← asLength }
      | "rule-above-skip" => st := { st with ruleAboveSkip := ← asLength }
      | "rule-above-gap" => st := { st with ruleAboveGap := ← asLength }
      | "rule-below" => st := { st with ruleBelow := ← asLength }
      | "rule-below-gap" => st := { st with ruleBelowGap := ← asLength }
      | "rule-below-skip" => st := { st with ruleBelowSkip := ← asLength }
      | "author-font" => st := { st with authorFont := ← asInline }
      | "author-strut" => st := { st with authorStrut := ← asLength }
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
  noteDeclared ctx "style" element
  return styles.declare element st

/-- `\chrome{ footer = { left = \sectiontitle, right = \framenumber } }`:
page furniture as declared data. A slot names a per-page datum the engine
supplies — the current section's title, or the frame's own number — never
literal content (that is `\runningfoot`, which overrides the whole footer).
Redeclaring merges per slot onto the chrome already declared — across
blocks exactly as within one, and onto a theme's default exactly as a
`\palette` entry overrides the theme's — so a second block refines the slot
it names and leaves its sibling standing. -/
private def applyChrome (ctx : Ctx) (c0 : Chrome) (src : String) (pos : Pos) :
    Chrome × Array PEvent := Id.run do
  let mut chrome : Chrome := c0
  let mut evs : Array PEvent := #[]
  let slotHelp := "slots are \\sectiontitle, \\framenumber, or \\framefraction"
  let say (evs : Array PEvent) (code : DiagCode) (msg : String)
      (help : Option String := none) : Array PEvent :=
    evs.push (.say (diagOf ctx code msg (some pos) help))
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | none =>
      evs := say evs .E0320 s!"invalid entry in '\\chrome': {entry.quote}"
        (help := "entries look like: footer = { left = \\sectiontitle, right = \\framenumber }")
    | some (key, valueSrc) =>
      if key == "footer" then
        match Decl.parseValue valueSrc with
        | some (.block inner) =>
          for slotEntry in Decl.splitEntries inner do
            match Decl.splitEntry slotEntry with
            | none =>
              evs := say evs .E0320 s!"invalid entry in '\\chrome' footer: {slotEntry.quote}"
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
                evs := say evs .E0321
                  s!"cannot read the '\\chrome' footer slot '{slotKey}': {slotVal.quote}"
                  (help := slotHelp)
              | some d =>
                match slotKey with
                | "left" =>
                  evs := evs.push (.scalar "chrome" "footer.left" s!"\\{d.label}" pos)
                  evs := evs.push (.declared "chrome" "footer.left")
                  chrome := { chrome with footerLeft := some d }
                | "right" =>
                  evs := evs.push (.scalar "chrome" "footer.right" s!"\\{d.label}" pos)
                  evs := evs.push (.declared "chrome" "footer.right")
                  chrome := { chrome with footerRight := some d }
                | _ =>
                  evs := evs.push (.say (Decl.unknownKey
                    ctx.file "chrome footer" slotKey ["left", "right"] pos))
        | some v =>
          evs := evs.push (.say (Decl.wrongType
            ctx.file "chrome" key
            "a block like { left = \\sectiontitle, right = \\framenumber }" v pos))
        | none =>
          evs := say evs .E0321 s!"cannot read value for 'footer' in '\\chrome': {valueSrc.quote}"
            (help := "footer = { left = \\sectiontitle, right = \\framenumber }")
      else
        evs := evs.push (.say (Decl.unknownKey ctx.file "chrome" key ["footer"] pos))
  return (chrome, evs)

/-- `\output{...}`: what to build, so a document needs no CLI options.
`formats` takes a bare comma list (`formats = pdf, html`), so entries are
walked by hand: an entry without `=` continues the list. -/
private def applyOutput (ctx : Ctx) (o0 : OutputSpec) (src : String) (pos : Pos) :
    OutputSpec × Array PEvent := Id.run do
  let mut o := o0
  let mut evs : Array PEvent := #[]
  let mut inFormats := false
  let say (evs : Array PEvent) (code : DiagCode) (msg : String)
      (help : Option String := none) : Array PEvent :=
    evs.push (.say (diagOf ctx code msg (some pos) help))
  let addFormat (o : OutputSpec) (evs : Array PEvent) (f : String) :
      OutputSpec × Array PEvent :=
    if ["pdf", "html", "md"].contains f then
      (o.addFormat f, evs)
    else
      (o, say evs .E0321 s!"'{f}' is not an output format"
        (help := "formats: pdf, html, md"))
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | some ("formats", v) =>
      inFormats := true
      let (o', evs') := addFormat o evs v
      o := o'
      evs := evs'
    | some ("css", v) =>
      inFormats := false
      if ["own", "bulma", "none"].contains v then
        o := { o with css := some v }
        evs := evs.push (.scalar "output" "css" v pos)
      else
        evs := say evs .E0321 s!"'{v}' is not a stylesheet mode"
          (help := "css: own, bulma, none")
    | some ("stylesheet", v) =>
      inFormats := false
      -- A path is a string; the quotes other declarations require are
      -- accepted but not demanded, as `formats` entries are bare too.
      let v := if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then
          String.ofList (v.toList.drop 1).dropLast
        else v
      o := { o with stylesheet := some v }
      evs := evs.push (.scalar "output" "stylesheet" v pos)
    | some ("md", v) =>
      inFormats := false
      let v := if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then
          String.ofList (v.toList.drop 1).dropLast
        else v
      o := { o with md := some v }
      evs := evs.push (.scalar "output" "md" v pos)
    | some (key, _) =>
      inFormats := false
      evs := evs.push (.say (Decl.unknownKey ctx.file "output" key
        ["formats", "css", "stylesheet", "md"] pos))
    | none =>
      if inFormats then
        let (o', evs') := addFormat o evs entry
        o := o'
        evs := evs'
      else
        evs := say evs .E0320 s!"invalid entry in '\\output': {entry.quote}"
          (help := some "entries look like: formats = pdf, html")
  return (o, evs)

/-- `\pdfmeta{...}`: PDF document information. -/
private def applyMeta (ctx : Ctx) (m0 : Meta) (entries : Array Decl.Entry)
    (pos : Pos) : Meta × Array PEvent := Id.run do
  let mut m := m0
  let mut evs : Array PEvent := #[]
  for e in entries do
    let before := evs.size
    match e.key, e.value with
    | "title", .str s => m := { m with title := some s }
    | "language", .str s =>
      -- Stored as declared — both artifacts carry the author's tag even
      -- when no locale record ships; the data fallback is named here.
      if (Locale.forTag s).isNone then
        evs := evs.push (.say (Diag.of .W0368
          s!"no locale for language '{s}'; English captions and patterns stand in" (some ⟨ctx.file, pos⟩)
          (help := some "the engine ships locale records for: en, fr, de")))
      m := { m with language := some s }
    | "author", .str s => m := { m with author := some s }
    | "subject", .str s => m := { m with subject := some s }
    | "keywords", .str s => m := { m with keywords := some s }
    | "url", .str s => m := { m with url := some s }
    | "image", .str s => m := { m with image := some s }
    | "favicon", .str s => m := { m with favicon := some s }
    | key, v =>
      if metaKeys.contains key then
        evs := evs.push (.say (Decl.wrongType ctx.file "pdfmeta" key "a string" v pos))
      else
        evs := evs.push (.say (Decl.unknownKey ctx.file "pdfmeta" key metaKeys pos))
    if evs.size == before then
      evs := evs.push (.scalar "pdfmeta" e.key (renderValue e.value) pos)
  return (m, evs)

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
private def parseAssert (ctx : Ctx) (src : String) (pos : Pos) :
    Option Assertion × Array PEvent :=
  let words := (src.splitOn " ").filterMap fun w =>
    let t := w.trimAscii.toString
    if t.isEmpty then none else some t
  let fail (why : String) : Option Assertion × Array PEvent :=
    (none, #[.say (diagOf ctx .E0325
      s!"cannot read assertion: {src.trimAscii.toString.quote}" (some pos)
      (help := some why))])
  match words with
  | ["fonts.all_embedded"] =>
    (some { kind := .fontsAllEmbedded, span := some ⟨ctx.file, pos⟩ }, #[])
  | ["text.in_area"] =>
    (some { kind := .textInArea, span := some ⟨ctx.file, pos⟩ }, #[])
  | ["text.xheight", ">=", v] =>
    match Decl.parseValue v with
    | some (.dim d) => (some { kind := .minXHeight d, span := some ⟨ctx.file, pos⟩ }, #[])
    | _ => fail s!"'{v}' is not a dimension (like 1.4mm)"
  | ["pages", op, n] =>
    match cmpOp op, n.toInt? with
    | some o, some v => (some { kind := .pages o v, span := some ⟨ctx.file, pos⟩ }, #[])
    | none, _ => fail s!"'{op}' is not a comparison (== != <= < >= >)"
    | _, none => fail s!"'{n}' is not a whole number"
  | _ => fail "supported forms: pages <op> N, fonts.all_embedded, text.in_area, text.xheight >= <len>"

/-- One scanned preamble declaration: the value `applyDecl` folds over and
the commutation statement (T1) quantifies over. Scanning is segmentation
only — payloads stay raw (token runs, block sources): content elaborates at
apply time, where the context (user commands, palette, tokens) is the one
the declaration stands after, because reference→referent order is real and
stays sequential. Malformation facts met while finding extents (an unclosed
`[`, a missing group) ride as data, so `applyDecl` owns every diagnostic
and emits it in scan order. -/
inductive PDecl where
  | docclass (options : Option String) (cls : Option String) (pos : Pos)
  | defineCmd (decl : Array Raw) (pos : Pos)
  | defineEnv (name : Option (String × Pos)) (sig : String)
      (beginB : Option (Array Raw)) (endB : Option (Array Raw)) (pos : Pos)
  | fileMark (f : String)
  | running (name : String) (opts : Option (Array Raw))
      (body : Option (Array Raw)) (pos : Pos)
  | logo (body : Option (Array Raw)) (pos : Pos)
  | palette (opts : Option (Array Raw)) (body : Option String) (pos : Pos)
  | style (args : Option (String × String)) (pos : Pos)
  | allow (body : Option String) (pos : Pos)
  | theme (src : Option String) (pos : Pos)
  | assert (src : Option String) (pos : Pos)
  | output (src : Option String) (pos : Pos)
  | tokens (src : Option String) (pos : Pos)
  | chrome (src : Option String) (pos : Pos)
  | page (src : Option String) (pos : Pos)
  | fonts (src : Option String) (pos : Pos)
  | pdfmeta (src : Option String) (pos : Pos)
  | captionsetup (unclosed : Option Pos) (body : Option String) (pos : Pos)
  | titleDecl (name : String) (unclosed : Option Pos) (recovered : Bool)
      (body : Option (Array Raw)) (pos : Pos)
  | reserved (name : String) (code : DiagCode) (unclosed : Option Pos) (pos : Pos)
  | unknownCmd (name : String) (unclosed : Option Pos) (pos : Pos)
  | stray

/-- The preamble fold's threaded state: exactly the loop-local values the
imperative scanner carried, as a value `applyDecl` maps. `textDiagged` is
the E0313 once-latch — reporting machinery, beside ESt's diags,
`warnedUnknown`, `seenScalars`, and `declaredKeys`: the commutation
statement's projection excludes these four and nothing else, because their
only readers are diagnostic sites. -/
structure PreState where
  ctx : Ctx
  docClass : Ir.DocClass := .article
  sawClass : Bool := false
  classOptions : String := ""
  page : PageSpec := {}
  sawPage : Bool := false
  fonts : FontSpec := {}
  palette : Palette := {}
  tokens : Tokens := {}
  head : Option (Array Inline) := none
  foot : Option (Array Inline) := none
  headFrom : Nat := 1
  footFrom : Nat := 1
  styles : Styles := {}
  chrome : Chrome := {}
  chromeDeclared : Bool := false
  info : Meta := {}
  output : OutputSpec := {}
  asserts : Array Assertion := #[]
  allow : Array String := #[]
  textDiagged : Bool := false
  /-- The document wrote `\theme{...}` — any spelling, known or not: the
  author's choice stands and the class default steps aside. -/
  sawTheme : Bool := false

/-- Segment the preamble into declaration values. Pure and positional: the
same argument extents the imperative loop walked (`skipSpaces`,
`scanBracketArg`, group taking, `skipReservedArgs`), including its recovery
quirks — a declaration whose group never materialises consumes only what
the loop consumed, and the tokens it looked past rescan as their own units,
exactly as they always did. `\input` wrappers splice open in place between
file markers, so a value's diagnostics name the file that holds it. -/
def scanDecls (file : String) (pre : Array Raw) : Array PDecl := Id.run do
  let mut preamble := pre
  let mut curFile := file
  let mut out : Array PDecl := #[]
  let mut i : Nat := 0
  repeat
    if h : i < preamble.size then
      let r := preamble[i]
      if let .env n wrapped pos := r then
        if let some f := Parse.inputEnvFile? n then
          preamble := preamble.extract 0 i ++
            #[Raw.ctrl (fileMarker f) pos] ++ wrapped ++
            #[Raw.ctrl (fileMarker curFile) pos] ++
            preamble.extract (i + 1) preamble.size
          continue
      match r with
      | .space => i := i + 1
      | .par _ => i := i + 1
      | .ctrl "documentclass" pos =>
        i := i + 1
        let mut j := skipSpaces preamble i
        let mut options : Option String := none
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
          options := some (rawSrc opts)
          j := skipSpaces preamble j
        match preamble[j]? with
        | some (.group nameRaws _) =>
          i := j + 1
          out := out.push (.docclass options
            (some ((rawSrc nameRaws).trimAscii.toString)) pos)
        | _ =>
          out := out.push (.docclass options none pos)
      | .ctrl "define" pos =>
        i := i + 1
        let j := skipSpaces preamble i
        match preamble[j]? with
        | some (.ctrl _ _) =>
          let mut k := j + 1
          for _ in [k:preamble.size] do
            match preamble[k]? with
            | some (.group _ _) =>
              k := k + 1
              break
            | some _ => k := k + 1
            | none => break
          out := out.push (.defineCmd (preamble.extract i k) pos)
          i := k
        | _ =>
          out := out.push (.defineCmd (preamble.extract i (j + 1)) pos)
          i := j + 1
      | .ctrl "defineenv" pos =>
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
          out := out.push (.defineEnv (some (envName, npos)) (rawSrc sigRaws)
            beginRaws endRaws pos)
        | _ =>
          out := out.push (.defineEnv none "" none none pos)
          i := j + 1
      | .ctrl name pos =>
        i := i + 1
        if let some f := fileMarkerFile? name then
          curFile := f
          out := out.push (.fileMark f)
        else if runningCtrl.contains name then
          let mut j := skipSpaces preamble i
          let mut opts : Option (Array Raw) := none
          if let some (.sym '[' _) := preamble[j]? then
            let mut opt : Array Raw := #[]
            let mut k := j + 1
            for _ in [k:preamble.size + 1] do
              match preamble[k]? with
              | some (.sym ']' _) => k := k + 1; break
              | some r => opt := opt.push r; k := k + 1
              | none => break
            opts := some opt
            j := skipSpaces preamble k
          match preamble[j]? with
          | some (.group body _) =>
            i := j + 1
            out := out.push (.running name opts (some body) pos)
          | _ =>
            out := out.push (.running name opts none pos)
        else if name == "logo" then
          let j := skipSpaces preamble i
          match preamble[j]? with
          | some (.group body _) =>
            i := j + 1
            out := out.push (.logo (some body) pos)
          | _ =>
            out := out.push (.logo none pos)
        else if name == "palette" then
          let mut j := skipSpaces preamble i
          let mut opts : Option (Array Raw) := none
          if let some (.sym '[' _) := preamble[j]? then
            let mut opt : Array Raw := #[]
            let mut k := j + 1
            for _ in [k:preamble.size + 1] do
              match preamble[k]? with
              | some (.sym ']' _) => k := k + 1; break
              | some r => opt := opt.push r; k := k + 1
              | none => break
            opts := some opt
            j := skipSpaces preamble k
          match preamble[j]? with
          | some (.group body _) =>
            i := j + 1
            out := out.push (.palette opts (some (rawSrc body)) pos)
          | _ =>
            out := out.push (.palette opts none pos)
        else if name == "style" then
          let j := skipSpaces preamble i
          let j2 := skipSpaces preamble (j + 1)
          match preamble[j]?, preamble[j2]? with
          | some (.group elem _), some (.group body _) =>
            i := j2 + 1
            out := out.push (.style (some (rawSrc elem, rawSrc body)) pos)
          | _, _ =>
            out := out.push (.style none pos)
        else if name == "allow" then
          let j := skipSpaces preamble i
          match preamble[j]? with
          | some (.group body _) =>
            i := j + 1
            out := out.push (.allow (some (rawSrc body)) pos)
          | _ =>
            out := out.push (.allow none pos)
        else if declCtrl.contains name then
          let j := skipSpaces preamble i
          let src : Option String := match preamble[j]? with
            | some (.group body _) => some (rawSrc body)
            | _ => none
          if src.isSome then
            i := j + 1
          match name with
          | "theme" => out := out.push (.theme src pos)
          | "assert" => out := out.push (.assert src pos)
          | "output" => out := out.push (.output src pos)
          | "tokens" => out := out.push (.tokens src pos)
          | "chrome" => out := out.push (.chrome src pos)
          | "page" => out := out.push (.page src pos)
          | "fonts" => out := out.push (.fonts src pos)
          | _ => out := out.push (.pdfmeta src pos)
        else if name == "captionsetup" then
          let mut j := i
          let mut unclosed : Option Pos := none
          match scanBracketArg preamble j pos with
          | .took j' => j := j'
          | .unclosed bpos => unclosed := some bpos
          | .content => pure ()
          j := skipSpaces preamble j
          match preamble[j]? with
          | some (.group gbody _) =>
            i := j + 1
            out := out.push (.captionsetup unclosed (some (rawSrc gbody)) pos)
          | _ =>
            out := out.push (.captionsetup unclosed none pos)
        else if titleCtrls.contains name then
          let (j, recovered, _, unclosed) := scanOptArg preamble i pos
          match preamble[j]? with
          | some (.group b _) =>
            i := j + 1
            out := out.push (.titleDecl name unclosed recovered (some b) pos)
          | _ =>
            out := out.push (.titleDecl name unclosed recovered none pos)
            if recovered then
              i := j
        else if let some code := reservedCtrl.lookup name then
          let (j, unclosed) := skipReservedArgs preamble i pos
          match unclosed with
          | some bpos =>
            out := out.push (.reserved name code (some bpos) pos)
            i := skipMalformedArgs preamble i pos
          | none =>
            out := out.push (.reserved name code none pos)
            i := j
        else
          -- TeX's register assignment (`\widowpenalty=10000`,
          -- `\parindent=\z@`) is one construct: the `=` and its value go
          -- with the skipped name, never left behind as stray content.
          let j0 := skipSpaces preamble i
          match preamble[j0]? with
          | some (.sym '=' _) =>
            let j1 := skipSpaces preamble (j0 + 1)
            match preamble[j1]? with
            | some (.word _ _) | some (.ctrl _ _) => i := j1 + 1
            | _ => i := j0 + 1
          | some (.word w _) =>
            if w.startsWith "=" then i := j0 + 1
          | _ => pure ()
          let (j, unclosed) := skipReservedArgs preamble i pos (maxGroups := 9)
          match unclosed with
          | some bpos =>
            out := out.push (.unknownCmd name (some bpos) pos)
            i := skipMalformedArgs preamble i pos
          | none =>
            out := out.push (.unknownCmd name none pos)
            i := j
      | _ =>
        i := i + 1
        out := out.push .stray
    else
      break
  return out

/-- `\allow{W0307, E0502}`: the document accepts the named losses. The
teeth: an unknown code is an error (a typo must not grant a silent
blanket), an entry that never fires warns (Main), and the acceptance always
prints in the build summary. -/
private def applyAllow (ctx : Ctx) (allow : Array String) (src : String) (pos : Pos) :
    Array String × Array PEvent := Id.run do
  let mut allow := allow
  let mut evs : Array PEvent := #[]
  for entry in src.splitOn "," do
    let code := entry.trimAscii.toString
    if code.isEmpty then continue
    match DiagCode.ofString? code with
    | some c =>
      unless allow.contains c.code do
        allow := allow.push c.code
    | none =>
      evs := evs.push (.say (diagOf ctx .E0329
        s!"'\\allow' names no diagnostic code '{code}'" (some pos)
        (help := "codes look like 'E0333'; each names the one loss it accepts")))
  return (allow, evs)

/-- One keyed apply step, finished: fulfil its reporting events and return
its value. Every keyed `applyDecl` arm is `stepDone` of a pure step — the
shape T1's proof reads, one run lemma for all seven heads. -/
private def stepDone (ctx : Ctx) (r : PreState × Array PEvent) : EM PreState := do
  emitEvents ctx r.2
  return r.1

private def stepPage (s : PreState) (src : String) (pos : Pos) :
    PreState × Array PEvent :=
  let pb := Decl.parseBlock s.ctx.file src pos "page" s.tokens.entries
  let pe := applyPage s.ctx s.page pb.1 pos
  -- Only geometry keys claim the page: `\page{ parskip = ... }` keeps the
  -- Bringhurst default margin standing (≈ the `!sawPage` branch after the
  -- fold).
  ({ s with
      page := pe.1
      sawPage := pb.1.any (pageGeometryKeys.contains ·.key) || s.sawPage },
   pb.2.map .say ++ pe.2)

private def stepFonts (s : PreState) (src : String) (pos : Pos) :
    PreState × Array PEvent :=
  let pb := Decl.parseBlock s.ctx.file src pos "fonts" s.tokens.entries
  let fe := applyFonts s.ctx s.fonts pb.1 pos
  ({ s with fonts := fe.1 }, pb.2.map .say ++ fe.2)

private def stepPdfmeta (s : PreState) (src : String) (pos : Pos) :
    PreState × Array PEvent :=
  let pb := Decl.parseBlock s.ctx.file src pos "pdfmeta" s.tokens.entries
  let me := applyMeta s.ctx s.info pb.1 pos
  ({ s with info := me.1 }, pb.2.map .say ++ me.2)

/-- Parses its own entries: `formats` is a bare comma list, which a generic
key/value pre-parse would break apart. -/
private def stepOutput (s : PreState) (src : String) (pos : Pos) :
    PreState × Array PEvent :=
  let oe := applyOutput s.ctx s.output src pos
  ({ s with output := oe.1 }, oe.2)

/-- Parses its own entries: slot values are `\sectiontitle` spellings a
key/value pre-parse would reject. Inert chrome would be a silent failure —
only slides draw it — so the step also says W0318 off the slides class;
declaring the block names what the footer band holds (`chromeDeclared`,
read by `footerSequenceDiags`). -/
private def stepChrome (s : PreState) (src : String) (pos : Pos) :
    PreState × Array PEvent :=
  let ce := applyChrome s.ctx s.chrome src pos
  ({ s with chrome := ce.1, chromeDeclared := true },
   ce.2 ++ (if !s.docClass.record.chrome then
     #[.say (diagOf s.ctx .W0318
       s!"'\\chrome' is slides furniture; the {s.docClass.name} class never draws it"
       (some pos) (help := "\\runninghead / \\runningfoot are the page furniture"))]
   else #[]))

private def stepAssert (s : PreState) (src : String) (pos : Pos) :
    PreState × Array PEvent :=
  let pa := parseAssert s.ctx src pos
  ({ s with asserts :=
      match pa.1 with
      | some a => s.asserts.push a
      | none => s.asserts },
   pa.2)

private def stepAllow (s : PreState) (src : String) (pos : Pos) :
    PreState × Array PEvent :=
  let ae := applyAllow s.ctx s.allow src pos
  ({ s with allow := ae.1 }, ae.2)

/-- The E0304 a keyed head without its `{...}` block earns, as a step. -/
private def stepMissing (s : PreState) (name : String) (what : String) (pos : Pos) :
    PreState × Array PEvent :=
  (s, #[.say (diagOf s.ctx .E0304 s!"'\\{name}' needs {what}" (some pos))])

/-- Apply one declaration to the fold state: the imperative loop's arm
bodies over a value, one arm per constructor, no wildcard. Every diagnostic
the loop emitted is emitted here, in the same order — the scan owns extents
only. The preamble IS `foldlM applyDecl` over `scanDecls`' values; the
commutation statement ranges over exactly this function. -/
def applyDecl (s : PreState) (d : PDecl) : EM PreState := do
  match d with
  | .docclass options cls pos =>
    let s := { s with sawClass := true }
    let s := match options with
      | some o => { s with classOptions := o }
      | none => s
    match cls with
    | some named =>
      match Ir.DocClass.ofString? named with
      | some c => return { s with docClass := c }
      | none =>
        diag s.ctx .E0309 s!"unknown document class '{named}'" pos
          (help := "classes: article, slides, card, resume, webpage")
        return s
    | none =>
      diag s.ctx .E0304 "'\\documentclass' needs a {class}" pos
      return s
  | .defineCmd decl pos =>
    -- Through `takeDefine`, the one door the body arm uses too: the
    -- validation (W0303, E0303, the signature grammar) cannot drift
    -- between the two positions. The scan carried the declaration's own
    -- token run; the extent is the scan's, so the returned index is not
    -- read here.
    let ⟨(cmd?, _), _⟩ ← takeDefine s.ctx decl 0 pos
    if let some cmd := cmd? then
      if let some (lvl, parts) := secFmtDefine? cmd then
        -- Not a macro: a heading-number format declaration, the same
        -- interception as the body walk's define arm.
        applySecFmt lvl parts
        return s
    let cmd? ← match cmd? with
      | some cmd => do
        if (← gateRedefB s.ctx cmd) then pure (some cmd) else pure none
      | none => pure none
    match cmd? with
    | some cmd =>
      -- The same boundary insertion as the body walk's define arm
      -- (`bindCmd`): at the preamble top level `limit` equals the array's
      -- size and this is a plain push, but the spelling keeps visibility
      -- monotone wherever the fold runs.
      return { s with ctx := bindCmd s.ctx cmd }
    | none => return s
  | .defineEnv name sig beginB endB pos =>
    match name with
    | some (envName, npos) =>
      if builtinEnvNames.contains envName then
        -- Rule (b)'s remainder for environments: the abstract's refused
        -- redefinition may still declare the built-in's appearance —
        -- `\large\bf` and `\centerline` are read as `\style{abstract}`
        -- keys, merged under anything the document declared itself, and
        -- the W0303 gains W0361's clause naming what survived.
        let est := if envName == "abstract" then
            beginB.bind fun b => envStyleInterpret (envStyleScanList {} b.toList)
          else none
        modify fun st => { st with diags := st.diags.push (Diag.of .W0303
          (if est.isSome then
            s!"'\{{envName}}' is built in; this definition is ignored, its declarations styling the built-in"
          else
            s!"'\{{envName}}' is built in; this definition is ignored")
          (some ⟨s.ctx.file, npos⟩)
          (help := "the built-in already does this; \\define it under another name")) }
        match est with
        | some est =>
          let merged := Theme.styleMerge ((s.styles.find? "abstract").getD {}) est
          return { s with styles := s.styles.declare "abstract" merged }
        | none => return s
      else
        match beginB, endB with
        | some b, some e =>
          let params ← parseSig s.ctx sig pos
          return { s with ctx := { s.ctx with
            userEnvs := s.ctx.userEnvs.push
              ⟨envName, params, trimRaws b, trimRaws e, s.ctx.limit⟩
            envLimit := s.ctx.userEnvs.size + 1 } }
        | _, _ =>
          diag s.ctx .E0303 s!"'\\defineenv \{{envName}}' needs \{begin} and \{end}" pos
          return s
    | none =>
      diag s.ctx .E0303 "expected '\\defineenv {name}(...) {begin} {end}'" pos
      return s
  | .fileMark f =>
    return { s with ctx := { s.ctx with file := f } }
  | .running name opts body pos =>
    -- `[from = 2]` keeps the opening page clean, as a title page is.
    -- The option is this declaration's own: it gates the head or foot
    -- it rides on, never the sibling's, and a redeclaration without
    -- it resets the gate — a replace is whole, options included.
    let mut fromPage : Nat := 1
    if let some opt := opts then
      for e in Decl.splitEntries (rawSrc opt) do
        match Decl.splitEntry e with
        | some ("from", v) =>
          match v.trimAscii.toString.toNat? with
          | some n => fromPage := n
          | none => diag s.ctx .E0321 s!"'from' needs a page number, got {v.quote}" pos
        | _ =>
          diag s.ctx .E0320 s!"unknown option in \\{name}: {e.quote}" pos
            (help := "options: from = <page>")
    match body with
    | some b =>
      let content ← elabInlines s.ctx b
      -- The gate-only spelling: `\runningfoot[from = 2]{}` moves the run's
      -- start without declaring a line — `\thispagestyle{empty}`'s carrier
      -- (its page-1 form: this-page-only and from-page-2 coincide when the
      -- override is the opening page's). It only defers — a declaration's
      -- own later `from` stands (max) — and it never touches content, so
      -- it cannot clear a declared line or suppress the class default.
      if content.isEmpty then
        if name == "runninghead" then
          return { s with headFrom := max s.headFrom fromPage }
        else
          return { s with footFrom := max s.footFrom fromPage }
      -- The whole declaration is one scalar: a second one replaces
      -- the first, said aloud when their content differs (the same
      -- store W0343's keyed sites use; a byte-identical repeat is
      -- silent).
      let raw := (rawSrc b).trimAscii.toString
      let store := (← get).seenScalars
      if let some prev := store.find? (fun e => e.1 == name && e.2.1 == "content") then
        if prev.2.2 != raw then
          diag s.ctx .W0343 s!"a second '\\{name}' replaces the first" (some pos)
            (help := s!"one '\\{name}' declares the line; delete the one you do not mean")
      let store := (store.filter fun e => !(e.1 == name && e.2.1 == "content"))
      let store := store.push (name, "content", raw)
      modify fun st => { st with seenScalars := store }
      if name == "runninghead" then
        return { s with head := some content, headFrom := fromPage }
      else
        return { s with foot := some content, footFrom := fromPage }
    | none =>
      diag s.ctx .E0304 s!"'\\{name}' needs one group of inline content" pos
      return s
  | .logo body pos =>
    -- beamer's `\logo{...}`: one piece of inline content — normally an
    -- image — placed at the lower-right corner of every page carrying
    -- running content. The image inside is the same node
    -- `\includegraphics` makes; only the placement is the deck's.
    match body with
    | some b =>
      let content ← elabInlines s.ctx b
      modify fun st => { st with
        logo := if content.isEmpty then none else some content }
      return s
    | none =>
      diag s.ctx .E0304 "'\\logo' needs one group of inline content" pos
      return s
  | .palette opts body pos =>
    -- `\palette[decorative]{...}`: the block's entries are declared
    -- deliberately low-contrast and exempt from the pairing check. An
    -- unrecognised option skips the block rather than applying it as
    -- the base palette -- a variant block applied as base would
    -- silently restyle the document.
    let mut decorative := false
    let mut skipBlock := false
    if let some opt := opts then
      for e in Decl.splitEntries (rawSrc opt) do
        if e == "decorative" then
          decorative := true
        else
          diag s.ctx .W0316 s!"unknown option in '\\palette': {e.quote}; block skipped" pos
            (help := "options: decorative")
          skipBlock := true
    match body with
    | some src =>
      if skipBlock then
        return s
      else
        let pal ← applyPalette s.ctx s.palette src pos (decorative := decorative)
        return { s with palette := pal, ctx := { s.ctx with palette := pal } }
    | none =>
      diag s.ctx .E0304 "'\\palette' needs a {...} block" pos
      return s
  | .style args pos =>
    match args with
    | some (elem, body) =>
      let styles ← applyStyle s.ctx s.styles elem body pos
      return { s with styles := styles }
    | none =>
      diag s.ctx .E0304 "'\\style' needs {element} and a {...} block" pos
      return s
  | .allow (some src) pos => stepDone s.ctx (stepAllow s src pos)
  | .allow none pos =>
    stepDone s.ctx (stepMissing s "allow" "a {...} block of diagnostic codes" pos)
  | .theme src pos =>
    match src with
    | some src =>
      let s := { s with sawTheme := true }      -- A theme is a named bundle of typed values, installed here
      -- through the same replace-on-redeclare door the document's
      -- own declarations use. Everything after this site overrides:
      -- the theme is a default, never a lock. The install itself is
      -- `Theme.apply` — values in, values out; this site only
      -- threads the result back into the fold's state.
      let tname := src.trimAscii.toString
      -- beamer's own `\usetheme{default}` is the base look: no bundle
      -- installs, and the class default (the slides `daylight` install)
      -- steps aside — the author chose bareness by name.
      if tname == "default" then
        return s
      match Theme.find? tname with
      | some th =>
        -- The class gates whether furniture draws; the theme only
        -- supplies its values. A bundle whose chrome or slides
        -- furniture styles land under a class that never draws
        -- them would be silently inert, so the install says so —
        -- the document's own `\chrome` has its own name (W0318).
        if !s.docClass.record.chrome then
          let inert := (if th.chrome.hasFooter then ["chrome"] else []) ++
            ["frametitle", "sectionpage", "standout"].filter
              (fun e => (th.styles.find? e).isSome)
          unless inert.isEmpty do
            diag s.ctx .W0355
              (s!"theme '{tname}' installs slides furniture " ++
                s!"({String.intercalate ", " inert}); " ++
                s!"the {s.docClass.name} class never draws it")
              (some pos)
              (help := "the palette and tokens apply either way; \
\\documentclass{slides} draws the furniture")
        let before : Theme.Decls :=
          { palette := s.palette, tokens := s.tokens
            styles := s.styles, chrome := s.chrome }
        -- A theme replacing a key the document already declared is
        -- almost certainly an ordering mistake, not an intent: the
        -- positional rule says the theme wins, so say so (W0348).
        -- Judged against what the DOCUMENT declared — a value
        -- standing from an earlier bundle warns nothing.
        for (kind, key) in Theme.replaces th before do
          if (← get).declaredKeys.contains (kind, key) then
            diag s.ctx .W0348
              s!"theme '{tname}' replaces the document's earlier '{key}' from '\\{kind}'"
              (some pos)
              (help := "overrides go after '\\theme': move the declaration below it")
        -- The keys the bundle installs now stand from it, not from
        -- the document, whatever they replaced.
        let installed := Theme.declares th
        modify fun st => { st with
          declaredKeys := st.declaredKeys.filter (fun e => !installed.contains e) }
        let ds := Theme.apply th before
        return { s with
          palette := ds.palette
          tokens := ds.tokens
          styles := ds.styles
          chrome := ds.chrome
          ctx := { s.ctx with palette := ds.palette, tokens := ds.tokens } }
      | none =>
        diag s.ctx .W0319 s!"unknown theme '{tname}'; the document is unthemed"
          (some pos)
          (help := s!"themes: {String.intercalate ", " Theme.names}")
        return s
    | none =>
      diag s.ctx .E0304 "'\\theme' needs a {...} block" pos
      return s
  | .assert (some src) pos => stepDone s.ctx (stepAssert s src pos)
  | .assert none pos => stepDone s.ctx (stepMissing s "assert" "a {...} block" pos)
  | .output (some src) pos => stepDone s.ctx (stepOutput s src pos)
  | .output none pos => stepDone s.ctx (stepMissing s "output" "a {...} block" pos)
  | .tokens src pos =>
    match src with
    | some src =>
      -- Parses its own entries one at a time; a generic pre-parse
      -- would reject `0.6 * rhythm` before the reference resolves.
      let tk ← applyTokens s.ctx s.tokens src pos
        (engine := engineLengthTokens s.docClass s.classOptions s.page)
      return { s with tokens := tk, ctx := { s.ctx with tokens := tk } }
    | none =>
      diag s.ctx .E0304 "'\\tokens' needs a {...} block" pos
      return s
  | .chrome (some src) pos => stepDone s.ctx (stepChrome s src pos)
  | .chrome none pos => stepDone s.ctx (stepMissing s "chrome" "a {...} block" pos)
  | .page (some src) pos => stepDone s.ctx (stepPage s src pos)
  | .page none pos => stepDone s.ctx (stepMissing s "page" "a {...} block" pos)
  | .fonts (some src) pos => stepDone s.ctx (stepFonts s src pos)
  | .fonts none pos => stepDone s.ctx (stepMissing s "fonts" "a {...} block" pos)
  | .pdfmeta (some src) pos => stepDone s.ctx (stepPdfmeta s src pos)
  | .pdfmeta none pos => stepDone s.ctx (stepMissing s "pdfmeta" "a {...} block" pos)
  | .captionsetup unclosed body pos =>
    -- The caption package's option interface (caption manual §2–4).
    -- `position`/`tableposition`/`figureposition` declare which side
    -- captions will stand on, so the package can put the skip
    -- between caption and object (§2.2: the option does not move
    -- the caption — placement stays source order there too). This
    -- engine binds `captionsep` to the object side of a caption
    -- wherever the source puts it, so those declarations already
    -- hold. `skip` is that gap's own value (caption manual §2.2:
    -- `skip=` sets `\abovecaptionskip`, the object-side skip), so a
    -- literal length declares the `captionsep` token. Every other
    -- key — and a `skip` whose value is a TeX length register the
    -- engine does not resolve — is named and ignored (W0354), one
    -- warning per key. The `[float type]` scope changes nothing in
    -- that judgment, so it is skipped.
    if let some bpos := unclosed then
      warnUnclosed s.ctx "'\\captionsetup'" bpos
    match body with
    | some src =>
      let mut s := s
      for entry in src.splitOn "," do
        let parts := entry.splitOn "="
        let key := (parts.headD "").trimAscii.toString
        if key.isEmpty then continue
        let honouredSkip ← do
          if key == "skip" then
            let value := (String.intercalate "=" (parts.drop 1)).trimAscii.toString
            match Decl.parseGlue value with
            | some g =>
              let tokens := s.tokens.declare "captionsep" g
              s := { s with tokens := tokens, ctx := { s.ctx with tokens := tokens } }
              noteDeclared s.ctx "tokens" "captionsep"
              pure true
            | none => pure false
          else pure false
        unless honouredSkip ||
            ["position", "tableposition", "figureposition"].contains key do
          warnOnce s.ctx ("captionsetup:" ++ key) .W0354
            s!"'\\captionsetup' key '{key}' is not honoured; the caption keeps \
its declared layout" pos
            (help := "\\tokens{ captionsep = ... } declares the caption gap")
      return s
    | none =>
      diag s.ctx .E0304 "'\\captionsetup' needs a {key = value} block" pos
      return s
  | .titleDecl name unclosed recovered body pos =>
    -- A declaration-only position: the malformed run is dropped with
    -- W0310 already pointing at it — the preamble has no content.
    if let some bpos := unclosed then
      warnUnclosed s.ctx s!"'\\{name}'" bpos
    match body with
    | some b =>
      let content ← elabInlines s.ctx b
      modify fun st => match name with
        | "title" => { st with title := some content }
        | "subtitle" => { st with subtitle := some content }
        | "author" => { st with author := some content }
        | "institute" => { st with institute := some content }
        | _ => { st with date := some content }
      return s
    | none =>
      if recovered then
        warnSkippedDecl s.ctx name pos
        return s
      else
        diag s.ctx .E0304 s!"'\\{name}' needs a \{...} group" pos
        return s
  | .reserved name code unclosed pos =>
    warnOnce s.ctx ("ctrl:" ++ name) code s!"'\\{name}' is not implemented yet; skipped" pos
    if let some bpos := unclosed then
      -- The malformed arguments end with the command's line or at the
      -- next construct on it: the author's next declaration is never
      -- consumed here.
      warnUnclosed s.ctx s!"'\\{name}'" bpos
    return s
  | .unknownCmd name unclosed pos =>
    -- Unknown preamble commands are configuration, not content: their
    -- arguments are skipped with them, never elaborated as stray text.
    warnOnce s.ctx ("ctrl:" ++ name) .W0301
      s!"unknown command '\\{name}' in the preamble; skipped" pos
      (help := "\\define \\name(...) {body} declares it")
      (demote := Compat.styInternal s.ctx.file name)
    if let some bpos := unclosed then
      warnUnclosed s.ctx s!"'\\{name}'" bpos
    return s
  | .stray =>
    if s.textDiagged then
      return s
    else
      diag s.ctx .E0313 "only declarations may appear before '\\begin{document}'" none
      return { s with textDiagged := true }

/-- The elaboration state with the reporting machinery erased: the
projection T1's commutation compares. What it deliberately ignores — and
nothing else — is the four stores whose only readers are diagnostic sites:
the emitted diagnostics themselves (a swap legitimately reorders emission;
the diagnostic-code multiset stays under `scripts/compose-fuzz.lean`'s
watch), the warn-once memo (read only by `warnOnce`), the W0343 scalar
store (read only by `applyEvent`'s `.scalar` arm), and the W0348
declared-key store (read only by the `\theme` site). Everything a backend
or the body elaboration reads survives the projection. -/
def ESt.sem (e : ESt) : ESt :=
  { e with diags := #[], warnedUnknown := #[], seenScalars := #[], declaredKeys := #[] }

/-- The fold state with its one piece of reporting machinery erased, the
E0313 once-latch. -/
def PreState.sem (s : PreState) : PreState := { s with textDiagged := false }

/-- The heads in T1's proved tier: the keyed block declarations whose whole
apply step is a pure value plus reporting events. -/
def PDecl.keyedHead? : PDecl → Option String
  | .page _ _ => some "page"
  | .pdfmeta _ _ => some "pdfmeta"
  | .fonts _ _ => some "fonts"
  | .output _ _ => some "output"
  | .chrome _ _ => some "chrome"
  | .assert _ _ => some "assert"
  | .allow _ _ => some "allow"
  | _ => none

/-- T1's independence condition, proved tier: two keyed declarations with
different heads. The named exceptions stay outside by construction —
`\define`/`\defineenv`/`\tokens`/`\palette`/`\style` (reference→referent
order is essential), `\theme` (positional by design), `\documentclass`
(W0318 reads the class declared so far), same-head pairs (same-key
last-wins is the one essential order), and the inline-content heads
(running head/foot, logo, the title declarations), whose apply elaborates
content through `elabInlines` — one of the three tracked exemptions from
the termination checker, opaque to the kernel, which no theorem can range
over — so those heads stay with the oracle. -/
def PDecl.Independent (d₁ d₂ : PDecl) : Prop :=
  match d₁.keyedHead?, d₂.keyedHead? with
  | some h₁, some h₂ => h₁ ≠ h₂
  | _, _ => False

private theorem EM.run_bind (m : EM α) (f : α → EM β) (e : ESt) :
    (m >>= f).run e = (f (m.run e).1).run (m.run e).2 := rfl

private theorem applyEvent_sem (ctx : Ctx) (st : ESt) (ev : PEvent) :
    (applyEvent ctx st ev).sem = st.sem := by
  cases ev with
  | say d => rfl
  | scalar decl key value pos =>
    simp only [applyEvent, ESt.sem]
    repeat' split
    all_goals rfl
  | declared decl key =>
    simp only [applyEvent, ESt.sem]
    repeat' split
    all_goals rfl

private theorem foldEvents_sem (ctx : Ctx) (l : List PEvent) (st : ESt) :
    (l.foldl (applyEvent ctx) st).sem = st.sem := by
  induction l generalizing st with
  | nil => rfl
  | cons ev l ih =>
    simp only [List.foldl_cons]
    exact (ih (applyEvent ctx st ev)).trans (applyEvent_sem ctx st ev)

private theorem foldArr_sem (ctx : Ctx) (evs : Array PEvent) (e : ESt) :
    (evs.foldl (applyEvent ctx) e).sem = e.sem := by
  rw [← Array.foldl_toList]
  exact foldEvents_sem ctx evs.toList e

private theorem EM.run_stepDone_fst (ctx : Ctx) (r : PreState × Array PEvent) (e : ESt) :
    ((stepDone ctx r).run e).1 = r.1 := rfl

private theorem EM.run_stepDone_snd (ctx : Ctx) (r : PreState × Array PEvent) (e : ESt) :
    ((stepDone ctx r).run e).2 = r.2.foldl (applyEvent ctx) e := rfl

private theorem applyDecl_page_some (s : PreState) (src : String) (pos : Pos) :
    applyDecl s (.page (some src) pos) = stepDone s.ctx (stepPage s src pos) := rfl
private theorem applyDecl_page_none (s : PreState) (pos : Pos) :
    applyDecl s (.page none pos)
      = stepDone s.ctx (stepMissing s "page" "a {...} block" pos) := rfl
private theorem applyDecl_fonts_some (s : PreState) (src : String) (pos : Pos) :
    applyDecl s (.fonts (some src) pos) = stepDone s.ctx (stepFonts s src pos) := rfl
private theorem applyDecl_fonts_none (s : PreState) (pos : Pos) :
    applyDecl s (.fonts none pos)
      = stepDone s.ctx (stepMissing s "fonts" "a {...} block" pos) := rfl
private theorem applyDecl_pdfmeta_some (s : PreState) (src : String) (pos : Pos) :
    applyDecl s (.pdfmeta (some src) pos) = stepDone s.ctx (stepPdfmeta s src pos) := rfl
private theorem applyDecl_pdfmeta_none (s : PreState) (pos : Pos) :
    applyDecl s (.pdfmeta none pos)
      = stepDone s.ctx (stepMissing s "pdfmeta" "a {...} block" pos) := rfl
private theorem applyDecl_output_some (s : PreState) (src : String) (pos : Pos) :
    applyDecl s (.output (some src) pos) = stepDone s.ctx (stepOutput s src pos) := rfl
private theorem applyDecl_output_none (s : PreState) (pos : Pos) :
    applyDecl s (.output none pos)
      = stepDone s.ctx (stepMissing s "output" "a {...} block" pos) := rfl
private theorem applyDecl_chrome_some (s : PreState) (src : String) (pos : Pos) :
    applyDecl s (.chrome (some src) pos) = stepDone s.ctx (stepChrome s src pos) := rfl
private theorem applyDecl_chrome_none (s : PreState) (pos : Pos) :
    applyDecl s (.chrome none pos)
      = stepDone s.ctx (stepMissing s "chrome" "a {...} block" pos) := rfl
private theorem applyDecl_assert_some (s : PreState) (src : String) (pos : Pos) :
    applyDecl s (.assert (some src) pos) = stepDone s.ctx (stepAssert s src pos) := rfl
private theorem applyDecl_assert_none (s : PreState) (pos : Pos) :
    applyDecl s (.assert none pos)
      = stepDone s.ctx (stepMissing s "assert" "a {...} block" pos) := rfl
private theorem applyDecl_allow_some (s : PreState) (src : String) (pos : Pos) :
    applyDecl s (.allow (some src) pos) = stepDone s.ctx (stepAllow s src pos) := rfl
private theorem applyDecl_allow_none (s : PreState) (pos : Pos) :
    applyDecl s (.allow none pos)
      = stepDone s.ctx (stepMissing s "allow" "a {...} block of diagnostic codes" pos) := rfl

set_option maxHeartbeats 1000000 in
/-- T1 over `applyDecl`, the proved tier (audit-compose; the statement the
2026-09-18 PLAN entry records as unstatable before this fold existed):
independent adjacent preamble declarations commute up to reporting — the
fold state agrees under `PreState.sem`, and the elaboration state comes
back reporting-equal to where it started (`ESt.sem`), in both orders. The
oracle `scripts/compose-fuzz.lean` keeps watching what this tier does not
reach: the inline-content heads, same-head field-disjoint swaps, and the
diagnostic-code multiset. A commutation is a new theorem shape beside the
registered suffixes; `_comm` names it. -/
theorem applyDecl_comm (s : PreState) (e : ESt) (d₁ d₂ : PDecl)
    (h : PDecl.Independent d₁ d₂) :
    (((applyDecl s d₁ >>= fun s' => applyDecl s' d₂).run e).1.sem
      = ((applyDecl s d₂ >>= fun s' => applyDecl s' d₁).run e).1.sem)
    ∧ (((applyDecl s d₁ >>= fun s' => applyDecl s' d₂).run e).2.sem = e.sem)
    ∧ (((applyDecl s d₂ >>= fun s' => applyDecl s' d₁).run e).2.sem = e.sem) := by
  cases d₁ <;> cases d₂ <;>
    first
    | exact h.elim
    | exact absurd rfl h
    | (rename_i src₁ pos₁ src₂ pos₂
       rcases src₁ with _ | src₁ <;> rcases src₂ with _ | src₂ <;>
         refine ⟨?_, ?_, ?_⟩ <;>
           simp only [applyDecl_page_some, applyDecl_page_none, applyDecl_fonts_some,
             applyDecl_fonts_none, applyDecl_pdfmeta_some, applyDecl_pdfmeta_none,
             applyDecl_output_some, applyDecl_output_none, applyDecl_chrome_some,
             applyDecl_chrome_none, applyDecl_assert_some, applyDecl_assert_none,
             applyDecl_allow_some, applyDecl_allow_none,
             EM.run_bind, EM.run_stepDone_fst, EM.run_stepDone_snd] <;>
           first
             | simp only [foldArr_sem]
             | (dsimp only [stepPage, stepFonts, stepPdfmeta, stepOutput, stepChrome,
                  stepAssert, stepAllow, stepMissing]
                all_goals rfl))

/-- `sty_is_defaults`, the `\tokens` half (the sty-e2e audit's q2): a
`.sty`-sourced value is a default — for a keyed store, a document
declaration folding after the `.sty`'s wins, never the reverse. A
corollary of keyed last-wins (`Tokens.declare_last_wins`) plus the splice
preserving position: `Compat.applyLocalSty` inserts the file's text at
the `\usepackage` itself, so the `.sty`'s declarations fold before every
later document declaration — the premise this statement pins against a
future splice change. Source: LaTeX's own semantics, where package code
executes at `\usepackage` time (ltfiles.dtx `\@onefilewithoptions`) — so
a document declaration written *before* the `\usepackage` is overridden
by the `.sty`, exactly as in LaTeX. Layering (the audit's q3): a `.sty`
is document-layer text at its splice position — after class defaults,
before everything later in the preamble — not a new layer; `\theme`
stays the visual layer and `Theme.apply`'s theorems are untouched. -/
theorem sty_is_defaults_tokens (t : Tokens) (k : String) (sty doc : SymGlue) :
    ((t.declare k sty).declare k doc).find? k = some doc :=
  Tokens.declare_last_wins _ k doc

/-- `sty_is_defaults`, the `\palette` half: the same corollary through the
same one install door (`Palette.declare_last_wins`). -/
theorem sty_is_defaults_palette (p : Palette) (k : String) (sty doc : Color)
    (d d' : Bool) :
    ((p.declare k sty d).declare k doc d').find? k = some doc :=
  Palette.declare_last_wins _ k doc


/-- Rule (b)'s remainder, honoured: a `\renewcommand{\maketitle}` the gate
refused may still *declare* the built-in's styling — rules, skips, size and
weight, alignment — sitting around the built-in's own datum (`\@title`).
Read here, at the preamble's end, and not at the gate: the venue defines
the internals the body names (`\@maketitle`, `\@toptitlebar`) *after* the
redefinition itself, so only now does the body's expansion reach them. The
extracted keys merge *under* anything the document declared itself
(`\style{titlepage}` wins, `Theme.styleMerge`), and the W0361 that refused
the body gains the clause naming what survived. A redefinition that later
won (the built-in will not render) extracts nothing; a body-walk
redefinition keeps plain rule (b) — the venue's site is the preamble. -/
private def applyRefusedTitleStyle (s : PreState) : EM PreState := do
  let some body := (← get).refusedTitleBody | return s
  if (lookupUser s.ctx "maketitle").isSome then return s
  let events := barScanList s.ctx.user s.ctx.limit {} #[] body.toList
  let some est := barInterpret events | return s
  let merged := Theme.styleMerge ((s.styles.find? "titlepage").getD {}) est
  modify fun st => Id.run do
    let mut diags := st.diags
    let mut i := diags.size
    for _ in [0:st.diags.size] do
      i := i - 1
      if h : i < diags.size then
        let d := diags[i]
        if d.code == DiagCode.W0361.code && (d.message.splitOn "'\\maketitle'").length > 1 then
          diags := diags.set i { d with
            message := d.message ++ ", styled by the redefinition's rules and spacing" } h
          break
    return { st with diags := diags, refusedTitleBody := none }
  return { s with styles := s.styles.declare "titlepage" merged }

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
  -- The preamble is a fold: `scanDecls` segments it into declaration
  -- values, `applyDecl` applies each. The commutation statement (T1)
  -- quantifies over exactly these values; everything after the fold is a
  -- function of the fold's result.
  let s ← (scanDecls file preamble).foldlM applyDecl { ctx := { file := file } }
  -- What a refused `\maketitle` redefinition still declares, applied once
  -- the fold has bound everything its body names.
  let s ← applyRefusedTitleStyle s
  let mut ctx := s.ctx
  let docClass := s.docClass
  let sawClass := s.sawClass
  let classOptions := s.classOptions
  let mut page := s.page
  let sawPage := s.sawPage
  let fonts := s.fonts
  -- A deck that declares no theme takes the default bundle, installed
  -- *under* the document (`Theme.applyUnder`: the document's own
  -- declarations win): a presentation always paints its pages, so the
  -- slides class defaults to `daylight`. Every other class keeps the
  -- unpainted defaults — a default bundle on print classes paints every
  -- page edge to edge (measured at a 99.9% pixel change on a one-page
  -- résumé). A `\theme` of any spelling is the author's choice and
  -- stands, unknown names included (W0319 already spoke).
  let defaultBundle := s.docClass == Ir.DocClass.slides && !s.sawTheme
  let themedDs : Theme.Decls :=
    let own : Theme.Decls := { palette := s.palette, tokens := s.tokens
                               styles := s.styles, chrome := s.chrome }
    if defaultBundle then Theme.applyUnder Theme.daylight own else own
  let palette := themedDs.palette
  let tokens := themedDs.tokens
  let styles := themedDs.styles
  let chrome := themedDs.chrome
  ctx := { ctx with palette := palette, tokens := tokens, styles := styles
                    locale := s.info.locale }
  let mut head := s.head
  let mut foot := s.foot
  let headFrom := s.headFrom
  let footFrom := s.footFrom
  let chromeDeclared := s.chromeDeclared
  let mut info := s.info
  let mut output := s.output
  let mut asserts := s.asserts
  let allow := s.allow
  -- A classless .tex builds — the no-preamble pitch needs a bare document
  -- to build, and the article default is a real, sourced page model — but
  -- not silently: the class switches the page model, the furniture
  -- legality, and the implied assertions, so a choice the engine made for
  -- the author is named. LaTeX errors here out of implementation necessity
  -- (no class, no \normalsize), not design. Markdown has no class concept:
  -- the omission is that surface's grammar, never noted.
  if !sawClass && file.endsWith ".tex" then
    diag ctx .N0017 "no '\\documentclass'; the article page model is assumed" none
      (help := "declare \\documentclass{article} (or slides, card, resume, webpage, poster) to choose it")
  let record := docClass.record
  -- The body size: `\page{ fontsize = ... }` wins, else the class option
  -- (`fontsize=11pt`, KOMA's spelling, or the standard classes' bare
  -- `11pt`), else the class record's default — beamer's documented 11pt
  -- for slides (user guide §18.2.1), the engine's 10pt base otherwise.
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
      if let some d := record.fontSize then
        page := { page with fontSize := d }
  -- The class's paragraph separation, where the document declares none:
  -- `\page{ parskip = ... }` and compat's injected declaration both win.
  if page.parskip.isNone then
    if let some g := record.parskip then
      page := { page with parskip := some g }
  -- The geometry is the page model's, the kernel's own: a frame fills
  -- beamer's stage, a face is trimmed to a trade size, flow takes the
  -- text block. Option-keyed sizes (aspectratio, us/jis) live here with
  -- the model, not on the class record — they are the model's stages.
  -- Class options and `\page` keys are one vocabulary: `*paper` (and
  -- KOMA's `paper=`) names a size from the same `pageSizes` table
  -- `\page{ size = ... }` reads, and `landscape` swaps the axes — the
  -- reading the geometry package documents for exactly these options
  -- (geometry manual §5.2, paper size options). A document that declared
  -- its own geometry keeps it: the class option is a default, never a
  -- lock (the same rule the slides stage takes). `twocolumn` and `draft`
  -- ask for a page model and a proofing mode the engine does not have:
  -- each is refused by name (W0356) — the silent drop was the defect
  -- class here, an a4paper request quietly shipping on letter.
  let classOpts := (classOptions.splitOn ",").map (·.trimAscii.toString)
  if record.model == .flow then
    let dflt : PageSpec := {}
    if page.width == dflt.width && page.height == dflt.height then
      let sized := classOpts.findSome? fun o =>
        let o := if o.startsWith "paper=" then
          (o.drop "paper=".length).toString ++ "paper" else o
        if o.endsWith "paper" then
          pageSizes.lookup ((o.dropEnd "paper".length).toString)
        else none
      if let some (w, h) := sized then
        page := { page with width := w, height := h }
      if classOpts.contains "landscape" then
        page := { page with width := page.height, height := page.width }
  for o in classOpts do
    if o == "twocolumn" then
      diag ctx .W0356
        "class option 'twocolumn' asks for a two-column page; the text is set in one column"
        none
    else if o == "draft" then
      diag ctx .W0356
        "class option 'draft' asks for a proofing mode the engine does not have; the document is rendered in full"
        none
  -- Slides fill beamer's stage unless the document declared its own
  -- geometry: a handout on letter portrait is not best effort, it is wrong.
  if record.model == .frame then
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
  -- A face is trimmed from a sheet, so its defaults are the print
  -- trade's, not a guess, and they live on the class record
  -- (`ClassRecord.trimDefault`/`safeMargin`): the card's ISO/IEC 7810
  -- ID-1 with the 5 mm safe zone, the poster's ISO 216 A0 with
  -- beamerposter's 1 cm — unless the class option names the US
  -- (3.5 × 2 in) or Japanese (91 × 55 mm) card trade size. No
  -- hyphenation: a face is display text, not a page of a run — which is
  -- also why the prose measure band (W0201) does not apply to it.
  else if record.model == .face then
    let dflt : PageSpec := {}
    let opts := (classOptions.splitOn ",").map (·.trimAscii.toString)
    if page.width == dflt.width && page.height == dflt.height then
      let named :=
        if opts.contains "us" then some (Dim.pt 252, Dim.pt 144)
        else if opts.contains "jis" then some (Dim.mm 91, Dim.mm 55)
        else none
      match named.orElse (fun _ => record.trimDefault) with
      | some (w, h) => page := { page with width := w, height := h }
      | none => pure ()
    if let some m := record.safeMargin then
      if page.hmargin == dflt.hmargin then
        page := { page with hmargin := m }
      if page.vmargin == dflt.vmargin then
        page := { page with vmargin := m }
    if page.hyphenate.isNone then
      page := { page with hyphenate := some false }
    -- Below the 40-character working minimum for justified text
    -- (Bringhurst, Elements 2.1.2), the measure is set ragged: at card
    -- width justification has no stretch to work with and the breaker is
    -- left choosing between overfull answers.
    if page.justify.isNone then
      page := { page with justify := some false }
  else if !sawPage then
    -- An undeclared letter page takes Bringhurst's text block for a 10pt
    -- text face, 26 picas, not the word-processor inch: the default must
    -- satisfy the measure band the engine checks (W0201). A document that
    -- declares any \page geometry keeps every value it named.
    page := { page with hmargin := (page.width - Ir.articleTextBlock) / 2 }
  -- Furniture legality is the class record's, not the geometry's: a class
  -- that carries no running furniture drops the declaration and says so.
  if !record.runningFurniture && (head.isSome || foot.isSome) then
    diag ctx .W0317
      "a card carries no running head or foot; the declaration is dropped" none
    head := none
    foot := none
  -- Build intent the class carries, when the document's `\output` names
  -- none: the class declares what to build the way `\documentclass`
  -- already declares the page model. A document's own `formats = ...`
  -- replaces it whole — opting into the print twin is one declared line.
  if output.formats.isEmpty then
    for f in record.formats do
      output := output.addFormat f
  if output.md.isNone then
    output := { output with md := record.mdName }
  ctx := { ctx with slides := record.model == .frame
                    numberHeadings := record.numberHeadings, styles := styles
                    page := page
                    engineTokens := engineLengthTokensOfPage page }
  -- Numbering is a property of the finished document, not of any one
  -- elaboration site: `Ir.numberFloats` fills every captioned float's
  -- number in document order (`numberFloats_exact` is the fact `\ref`
  -- will resolve against), once, before any backend reads the body.
  let blocks := Ir.numberFloats (← elabBlocks ctx body)
  -- Cross-references resolve here, once, against the whole document's
  -- labels: the float rows are read off the numbered IR it just produced
  -- (`Ir.floatLabelRows`), so a label under a captioned float binds to the
  -- number the node carries — one numbering, `Ir.refs_agree_with_numbering`
  -- the statement — and `Ir.resolveRefs` is a pure pass over the IR, so no
  -- backend re-scans for labels and a forward reference costs nothing. The
  -- diagnostics are judged from the recorded sites — a reference cannot be
  -- judged where it stands, because its label may follow it.
  let stRefs ← get
  let table := if stRefs.labels.isEmpty then stRefs.labels
    else Ir.withFloatRows stRefs.labels (Ir.floatLabelRows blocks)
  let blocks := if stRefs.refSites.isEmpty then blocks
    else Ir.resolveRefs table blocks
  let mut warnedRefs : Array String := #[]
  for (key, rpos) in stRefs.refSites do
    unless warnedRefs.contains key do
      match table.find? (·.1 == key) with
      | some (_, some _) => pure ()
      | some (_, none) =>
        warnedRefs := warnedRefs.push key
        diag ctx .W0349 s!"'{key}' is \\label'ed where nothing is numbered; set as '??'"
          (some rpos)
          (help := "move the \\label after a numbered heading, a captioned float, or into an equation")
      | none =>
        warnedRefs := warnedRefs.push key
        diag ctx .W0349 s!"no \\label\{{key}} in the document; set as '??'" (some rpos)
          (help := s!"declare \\label\{{key}} after the numbered thing it names")
  -- Body declarations do NOT displace the document state: `doc.palette`
  -- and `doc.tokens` stay the preamble+theme state — epoch 0 — and each
  -- body declaration rides its own `.setPalette`/`.setTokens` block, so a
  -- setting's effect is confined to the flow after it. The final flow
  -- state exists only for the shadow judge below, which must see every
  -- role the document ever declares.
  let stBody ← get
  let finalPalette := stBody.flowPalette.getD palette
  -- A definition that shadows a palette role replaces a value that adapts
  -- with one that cannot: the palette no longer reaches those words (a
  -- variant or a host page's override dies there), and the contrast judge —
  -- which sees a role use only because it resolves through the palette —
  -- goes blind to them. Shadowing a command is LaTeX-normal and stays
  -- permitted; the warning names what this particular shadow costs. Judged
  -- against the final palette, so declaration order cannot hide it.
  let mut shadowSaid : Array String := #[]
  for cmd in ctx.user do
    if !shadowSaid.contains cmd.name && (finalPalette.find? cmd.name).isSome then
      shadowSaid := shadowSaid.push cmd.name
      modify fun st => { st with diags := st.diags.push (Diag.of .W0342
        (s!"'\\{cmd.name}' is also a palette role; this definition freezes it, " ++
          "so the palette and the contrast check no longer reach it")
        (some cmd.span)
        (help := s!"drop the definition and '\\{cmd.name}' colours as declared; " ++
          s!"declared: {String.intercalate ", " (finalPalette.entries.toList.map (·.1))}")) }
  -- The logo may have been declared in either half; a card carries none.
  let mut logo := (← get).logo
  if !record.runningFurniture && logo.isSome then
    diag ctx .W0317
      "a card carries no logo; the declaration is dropped" none
    logo := none
  -- The class's implied contract, stated as the assertions the engine
  -- already enforces against the shipped pages (the card's: content fits
  -- its faces, ink respects the safe margin, the smallest type clears the
  -- fluent-reading floor; the resume's: the same frame over one page).
  -- Declaring an assertion of the same form is intent and silences the
  -- class default; the help beside each value is the record's own.
  if let some pb := record.pagesBound then
    unless asserts.any (fun a => match a.kind with | .pages _ _ => true | _ => false) do
      match pb with
      | .faces =>
        let faces : Int := max 1 (blocks.foldl (init := 0) fun n b =>
          match b with
          | .frame _ _ _ _ => n + 1
          | _ => n)
        asserts := asserts.push {
          kind := .pages .le faces
          help := some s!"the {docClass.name} class asserts content fits its {faces} face(s); \
declare \\assert\{ pages <= N } to take control" }
      | .lit op n =>
        asserts := asserts.push { kind := .pages op n, help := some record.pagesHelp }
  if let some h := record.inkInArea then
    unless asserts.any (·.kind == .textInArea) do
      asserts := asserts.push { kind := .textInArea, help := some h }
  if let some (floor, h) := record.xHeightFloor then
    unless asserts.any (fun a => match a.kind with | .minXHeight _ => true | _ => false) do
      asserts := asserts.push { kind := .minXHeight floor, help := some h }
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
    headFrom := headFrom
    footFrom := footFrom
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
