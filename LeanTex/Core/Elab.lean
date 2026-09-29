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
import LeanTex.Core.PdfContract

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
and its parameters bind from the groups after `\begin{name}`. The three
flags are the space rules TeX's own commands state at its seams
(`envOfHalves`). -/
structure UserEnv where
  name : String
  params : Array Param
  beginBody : Array Raw
  endBody : Array Raw
  /-- Commands the halves may use: those defined before this environment.
  That bound is what makes expansion terminate, as `limit` does for
  commands. -/
  cmdLimit : Nat
  /-- The body's leading spaces are skipped: `\ignorespaces` closes the
  begin code, or environ trims the body. -/
  ignoresLead : Bool := false
  /-- The body's trailing spaces are dropped: environ trims the body. -/
  trimsTail : Bool := false
  /-- The spaces after `\end{name}` are skipped: `\ignorespacesafterend` in
  the end code, environ's default final code. -/
  ignoresAfterEnd : Bool := false
  deriving Repr, BEq

/-- A theorem-like environment's style: the kernel's (latex.ltx
`\@begintheorem`: the head bold, the body `\itshape`) where amsthm is not
loaded, else amsthm's three (amsthm.sty `\th@plain`, `\th@definition`,
`\th@remark`: a bold head over an italic or upright body, and an italic
head over an upright one). -/
inductive ThmStyle where
  | kernel
  | plain
  | definition
  | remark
  deriving Repr, BEq, Inhabited

/-- The space a style's theorems open (`Ir.thmSkips`): the kernel's
trivlist, amsthm's `\thm@preskip` and `\thm@postskip`, remark's halves. -/
def ThmStyle.space : ThmStyle → Ir.ThmSpace
  | .kernel => .kernel
  | .plain | .definition => .ams
  | .remark => .amsHalf

/-- One `\newtheorem`: the environment, its heading, the counter it steps
(`none` is amsthm's unnumbered `\newtheorem*`) and the style in force where
it was declared (amsthm.sty: `\newtheorem` captures `\thm@style`). -/
structure ThmDef where
  env : String
  heading : Array Inline
  counter : Option String
  style : ThmStyle
  deriving Repr, BEq

/-- The theorem declarations the preamble made and the counters the body
steps: the environments, each counter with the heading level that resets it
(`[section]`), the `\theoremstyle` in force — `.kernel` until amsthm is
loaded, whose default is `plain` (Compat spells the load that way), so
whether amsthm's heads and its `proof` exist is read off the style — and,
in flow order, each counter with the heading number it last stepped under
(the `[within]` levels, spelled) and its value: a counter that finds its
heading moved restarts at 1, `\@addtoreset`'s effect read where the number
is used. One field on `ESt`, the `AlgSt` shape: the knots' state stays
narrow. -/
structure ThmDecls where
  defs : Array ThmDef := #[]
  counters : Array (String × Option Nat) := #[]
  style : ThmStyle := .kernel
  nums : Array (String × String × Nat) := #[]
  /-- The proofs open around the walk: amsthm's QED stack holds a mark only
  inside one, so a `\qedhere` outside sets nothing. -/
  proofs : Nat := 0
  /-- The innermost open proof's `\qedhere` has set its mark in a display's
  number slot, so the proof's end sets none. -/
  qedPlaced : Bool := false
  deriving Repr, BEq

/-- amsthm is loaded: some `\theoremstyle` has been declared. -/
def ThmDecls.ams (d : ThmDecls) : Bool := d.style != .kernel

/-- What the picture arm reads, as one field of `Ctx`: the block knot copies
every `Ctx` field at each `{ ctx with … }`, and its compilation is at its
budget (AGENTS.md), so the picture context travels as one value — the
`SpanRecords` shape. -/
structure PicCtx where
  /-- The boundary tool in force: the external TeX that draws pictures
  outside the rendered subset. Open by default — the tool belongs to the
  build environment exactly as fonts do, and the driver alone decides
  fulfilment (`boundary_request_env_free`) — so the declaration
  (`\pictures{ tool = lualatex }`, or TikZ's own `\tikzexternalize`
  spelling) *pins* a tool, and `\pictures{ tool = none }` refuses the
  boundary: `none` here is the declared refusal. -/
  tool : Option String := some "lualatex"
  /-- The boundary requests fulfilment withdrew: pictures the rendered
  subset draws in part whose request no tool drew (`Cli.Boundary.withdraw`).
  Each is drawn natively on the elaboration the driver runs with them, its
  refusals named as a refused door names them. Empty on the first pass,
  which states every request from the document alone. -/
  withdrawn : Array String := #[]
  /-- The preamble declarations a boundary standalone needs beyond the
  document's design — non-native package loads and the tikz-family set
  lines, as written (`Compat.boundaryDecls`). The font roles and the
  palette are not carried here: the request site (`Ir.pictureRefs`) reads
  them off the finished `Doc`, after contrast realization. -/
  preamble : String := ""
  /-- The document's own macro definitions for the boundary standalone, as
  written (`macroScan`). One entry per name; the request site carries the
  subset a picture body reaches. -/
  macros : Array (String × String) := #[]
  /-- The key lists the document's `\tikzset` lines wrote, in source order
  and wherever they stood (`Compat.tikzsetKeys`). Their `/.style`
  definitions are what every picture's own option block starts from, so a
  style reaches its picture whether it was declared in the preamble or
  beside the figure. Set once by the elaborator, as `preamble` is. -/
  sets : Array (Array Raw) := #[]
  /-- How a node label's content measures at a per-mille size: the face,
  arriving as a function rather than a font set, because the elaborator has
  no face of its own and does not acquire one by knowing this. The driver
  resolves it and passes it in; the default answers nothing, which is what a
  first pass — the one that discovers which face the document declared —
  must use. -/
  metric : Ir.Pic.LabelMetric := fun _ _ => {}

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
  /-- The document/class palette in force when the body opens. A page-colour
  reset restores only its ground from this snapshot while preserving every
  unrelated body declaration. -/
  basePalette : Palette := {}
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
  /-- The page model is `face` (card, poster's trimmed faces): one face of
  display text with no note apparatus — where `\footnote` is refused by
  name (W0374). -/
  face : Bool := false
  /-- The class numbers its unstarred headings (article; classes.dtx
  §Sectioning). Slides and card headings never number, so a deck renders
  exactly as before. -/
  numberHeadings : Bool := false
  /-- The effective backend target set of the enclosing `{ifbackend}`
  nesting: every backend at the top, intersected at each conditional on the
  way in, so a nested conditional that empties the set is diagnosed where
  it stands (E0334) — the same walk `Ir.orphanFree` performs. -/
  backendTargets : List String := Ir.backendNames
  /-- The picture arm's context (`PicCtx`): the boundary door, the withdrawn
  requests, the standalone's material and the label measurement. -/
  pic : PicCtx := {}
  /-- A definition body read the way its use will read it, at the definition
  (rule (b)'s trial, `gateRedefB`): document content, whatever file defined
  it. A command a style file defines is called from the document's own text,
  and the call is where its arguments stand, so the trial must not read the
  body as package code. -/
  atUse : Bool := false

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

/-- A document-defined algorithm keyword (`\SetKw`, `\SetKwInOut`,
`\SetKwInput`, `\SetKwFunction`, `\SetKwData` — algorithm2e §10.3):
what the defined control sequence means when it is met inside an
algorithm. The word/function/data payloads stay raws so accents in the
declared text still elaborate; an io label is rendered text, the line
kind's own word. -/
inductive AlgKwDef where
  | word (body : Array Raw)
  | io (label : String)
  | func (name : Array Raw)
  | data (name : Array Raw)
  deriving Repr, BEq

/-- The document-global algorithm state the preamble declares: keywords
(`\SetKw` and family — algorithm2e's definitions are document-wide) and
the display defaults every algorithm starts from (`\DontPrintSemicolon`,
`\LinesNumbered`). One field on `ESt`, so the elaboration knot's state
stays narrow. -/
structure AlgSt where
  kws : Array (String × AlgKwDef) := #[]
  semis : Bool := true
  numbered : Bool := false
  deriving Repr, BEq

/-- The spans the reporting layer reads back out of elaboration — the
`AlgSt` shape: one field on `ESt`, so the elaboration knot's state stays
narrow. `bib` is where each `\bibliography` marker stands (E0503's `-->`);
`images` each non-text object's first reporting span: file and boundary
image sources, and positional native-picture keys (the alt judge's `-->`,
the driver's per-picture diagnostics);
`cites` each citation key's first `\cite` (the no-bibliography judge:
with no `\bibliography` anywhere, `Bib.apply` never runs and nothing else
explains the '?' the mark ships). -/
structure SpanRecords where
  bib : Array (String × Span) := #[]
  images : Array (String × Span) := #[]
  cites : Array (String × Span) := #[]
  /-- Each colour expression's first span, the value it resolved to, and
  whether it named a role: the contrast judge's `-->`, and the expression
  it names for a colour that carries no role. -/
  colors : Array (String × Color × Bool × Span) := #[]
  /-- The boundary pictures the rendered subset draws in part, by picture
  id: the requests the driver may withdraw (`ReqSpans.fallbacks`). -/
  fallbacks : Array String := #[]
  deriving Repr, BEq

/-- beamer's `\logo` (`main`), a declaration legal in the preamble and the
body alike, and the gemini lineage's `\logoleft`/`\logoright` — the
headline band's corner slots; the last of each wins, as in beamer. -/
structure Logos where
  main : Option (Array Inline) := none
  left : Option (Array Inline) := none
  right : Option (Array Inline) := none
  deriving Repr, BEq

/-- **The argument shapes a counted refusal has met, as a set.** A
once-per-construct warning shows the first site's words and the group's
total, so those words are a claim about every site the number counts. When
the sites differ in shape — one call of `\x` leading with a `[...]` run,
another not — the first call's wording either hides a drop the reader needs
or claims one that never happened. Both were live: a dropped run went
unmentioned at default verbosity, and `(2 sites)` read as runs dropped at
both.

Two independent bits rather than a three-valued state, because that is what
makes the accumulation order-blind: each is an `Array.any` over the sites'
bits, so permuting the document's calls cannot change the wording
(`runShape_fold_exact`). `{}` is the empty group — no site yet — and is
never a wording. -/
structure RunShape where
  /-- Some site of this group led with a `[...]` run. -/
  withRun : Bool := false
  /-- Some site of this group led with no `[...]` run. -/
  withoutRun : Bool := false
  deriving Repr, BEq, DecidableEq

/-- One more site, folded in. -/
def RunShape.add (s : RunShape) (optionRun : Bool) : RunShape :=
  if optionRun then { s with withRun := true } else { s with withoutRun := true }

/-- **The accumulated shape is exactly the pair of `any`s over the sites.**
Both projections are `Array.any`/`List.any`, so the wording a group's
visible line carries is a function of the *set* of its sites' shapes and
never of their order: the same document with its two calls swapped reports
the same sentence. This is the statement behind the mixed-shape test that
runs both orders. -/
theorem runShape_fold_exact (bs : List Bool) :
    bs.foldl RunShape.add {} =
      { withRun := bs.any id, withoutRun := bs.any (!·) } := by
  suffices h : ∀ (s : RunShape) (bs : List Bool), bs.foldl RunShape.add s =
      { withRun := s.withRun || bs.any id, withoutRun := s.withoutRun || bs.any (!·) } by
    simpa using h {} bs
  intro s bs
  induction bs generalizing s with
  | nil => simp
  | cons b rest ih =>
    cases b <;> simp [RunShape.add, ih, List.any_cons, Bool.or_comm]

/-- Folding a site in only ever adds shapes: a group's wording widens and
never narrows, which is why one rewrite of the visible line per new shape is
enough (there are two shapes, so at most one rewrite per group). -/
theorem runShape_add_monotone (s : RunShape) (b : Bool) :
    (s.withRun → (s.add b).withRun) ∧ (s.withoutRun → (s.add b).withoutRun) := by
  cases b <;> simp [RunShape.add]

/-- The counters the flow keeps (ltcounts.dtx), in document order, and
the heading-number state they render through. -/
structure Counters where
  /-- The section counters in flow order, levels 1–3: elaboration is one
  pass in document order, so stepping them here is exactly LaTeX's
  \refstepcounter sequence. -/
  secNums : Nat × Nat × Nat := (0, 0, 0)
  /-- LaTeX's `secnumdepth` counter: the deepest level a heading numbers
  at, and above which it neither numbers nor steps (ltsect.dtx `\@sect`).
  3 is article's (classes.dtx); the run-in levels four and five number
  where a document raises it (`runNums`). -/
  secDepth : Int := 3
  /-- The run-in levels' counters, `paragraph` and `subparagraph`
  (classes.dtx: levels four and five), stepped only where `secDepth`
  reaches them and zeroed whenever a level above them steps
  (`\@addtoreset`, whose resets cascade). -/
  runNums : Nat × Nat := (0, 0)
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
  /-- The listing counter, per document: every captioned listing takes the
  next number in flow order, exactly the equation counter's fold
  (listings steps `\thelstlisting` per captioned listing). -/
  lstNum : Nat := 0
  /-- The footnote counter, per document, stepped by `Ir.footnoteMark`:
  `\footnote[n]` overrides without stepping, so
  `Ir.footnote_numbers_gapless` is the numbering this fold realizes.
  Per-chapter numbering waits for a real report class (a `ClassRecord`
  field then). -/
  fnNum : Nat := 0
  /-- The theorem-like environments (`\newtheorem`, `\theoremstyle`) and
  their counters in flow order. -/
  thm : ThmDecls := {}

structure ESt where
  diags : Array Diag := #[]
  /-- Warn-once keys already fired: a macro used forty times is one problem,
  not forty. Keys are namespaced (`env:`, `ctrl:`, `palette:`) so an
  environment and a command sharing a name cannot silence each other. -/
  warnedUnknown : Array String := #[]
  /-- Per counted-refusal key: the argument shapes its sites have carried,
  and the index in `diags` of the line the group's total is read off. The
  index is recorded rather than searched for, so only the diagnostic *this*
  emitter wrote is ever rewritten — the preamble's own refusal, which shares
  the key but not the wording, is untouched. An index is a position in one
  `diags` array, so it is reset with that array (`ESt.freshReport`). -/
  runShapes : Array (String × RunShape × Nat) := #[]
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
  /-- The bodies of refused size-command redefinitions (rule (b), W0361),
  in document order: read once more at the preamble's end for the
  `\@setfontsize` ladder they may declare (`applyRefusedSizeLadder`), as
  `refusedTitleBody` is for `\maketitle`'s styling. -/
  refusedSizeBodies : Array (String × Array Raw × Span) := #[]
  /-- Speaker-note bodies met inside inline content, where a block cannot
  stand, each with its `\note`'s position: the enclosing frame drains them
  to its end, so a mid-sentence `\note` neither splits its paragraph nor
  loses its words. -/
  pendingNotes : Array (Array Raw × Pos) := #[]
  /-- The logo declarations, one field: the knot state stays narrow (every
  `{ st with … }` across the knots copies each field, and the knot's LCNF
  compile scales with the count — the SpanRecords shape). -/
  logos : Logos := {}
  /-- Boundary picture requests met in the body: content hash of each
  wrapped standalone source, with the source — deduplicated, so one
  picture repeated is one request. Assembled onto `Doc.pictureSrcs`. -/
  pictures : Array (String × String) := #[]
  /-- The salvage this elaboration recovered, in flow order: assembled onto
  `Doc.salvage`. Written at the recovery sites and read nowhere inside the
  elaborator — it is the attribution the census needs, not a decision the
  front end makes. -/
  salvage : Array Ir.Recovered := #[]
  /-- Where the deck's frame count starts over (`Compat.frameRestartMark`):
  the index of the next top-level block when the mark was read. Assembled
  onto `Doc.frameRestart`. -/
  frameRestart : Option Nat := none
  /-- `\bibliographystyle`, wherever it appears — LaTeX reads it anywhere
  before the .aux is written; here the `\bibliography` marker met later
  carries it, so the declared name reaches resolution with the block. -/
  bibStyle : Option String := none
  /-- natbib's declarations, as `Doc.natbib` carries them: `none` until the
  load's marker (`@natbib`, which the compatibility pass replays at
  `\begin{document}`) says natbib is there. -/
  natbib : Option (Array String) := none
  /-- The family a `\url`/`\nolinkurl` sets in, from url.sty's `\urlstyle`:
  `tt`/`rm`/`sf` name the mono/roman/sans family, and `same` asks for the
  running face, which is `none` — no family style at all, not a fourth
  family. url.sty's own default is `tt`, so that is the initial value.
  In the preamble it is the last defined value the preamble names, for
  every declaration wherever the selector stands (`elabDoc` reads it before
  the fold); in the body, flow scope, as `flowPalette` is: a selector
  applies to the URLs after it. -/
  urlFamily : Option Ir.Style := some .mono
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
  /-- The declarations met between blocks in the enclosing scopes,
  outermost first (`Ir.Decl`), threaded as the flow language is: every
  inline region built under them — a paragraph, a table cell — is wrapped
  in them (`Ir.wrapDecls`), which is how `\footnotesize` before a tabular
  reaches its cells (`Ir.decl_between_blocks_covers`). The declaration
  arm pushes on entering the rest of its scope and restores on leaving. -/
  blockDecls : List Ir.Decl := []
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
  /-- LaTeX's counters and the heading numbers they render, apart: the
  inline elaboration knot's compile grows with this structure's fields and
  stands at its heartbeat budget, so state the knot never reads is a record
  of its own (`Counters`). -/
  ctr : Counters := {}
  /-- The binding of the nearest preceding numbered thing — what a `\label`
  declared here binds to: the rendered number with the kind of what it
  names (`Ir.RefBinding`). A heading sets it for the flow after it; a bare
  `\refstepcounter` sets a kindless binding (`applyCounter`). A captioned
  float never writes here: its number exists only after
  `Ir.numberFloats` runs on the finished body, so the labels under it are
  bound from the numbered IR (`Ir.floatLabelRows`), never predicted. -/
  refTarget : Option Ir.RefBinding := none
  /-- The label table in flow order: each key with the binding it took.
  The first declaration of a key wins (LaTeX's behaviour); a second is
  W0350 at its own position. -/
  labels : Array (String × Option Ir.RefBinding) := #[]
  /-- The same table's key set, the only thing the duplicate test asks of
  it. The table stays flow-ordered because backends read it in order; the
  set answers "already declared" without walking it, which a document of
  a few thousand labels had been paying a square for. One writer
  (`labelStep`) moves both, and `labelStep_set_eq` is that they cannot
  drift. -/
  labelKeys : Std.HashSet String := {}
  /-- Every reference site with its form, for W0349 and W0380 once the
  whole table is known: a reference may point forward, so it cannot be
  judged where it stands. -/
  refSites : Array (String × Ir.RefForm × Pos) := #[]
  /-- The spans the reporting layer reads, packed as one field: the state
  is copied at every `{ st with ... }` across the elaboration knots, and
  the knots' compile cost scales with the field count, so the three
  span records ride together. Reporting metadata, delivered beside the
  `Doc` (`ReqSpans`), never on it. -/
  spans : SpanRecords := {}
  /-- The document-global algorithm state the preamble declared. -/
  alg : AlgSt := {}

/-- **The reporting state a trial elaboration starts from.** A trial swaps
`diags` for an empty array, and every field that indexes that array or
dedups against it goes with it: `runShapes` holds positions in `diags`, so a
trial that kept it while emptying `diags` let `bumpRunShape` reword whatever
the trial had pushed at a recorded position — a diagnostic another construct
emitted — and W0361 then quoted that construct. One helper, so a field of
this kind is reset at the one place a trial begins, never field by field. -/
def ESt.freshReport (e : ESt) : ESt :=
  { e with diags := #[], warnedUnknown := #[], runShapes := #[] }
/-- The mandatory `{language}` head of a `{minted}` body, after any option
head: the language text and the index past the `}`, `none` when the group
is missing. -/
private def mintedLangHead (s : String) (start : Nat) : Option (String × Nat) := Id.run do
  let cs := s.toList.toArray
  let mut i := start
  for _ in [0:cs.size] do
    if h : i < cs.size then
      if cs[i] == ' ' || cs[i] == '\t' then i := i + 1 else break
    else break
  if h : i < cs.size then
    if cs[i] != '{' then return none
    let mut j := i + 1
    let mut out := ""
    for _ in [0:cs.size] do
      if h2 : j < cs.size then
        let c := cs[j]
        if c == '}' then return some (out, j + 1)
        out := out.push c
        j := j + 1
      else break
    return none
  else return none

/-- Where a listing body's content starts: past the option head and, for
`{minted}`, its language argument — the one index both the block arm and
the inline degradation strip from. -/
private def listingContentStart (env s : String) : Nat :=
  let afterOpt := ((Parse.listingOptHead s).map (·.2)).getD 0
  if env == "minted" then
    ((mintedLangHead s afterOpt).map (·.2)).getD afterOpt
  else afterOpt

/-- Strip the value's one surrounding brace group: `{An example}` reads as
`An example`, as listings' keyval values do. -/
private def listingVal (v : String) : String :=
  let v := v.trimAscii.toString
  if v.startsWith "{" && v.endsWith "}" && v.length ≥ 2 then
    ((v.drop 1).dropEnd 1).toString.trimAscii.toString
  else v

abbrev EM := StateM ESt

/-- Build the diagnostic `diag` pushes, as a value: the one constructor
both the monadic emitter and the pure preamble steps (`PEvent.say`) share,
so a message exists in exactly one spelling. -/
private def diagOf (ctx : Ctx) (code : DiagCode) (msg : String) (pos : Option Pos)
    (help : Option String := none) (subject : Option String := none)
    (refused : Option String := none) : Diag :=
  Diag.of code msg (pos.map (⟨ctx.file, ·⟩)) help subject refused

private def diag (ctx : Ctx) (code : DiagCode) (msg : String) (pos : Option Pos)
    (help : Option String := none) (refused : Option String := none) : EM Unit :=
  modify fun st => { st with
    diags := st.diags.push (diagOf ctx code msg pos help (refused := refused)) }

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

/-- A warning delivered once per construct and *counted* every time: the
same unsupported construct in forty frames is one problem, not forty, but it
is also not one loss. The first site carries the message, the help, and —
after `Diag.tallySites` — the total; each later site rides beside it as a
note with the same code and the same structured `subject`, so it reads
under `-v` at its own position and the count on the visible line is the
number of sites the log holds. The words match too, except where a refusal
words its argument shape (`RunShape.clause`): there each note keeps its own
site's clause, and the first line is reworded to the group's. Keying on the
construct alone is what
made ten lines stand for fifty losses, two of them node labels dropped with
no diagnostic at all because an earlier site had spent the key.
`demote` delivers the first site as a note instead — the spliced-`.sty`
TeX-internal refusal (`Compat.styInternal`), correct and unactionable per
line, counted once by N0020 and listed under `-v`.

The state step is a pure function so that a statement can name it: the
first-site flag is a term over the state passed in, not a bound variable
inside a `do` block, which is what `warnUnknownCmd_push_exact` reads. -/
private def warnOnceDiag (ctx : Ctx) (key : String) (code : DiagCode) (msg : String)
    (pos : Pos) (help : Option String) (demote first : Bool) : Diag :=
  let d := diagOf ctx code msg (some pos) (if first then help else none) (subject := some key)
  if demote || !first then d.demote else d

/-- **One keyed warning, one diagnostic, carrying its code and its key as
subject.** The census hypothesis, discharged at the door every counted
diagnostic goes through: `Diag.tallySites_exact` — the theorem that the
number on the visible line is the number of sites of that loss — assumes
`subject.isSome`, and was vacuous on exactly the class that miscounted. -/
theorem warnOnceDiag_kind_exact (ctx : Ctx) (key : String) (code : DiagCode) (msg : String)
    (pos : Pos) (help : Option String) (demote first : Bool) :
    (warnOnceDiag ctx key code msg pos help demote first).kind = code := by
  unfold warnOnceDiag diagOf Diag.of Diag.demote
  dsimp only
  split <;> rfl

theorem warnOnceDiag_subject_exact (ctx : Ctx) (key : String) (code : DiagCode) (msg : String)
    (pos : Pos) (help : Option String) (demote first : Bool) :
    (warnOnceDiag ctx key code msg pos help demote first).subject = some key := by
  unfold warnOnceDiag diagOf Diag.of Diag.demote
  dsimp only
  split <;> rfl

private def warnOnceState (ctx : Ctx) (key : String) (code : DiagCode) (msg : String)
    (pos : Pos) (help : Option String) (demote : Bool) (st : ESt) : ESt :=
  let first := !st.warnedUnknown.contains key
  { st with
    warnedUnknown := if first then st.warnedUnknown.push key else st.warnedUnknown
    diags := st.diags.push (warnOnceDiag ctx key code msg pos help demote first) }

theorem warnOnceState_diags_exact (ctx : Ctx) (key : String) (code : DiagCode) (msg : String)
    (pos : Pos) (help : Option String) (demote : Bool) (st : ESt) :
    (warnOnceState ctx key code msg pos help demote st).diags =
      st.diags.push (warnOnceDiag ctx key code msg pos help demote
        (!st.warnedUnknown.contains key)) := rfl

private def warnOnce (ctx : Ctx) (key : String) (code : DiagCode) (msg : String) (pos : Pos)
    (help : Option String := none) (demote : Bool := false) : EM Unit :=
  modify (warnOnceState ctx key code msg pos help demote)

/-- Record a citation group's keys with their `\cite`'s span, first
occurrence per key: the no-bibliography judge's sites (elabDoc). A
top-level helper so the inline knot carries a call, not a closure. -/
private def recordCiteSites (ctx : Ctx) (keys : List String) (pos : Pos) : EM Unit :=
  modify fun st => { st with spans := keys.foldl (fun sp k =>
    if sp.cites.any (·.1 == k) then sp
    else { sp with cites := sp.cites.push (k, ⟨ctx.file, pos⟩) }) st.spans }

/-- Record a non-text object's census key and span. File and boundary
images use their source; every native picture uses a positional
`picture#k` key, including described and decorative pictures so a caption
cannot renumber a later missing alternative. -/
private def recordImageSpan (ctx : Ctx) (src : String) (pos : Pos) : EM Unit :=
  modify fun st =>
    if st.spans.images.any (·.1 == src) then st
    else { st with spans :=
      { st.spans with images := st.spans.images.push (src, ⟨ctx.file, pos⟩) } }

private def recordNativePictureSpan (ctx : Ctx) (pos : Pos) : EM Unit := do
  let k := ((← get).spans.images.filter fun e => e.1.startsWith Ir.picKeyPrefix).size
  recordImageSpan ctx (Ir.picKeyPrefix ++ toString k) pos

/-- Record a colour expression's span and value, first occurrence per
expression: the contrast judge's `-->` and the name it reports. -/
private def recordColorSpan (ctx : Ctx) (expr : String) (c : Color) (role : Bool)
    (pos : Pos) : EM Unit :=
  modify fun st =>
    if st.spans.colors.any (·.1 == expr) then st
    else { st with spans :=
      { st.spans with colors := st.spans.colors.push (expr, c, role, ⟨ctx.file, pos⟩) } }

/-- Where a coloured use came from, for the contrast judge: a role's first
use, or the first expression that resolved to an anonymous colour. -/
def colorSiteOf (colors : Array (String × Color × Bool × Span)) :
    Option String → Color → Option (String × Span)
  | some r, _ => (colors.find? (·.1 == r)).map fun (e, _, _, sp) => (e, sp)
  | none, c => (colors.find? fun (_, v, role, _) => !role && v.sameSource c).map
      fun (e, _, _, sp) => (e, sp)

/-- Record a `\bibliography` marker's span: E0503's `-->` (ReqSpans.bib). -/
private def recordBibSpan (ctx : Ctx) (src : String) (pos : Pos) : EM Unit :=
  modify fun st => { st with spans :=
    { st.spans with bib := st.spans.bib.push (src, ⟨ctx.file, pos⟩) } }

/-- **url.sty's `\urlstyle` values, as the family each names.** `tt`, `rm`
and `sf` name the mono, roman and sans families; `same` asks for the face in
force, which is no family style at all rather than a fourth family — hence
the nested `Option`. Anything else is not a url.sty value (url.sty header,
`\urlstyle`). -/
def urlStyleFamily? : String → Option (Option Ir.Style)
  | "tt" => some (some .mono)
  | "rm" => some (some .roman)
  | "sf" => some (some .sans)
  | "same" => some none
  | _ => none

/-- Reserved control words, and the code each skip earns — W0307 (pending,
a warning: a milestone owns the construct) when the skipped arguments carry
content, W0329 (config) when only layout or selection is lost. -/
def reservedCtrl : List (String × DiagCode) :=
  [("vspace", .W0329), ("noindent", .W0329),
   ("fontfallback", .W0329), ("figure", .W0307), ("pageref", .W0307)]

/-- Declarations that take a `{...}` block and are handled in the preamble. -/
def declCtrl : List String :=
  ["page", "pdfmeta", "assert", "fonts", "palette", "tokens", "style", "output",
   "theme", "chrome", "pictures", "allow"]

/-- The boundary tools the engine will run. A document declares *which* of
these draws its pictures, never an arbitrary binary: the driver executes
the named tool, so an open value would be a document running commands. -/
def picTools : List String := ["lualatex"]

/-- Preamble declarations that take one group of *inline content* rather than
a key/value block: running head and foot. -/
def runningCtrl : List String := ["runninghead", "runningfoot"]

def pageKeys : List String :=
  ["size", "width", "height", "margin", "vmargin", "hmargin",
   "textwidth", "textheight", "leading", "parskip",
   "measure", "fontsize", "bleed", "hyphenate", "justify", "protrusion",
   "expansion", "numbers", "marks", "mark-gap", "mark-thickness", "linenumbers", "modulo",
   "furnituregap", "headsep", "footskip", "rule", "trim", "bottom"]

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
   "language", "version"]

def fontKeys : List String := ["body", "sans", "mono", "math", "rm", "sf", "tt", "dir"]

/-- Named page sizes, in sp: the ISO 216 A-series at TeX's big-point
rounding (A4 595 × 842 pt, A5 420 × 595 pt) and the ANSI/US office sizes
(letter 8.5 × 11 in, legal 8.5 × 14 in = 612 × 792 / 612 × 1008 pt). -/
def pageSizes : List (String × (Sp × Sp)) :=
  [("letter", (pt 612, pt 792)),
   ("legal", (pt 612, pt 1008)),
   ("a4", (Dim.pt 595, Dim.pt 842)),
   ("a5", (Dim.pt 420, Dim.pt 595))]

/-- The slides stage a class-option list selects: beamer's `aspectratio=`
option read through `Ir.slidesStages`; absent — or naming a ratio beamer
does not — the 4:3 stage, beamer's documented default (user guide §8.1). -/
def slidesStageOf (opts : List String) : Sp × Sp :=
  (opts.findSome? fun o =>
    if o.startsWith "aspectratio=" then
      Ir.slidesStageNamed ((o.drop "aspectratio=".length).toString)
    else none).getD Ir.slidesStage43

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

/-- Which edges of a text-font command's argument get ltfntcmd's
`\maybe@ic`, as `(before, after)`. `\DeclareTextFontCommand` sets
`\check@icl` before the argument and `\check@icr` after the group; there is
neither for an empty or a lone-space argument (`\text@command`), none
before when the argument opens with `\nocorr`, none after when a `\nocorr`
follows its first token (`\check@nocorr@`), and none where the token
`\maybe@ic` reads next — the argument's first, or the one after the
group — is `,` or `.` (`\nocorrlist`). -/
def fontCmdNocorr : Raw → Bool
  | .ctrl "nocorr" _ => true
  | _ => false

def fontCmdEdges (body : List Raw) (next? : Option Raw) : Bool × Bool :=
  Ir.fontCmdEdges (· == .space) fontCmdNocorr
    (fun
      | some (.word s _) => !(s.startsWith "," || s.startsWith ".")
      | _ => true)
    body next?

/-- The argument content after ltfntcmd consumes its top-level `\nocorr`
markers. A marker inside a nested group is not one `fontCmdEdges` reads, so
it stays for that group's own elaboration rather than becoming a global
no-op command. -/
def fontCmdContent (body : Array Raw) : Array Raw :=
  body.filter fun r => !fontCmdNocorr r

/-- A text-font command's run: the styled argument, with the italic
corrections `fontCmdEdges` asks for inside it before the argument, under
the face the command selects, and after it, under the face around it. -/
def fontCmdPush (acc : Array Inline) (style : Style) (edges : Bool × Bool)
    (inner : Array Inline) : Array Inline :=
  (Ir.fontCmdInlines style edges inner).foldl Array.push acc

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
   ("LaTeX", "LaTeX"), ("TeX", "TeX"), ("LaTeXe", "LaTeX2ε"),
   ("textdegree", "°"), ("texteuro", "€"),
   -- latex.ltx's `\def\lq{`}` and `\def\rq{'}`, as the TeX quote ligatures
   -- set them (lualatex sets U+2018 and U+2019 for the two).
   ("lq", "‘"), ("rq", "’")]

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
   "underline", "uline", "ul", "varul",
   -- The phantom family, spelled out rather than spliced from
   -- `Picture.phantomCtrl`: a registry that derived itself from the family
   -- could not witness a member missing from it, which is what
   -- `phantom_rendered_covers` is for.
   "vphantom", "hphantom", "phantom"] ++
  blockOnly ++ (escapes.map (·.1)) ++ (argStyles.map (·.1)) ++
  (declStyles.map (·.1)) ++ (reservedCtrl.map (·.1)) ++ declCtrl ++
  (Lex.textSymbols.map (·.1))

/-- Built-ins a definition may never touch, whatever its body: the names
the walks' own shape depends on — grouping, definition machinery, block
boundaries, the reserved characters' escapes, the engine's declarations —
plus the underline family and the flexible-table column resolver, whose
refusal is the recorded divergence (`builtinNames`' comment). Redefining one would not change what renders
(the dispatch reads these before any user definition), so refusing loudly
(W0303) is the honest answer. Every other protected name is in
`renderedBuiltins`, where rule (b) judges the body instead. -/
def structuralNames : List String :=
  ["begin", "end", "par", "define", "ifgiven", "documentclass",
   "underline", "uline", "ul", "varul", "tabularxcolumn",
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
   "cref", "Cref", "crefrange", "Crefrange", "labelcref", "namecref", "nameCref",
   "paragraph", "subparagraph", "href", "link", "hyperlink", "hypertarget",
   "url", "nolinkurl", "hspace", "rule", "fontsize", "includegraphics", "faIcon",
   "pagenumber", "pagecount",
   "bibliography", "bibliographystyle", "textcolor",
   "refstepcounter", "stepcounter", "addtocounter", "setcounter",
   "section", "subsection", "subsubsection",
   "vphantom", "hphantom", "phantom"] ++ Ir.natbibCites.map (·.1) ++
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

/-- The invariant the phantom defect wanted, registry half: a command whose
whole meaning is *size without ink* is a name this dispatch gives a meaning
of its own. The family (`Picture.phantomCtrl`, where the label salvage reads
it) and the two registries are written out apart on purpose — a registry
spliced from the family would read `xs ⊆ A ++ xs ++ B` and could not witness
a member missing from it, which is the shape this statement had on its first
attempt and the reason it is spelled this way now.

What it does *not* reach is the arm: a name can be registered here and still
fall through to the unknown-command recovery, whose rule is "keep the braced
arguments as text" and which is how `\vphantom{y}`'s letter reached the page.
The arm's own gate is `phantomReservesWidth`, held to the family by
`phantom_axes_set_eq`; the page is `phantomChecks`, over `Layout.Out`. Three
statements, because no one of them can see the other two's failure. -/
theorem phantom_rendered_covers :
    (Picture.phantomCtrl.all fun n =>
      renderedBuiltins.contains n && builtinNames.contains n) = true := by
  decide +kernel

/-- The same family against the *salvage* tables: every member's group is a
naming argument (`Ir.floorNamedArgs`), so a recovery path that keeps content
groups — the math floor, a picture label — drops a phantom's group instead
of setting it. This one held before the fix as well: it is the reason
`$a\phantom{=}b$` never shipped an `=`, and it stays here as drift
insurance, not as the defect's witness. -/
theorem phantom_named_covers :
    (Picture.phantomCtrl.all fun n =>
      (Ir.floorNamedArgs.lookup n) == some 1) = true := by
  decide +kernel

/-- Which axes each member of the family reserves, which is the whole of
what tells them apart (plain.tex ll. 1024-1031): `\vphantom{x}` takes x's
height and depth and no width, `\hphantom{x}` takes its width and no height
or depth, `\phantom{x}` takes all three. None takes ink — that is what makes
them one family. Getting a column wrong here is a subtler defect than the
one this table was written for: an `\hphantom` that propped a height, or a
`\vphantom` that claimed a width, would be wrong in a direction no page
shows plainly.

This table is also the *arm's gate*: the dispatch fires on a key of this
list, not on the family list, so `phantom_axes_set_eq` below is what ties
the arm to the family. -/
structure PhantomAxes where
  /-- Reserves the argument's width. No width this engine sets was
  undeclared, so this axis has no carrier and is a named loss. -/
  width : Bool
  /-- Reserves the argument's height and depth. Already in force when the
  argument borrows the running face — `Layout.line_box_glyph_free` plus
  idempotence of the line box's componentwise `max` — which is the
  hypothesis `phantomBorrows` checks rather than assumes. -/
  extent : Bool
  deriving Repr, BEq, Inhabited

def phantomAxes : List (String × PhantomAxes) :=
  [("vphantom", ⟨false, true⟩), ("hphantom", ⟨true, false⟩),
   ("phantom", ⟨true, true⟩)]

/-- Family and axes, exactly each other's keys, and one row per key. This is
the statement that reaches the arm: the dispatch fires on this table, so a
member added to `Picture.phantomCtrl` and not here does not merely lose a
default — it is not dispatched at all, and falls to the unknown-command
recovery that shipped the letter. The no-duplicates conjunct pins the value
too: `lookup` takes the first row, so two rows for one name would leave the
axes decided by list order rather than by the table. The last conjunct is
the family's defining property — no member inks, so none of them is a
content wrapper that wandered in. -/
theorem phantom_axes_set_eq :
    ((Picture.phantomCtrl.all fun n => (phantomAxes.lookup n).isSome) &&
      (phantomAxes.all fun e => Picture.phantomCtrl.contains e.1) &&
      (phantomAxes.map (·.1)).Nodup &&
      (phantomAxes.all fun e => e.2.width || e.2.extent)) = true := by
  decide +kernel

/-- TU's accent and symbol tables as maps: the inline dispatch asks them of
every control word the hand tables before them do not answer, and a list
walk there cost `bench/underline.tex` 7 ms of 515. -/
def accentMap : Std.HashMap String Char := Std.HashMap.ofList TextSymData.accents

def textSymbolMap : Std.HashMap String Char := Std.HashMap.ofList TextSymData.symbols

/-- TeX's accent commands the engine composes to NFC: the combining mark
each adds to its base, from TU's accent table (`TextSymData.accents`) —
one table with .bib values (`Bib.accentOf`), so a name renders identically
in text and in a bibliography entry. -/
def accentMarkOf (name : String) : Option Char :=
  accentMap[name]?

/-- The one-character word commands (`\ss`, `\ae`, `\o`…), the same table
`.bib` values read (`Bib.charCommands`), and TU's text symbols
(`TextSymData.symbols`: `\S`, `\dag`, `\textbullet`, `\OE`…), folded into
one lookup with the escape table: all splice literal text. -/
def escapeOf (name : String) : Option String :=
  match escapes.lookup name with
  | some lit => some lit
  | none =>
    match (Bib.charCommands.find? (·.1 == name)).map (·.2) with
    | some lit => some lit
    | none => textSymbolMap[name]?.map (String.ofList [·])

/-- The letter a command stands for as an accent's base: `\i` and `\j` are
the dotted letters (tuenc.def composes `\'\i` as í: the dotless letter
exists only to carry an accent), and a one-character command is its
character (`\'\AE` is Ǽ). -/
def accentBase (d : String) : Option Char :=
  if d == "i" then some 'i' else if d == "j" then some 'j'
  else match (escapeOf d).map (·.toList) with
    | some [c] => some c
    | _ => none

/-- The composed text of an accent command applied to what follows: the
first letter of an adjacent word (`\'elair` → "élair"), a one-letter group
(`\'{e}`), a command base (`\'{\i}`, `\'\AE`), or an empty group (`\^{}` →
"^", TU's empty-base composite). `none` — a shape or a pair with no
precomposed scalar — falls through to the ordinary dispatch, so nothing new
is dropped and an unknown pair still warns by name. -/
def accentCompose (name : String) (r : Parse.Raw) : Option String := do
  let mark ← accentMarkOf name
  let one (b : Char) : Option String := (Bib.composeAccent mark b).map (String.ofList [·])
  match r with
  | .word s _ =>
    match s.toList with
    | b :: rest => (Bib.composeAccent mark b).map fun c => String.ofList (c :: rest)
    | [] => none
  | .ctrl d _ => accentBase d >>= one
  | .group body _ =>
    match body.toList with
    | [] => (TextSymData.emptyBase.lookup name).map (String.ofList [·])
    | [.word s _] =>
      match s.toList with
      | [b] => one b
      | _ => none
    | [.ctrl d _] => accentBase d >>= one
    | _ => none
  | _ => none

mutual

/-- Does a phantom's argument borrow only the face, size and raise the line
already carries? That is the *hypothesis* under which the height and depth a
phantom props are already in force — `Layout.line_box_glyph_free` says the
line box is the metric extent of the (font, size, raise) triples on the line
and never a glyph, and the box is a componentwise `max`, which is idempotent
for a triple the line already holds. Under this predicate the construct is
inert; outside it the extent really does go unreserved, and the arm names
that rather than dropping it in silence.

Words, spaces, reserved symbols, accents, escapes and named symbols set
characters in the running face, and which characters they are is exactly
what the line box does not read. A size switch, a face switch, a raise,
math, an environment: each is a triple the line may not carry.

Conservative in the safe direction — an unknown control word answers
`false`, so a construct this engine gains later is named until someone
decides it borrows. The cost is a name where nothing was lost; the
alternative is silence where something was. -/
def phantomBorrowsOne : Raw → Bool
  | .word _ _ | .space | .sym _ _ => true
  | .group body _ => phantomBorrowsList body.toList
  | .ctrl n _ =>
    (accentMarkOf n).isSome || (escapeOf n).isSome ||
      (Lex.textSymbols.lookup n).isSome
  | _ => false

/-- The `List` companion: the tail drives the recursion, the group's body is
a field of its head, so the walk is structural and owes no measure —
`Compat.boxShape`'s neighbour `boundaryLevel`/`boundaryRaw` is the shape. -/
def phantomBorrowsList : List Raw → Bool
  | [] => true
  | r :: rest => phantomBorrowsOne r && phantomBorrowsList rest

end

/-- A phantom's whole argument, as the predicate above judges it. -/
def phantomBorrows (raws : Array Raw) : Bool := phantomBorrowsList raws.toList

/-- The declaration styles by name, plus two unforgeable markers (`@` never
lexes into a control word): `@lang:fr` → `Style.lang "fr"` (Compat's
rewrite of `\selectlanguage`) and `@series:l` → `Style.series .l`
(Compat's rewrite of `\fontseries`, already validated there — an
unparsable code never becomes a marker). All apply to the rest of the
scope, so one dispatch arm serves them all. -/
def declStyleOf (name : String) : Option Ir.Style :=
  if name.startsWith "@lang:" then
    some (.lang ((name.drop "@lang:".length).toString))
  else if name.startsWith "@series:" then
    (Ir.Weight.parseSeries ((name.drop "@series:".length).toString)).map
      fun (w, _) => .series w
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

/-- Content between `column`s that is real stray content, deciding whether
the run flushes the accumulated columns row: space never is, and neither
is `\hfill` — beamer's own columns row opens with `\hbox{}\hfill` and
closes every column with one (beamerbaseframecomponents.sty,
`beamer@colentrycode` and `beamer@columnenv`'s end code), so a fill
standing between columns is glue in the row: the gutter the columns
layout already distributes, never a paragraph. Treating it as stray
content flushed the row and stacked each column in its own `.columns`
block — the A0 poster's four-page spill. A fill inside real stray
content still rides with that content into its paragraph. -/
private def isColumnStray (r : Raw) : Bool :=
  !isSpaceOrPar r && !(r matches .ctrl "hfill" _)

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

/-- An environment's halves lose only their outer edges — the begin code's
lead and the end code's tail. The edges facing the body are content, as TeX
reads them: `{Lead words }` ends in a space before the body, so the body's
first word is set apart from the code's last, and a body bringing its own
space there sets a second one, as TeX does (`mergeText`). -/
private def trimLead (raws : Array Raw) : Array Raw :=
  raws.extract (spanRaws raws 0 isSpaceOrPar) raws.size

private def trimTail (raws : Array Raw) : Array Raw :=
  raws.extract 0 (spanRawsEnd raws isSpaceOrPar)

/-- A defined environment from its halves, with the space rules TeX's own
commands state at its seams, each command spent here so none reaches a
half as an unknown word: `\ignorespaces` closing the begin code skips the
body's leading spaces (TeXbook ch. 24); environ's mark there trims both of
the body's edges (environ.sty `\env@save`: `\trim@spaces`); and
`\ignorespacesafterend` in the end code skips the spaces after
`\end{name}` (latex.ltx `\end`: `\if@ignore \@ignorefalse \ignorespaces`). -/
private def envOfHalves (name : String) (params : Array Param) (b e : Array Raw)
    (limit : Nat) : UserEnv :=
  let isCtrl (n : String) (r : Raw) : Bool := match r with
    | .ctrl m _ => m == n
    | _ => false
  let b := trimLead b
  let e := trimTail e
  let ink := spanRawsEnd b (· matches .space)
  let closing := if ink > 0 then b[ink - 1]? else none
  let environ := closing.any (isCtrl Compat.environBodyMark)
  let lead := environ || closing.any (isCtrl "ignorespaces")
  { name, params, cmdLimit := limit,
    beginBody := if lead then b.extract 0 (ink - 1) else b
    endBody := e.filter (!isCtrl "ignorespacesafterend" ·)
    ignoresLead := lead, trimsTail := environ,
    ignoresAfterEnd := e.any (isCtrl "ignorespacesafterend") }

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

/-- How a degraded formula's recovery reads, so the warning and the page
agree: the floor is the formula's text content, unless that content is
nothing at all, where a declared placeholder ships instead
(`Ir.floorInk_accounts`). Saying "sets as its text content" over a page
showing `[…]` would be a diagnostic describing a recovery that did not
happen. -/
private def floorWording (src : String) : String :=
  if (Ir.floorChars src).isEmpty then
    "sets as a placeholder: it has no text content"
  else "sets as its text content"

/-- One parser note to its own diagnostic: the two losses a formula can
carry while still rendering are different kinds, so each takes its own
code. `where` prefixes the environment's name when the note came from an
alignment body. -/
private def mathNote (ctx : Ctx) (note : MathParse.Note) (where_ : String)
    (pos : Pos) : EM Unit := do
  match note with
  | .ragged msg =>
    warnOnce ctx ("math:ragged:" ++ msg) .W0014
      (if where_.isEmpty then s!"alignment {msg}" else where_ ++ msg) pos
  | .styleDropped what =>
    warnOnce ctx ("math:style:" ++ what) .W0385
      s!"{where_}{what} inside math sets in the surrounding style" pos
  | .constructFloored what =>
    warnOnce ctx ("math:contain:" ++ what) .W0389
      s!"{where_}math with {what} is not rendered yet; its content operand sets \
in its place" pos

/-- One formula: parsed into math atoms when this slice can model it, kept
as its text content with a warning naming the construct when it cannot —
out of scope is a named warning, never a silent drop, and never its source
on the page (`Ir.mathFloor`). User commands expand first
(`expandMathList`), so a `\define`d macro renders instead of degrading its
formula. A ragged alignment row inside the formula (an `array`) is W0014,
padded; a colour or font change the math list cannot carry is W0385, its
content kept. -/
private def elabMathInline (ctx : Ctx) (display : Bool) (body : Array Parse.Raw)
    (pos : Pos) : EM Ir.Inline := do
  let expanded := expandMathList ctx.user ctx.limit #[] body.toList
  match MathParse.parseMath display expanded with
  | .ok (l, notes) =>
    for note in notes do
      mathNote ctx note "" pos
    return .formula display (Parse.rawSrc body) l
  | .error what =>
    let src := Parse.rawSrc body
    warnOnce ctx ("math:" ++ what) .W0012
      s!"math with {what} is not rendered yet; the formula {floorWording src}" pos
    return .math display src

/-- One alignment environment (`align`/`gather` and their starred forms):
its rows parsed into one display grid formula. A construct the parser
cannot model keeps the whole environment as its text content, named
(W0012); a ragged row is W0014, padded; a colour or font change the math
list cannot carry is W0385, its content kept; a numbered form warns W0015
once — the equation numbers are owed, the mathematics is not. -/
private def elabMathEnv (ctx : Ctx) (name : String) (kind : Math.GridKind)
    (numbered : Bool) (body : Array Parse.Raw) (pos : Pos) : EM Ir.Inline := do
  let expanded := expandMathList ctx.user ctx.limit #[] body.toList
  match MathParse.parseMathRows kind expanded with
  | .ok (l, notes) =>
    for note in notes do
      mathNote ctx note s!"'\{{name}}': " pos
    if numbered then
      warnOnce ctx ("math:eqnum:" ++ name) .W0015
        s!"equation numbers are not rendered yet; '\{{name}}' sets unnumbered" pos
        (help := if (alignEnvs.lookup name).any (·.2)
          then some s!"'\{{name}*}' spells the unnumbered form, which renders the same"
          else none)
    return .formula true (Parse.rawSrc body) l
  | .error what =>
    let src := Parse.rawSrc body
    warnOnce ctx ("math:" ++ what) .W0012
      s!"math with {what} is not rendered yet; '\{{name}}' {floorWording src}" pos
    return .math true src

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

/-- Is this raw an overlay spec word? The lexer keeps `<2->` one word. -/
private def specWord? : Raw → Option String
  | .word w _ => if w.startsWith "<" && w.endsWith ">" then some w else none
  | _ => none

private def flushText (acc : Array Inline) (sb : String) : Array Inline :=
  if sb == "" then acc else acc.push (.text sb)

/-- TeX's `\unskip` at a point of an inline run: the pending text, else the
run's last text, without the space it ends with. -/
private def unskipText (acc : Array Inline) (sb : String) : Array Inline :=
  if sb != "" then flushText acc sb.trimAsciiEnd.toString
  else if let some (.text s) := acc.back? then flushText acc.pop s.trimAsciiEnd.toString
  else acc

/-- The key a text-mode `\qedhere` mark stands under until its proof sets it
(`thmClose`): no document can spell a NUL, so no `\label` collides, and the
proof replaces every one it holds before a backend sees it. -/
def qedHereKey : String := "\u0000qedhere"

/-- amsthm.sty's `\qed` in text, `\hbox{}\nobreak\hfill\quad\hbox{\qedsymbol}`,
with the mark's place (`qedHereKey`) for the symbol. -/
private def qedHereRun : Array Inline :=
  #[.strut {}, .fill, .text "\u2003", .label qedHereKey]

/-- Adjacent text runs join into one, every space kept: where both bring a
space to the seam — an environment half's edge meeting its body's, a macro
body's tail meeting the text after it — TeX sets two interword glues, and
so does the joined run. -/
private def mergeText (xs : Array Inline) : Array Inline := Id.run do
  let mut out : Array Inline := #[]
  for x in xs do
    match x, out.back? with
    | .text s, some (.text t) => out := out.pop.push (.text (t ++ s))
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

/-- The source between the brackets `scanBracketArg` took from `i` to `k`. -/
private def bracketSrc (raws : Array Raw) (i k : Nat) : String :=
  rawSrc (raws.extract (skipSpaces raws i + 1) (k - 1))

/-- The point a box's `[pos]` stands it on its row's baseline by (latex.ltx
`\@iiiparbox`: `t` builds a `\vtop`, `b` a `\vbox`, `c` a `\vcenter`;
beamer's `column` and `columns` add `T`, the top edge). `none` for a
spelling no box reads. -/
private def boxPosOf (src : String) : Option Ir.BoxPos :=
  match src.trimAscii.toString with
  | "t" => some .first
  | "c" => some .center
  | "b" => some .last
  | "T" => some .top
  | _ => none

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
-- erased at runtime — no artifact reads a weight. Every component of the
-- knot's measure — weight, pars, items — is a pointwise `Nat` measure
-- summed over a list, so each list-sum fact is stated once below over the
-- pointwise measure `μ` and instantiated per component.

/-- The sum of a pointwise measure over a list: the one shape every
component of the knot's termination measure shares. -/
private def measList (μ : α → Nat) : List α → Nat
  | [] => 0
  | x :: rest => μ x + measList μ rest

private theorem measList_append (μ : α → Nat) (a b : List α) :
    measList μ (a ++ b) = measList μ a + measList μ b := by
  induction a with
  | nil => simp [measList]
  | cons x xs ih => simp [measList, ih]; omega

private theorem measList_push (μ : α → Nat) (a : Array α) (x : α) :
    measList μ (a.push x).toList = measList μ a.toList + μ x := by
  simp [Array.toList_push, measList_append, measList]

private theorem measList_drop_le (μ : α → Nat) (l : List α) (i : Nat) :
    measList μ (l.drop i) ≤ measList μ l := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ n =>
      have := ih n
      simp only [List.drop_succ_cons, measList]
      omega

private theorem measList_take_le (μ : α → Nat) (l : List α) (i : Nat) :
    measList μ (l.take i) ≤ measList μ l := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp [measList]
    | succ n =>
      have := ih n
      simp only [List.take_succ_cons, measList]
      omega

private theorem measList_mem_le {μ : α → Nat} {l : List α} {x : α}
    (h : x ∈ l) : μ x ≤ measList μ l := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp only [measList]
    rcases List.mem_cons.mp h with h | h
    · subst h; omega
    · have := ih h; omega

private theorem measList_le_of_le {μ ν : α → Nat} (h : ∀ x, μ x ≤ ν x)
    (l : List α) : measList μ l ≤ measList ν l := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    have := h x
    simp only [measList]
    omega

private theorem measList_extract_le (μ : α → Nat) (body : Array α) (a b : Nat) :
    measList μ (body.extract a b).toList ≤ measList μ body.toList := by
  rw [Array.toList_extract]
  exact Nat.le_trans (measList_take_le ..) (measList_drop_le ..)

/-- A measure component over the knot spine's slice: the pointwise sum
from `i` on. -/
private def sliceMeas (μ : α → Nat) (raws : Array α) (i : Nat) : Nat :=
  measList μ (raws.toList.drop i)

private theorem sliceMeas_here (μ : α → Nat) (raws : Array α) {i : Nat}
    (h : i < raws.size) :
    sliceMeas μ raws i = μ raws[i] + sliceMeas μ raws (i + 1) := by
  unfold sliceMeas
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp [measList]

private theorem sliceMeas_le (μ : α → Nat) (raws : Array α) {i j : Nat}
    (hij : i ≤ j) : sliceMeas μ raws j ≤ sliceMeas μ raws i := by
  unfold sliceMeas
  rw [show raws.toList.drop j = (raws.toList.drop i).drop (j - i) by
    rw [List.drop_drop]; congr 1; omega]
  exact measList_drop_le ..

private theorem sliceMeas_end (μ : α → Nat) (raws : Array α) {j : Nat}
    (h : raws.size ≤ j) : sliceMeas μ raws j = 0 := by
  unfold sliceMeas
  rw [List.drop_eq_nil_of_le (by simpa using h)]
  rfl

/-- An element standing anywhere at or past `i` measures no more than the
slice from `i`. -/
private theorem sliceMeas_elem_le {μ : α → Nat} {raws : Array α} {j : Nat}
    {x : α} (h : raws[j]? = some x) {i : Nat} (hij : i ≤ j) :
    μ x ≤ sliceMeas μ raws i := by
  obtain ⟨hj, hx⟩ := Array.getElem?_eq_some_iff.mp h
  have h1 := sliceMeas_here μ raws hj
  have h2 := sliceMeas_le μ raws hij
  rw [hx] at h1
  omega

private theorem sliceMeas_extract_le (μ : α → Nat) (raws : Array α) (a b : Nat) :
    measList μ (raws.extract a b).toList ≤ sliceMeas μ raws a := by
  rw [Array.toList_extract]
  exact measList_take_le ..

/-- Replacing the element at `i` by a run that measures strictly below it
strictly lowers the slice measure from `i`: the shape of every splice
edge. -/
private theorem sliceMeas_splice_lt {μ : α → Nat} {raws : Array α} {i : Nat}
    (h : i < raws.size) {seg : Array α}
    (hseg : measList μ seg.toList < μ raws[i]) :
    sliceMeas μ (raws.extract 0 i ++ seg ++ raws.extract (i + 1) raws.size) i
      < sliceMeas μ raws i := by
  have hlen : (raws.extract 0 i).toList.length = i := by
    simp [Array.length_toList]; omega
  have hdrop : (raws.extract 0 i ++ seg
      ++ raws.extract (i + 1) raws.size).toList.drop i
      = seg.toList ++ (raws.extract (i + 1) raws.size).toList := by
    simp only [Array.toList_append, List.append_assoc]
    rw [List.drop_append_of_le_length (by omega)]
    rw [List.drop_eq_nil_of_le (by omega)]
    simp
  have h1 := sliceMeas_here μ raws h
  have h3 : measList μ (raws.extract (i + 1) raws.size).toList
      ≤ measList μ (raws.toList.drop (i + 1)) := by
    rw [Array.toList_extract]
    exact measList_take_le ..
  unfold sliceMeas at h1 ⊢
  rw [hdrop, measList_append]
  omega

-- The weight component of the knot's measure.

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

/-- The mutual recursion above is `measList rawWeight`: the bridge every
weight fact crosses into the parametrized family. -/
private theorem rawWeightList_eq (l : List Raw) :
    rawWeightList l = measList rawWeight l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [rawWeightList, measList, ih]

/-- The measure component the knot's spine recurses on: the weight of the
slice from `i`. Kept definitionally over `rawWeightList`, so `sliceWeight a 0`
still unfolds to the whole-array weight the knot's `have` facts spell. -/
private def sliceWeight (raws : Array Raw) (i : Nat) : Nat :=
  rawWeightList (raws.toList.drop i)

private theorem sliceWeight_eq (raws : Array Raw) (i : Nat) :
    sliceWeight raws i = sliceMeas rawWeight raws i := by
  unfold sliceWeight sliceMeas; rw [rawWeightList_eq]

private theorem rawWeightList_append (a b : List Raw) :
    rawWeightList (a ++ b) = rawWeightList a + rawWeightList b := by
  simp only [rawWeightList_eq]; exact measList_append ..

private theorem rawWeightList_filter_monotone (p : Raw → Bool) (xs : List Raw) :
    rawWeightList (xs.filter p) ≤ rawWeightList xs := by
  induction xs with
  | nil => simp [rawWeightList]
  | cons x xs ih =>
    simp only [List.filter_cons]
    split <;> simp only [rawWeightList] <;> omega

private theorem rawWeight_pos (r : Raw) : 1 ≤ rawWeight r := by
  cases r <;> simp [rawWeight]

private theorem sliceWeight_here (raws : Array Raw) {i : Nat} (h : i < raws.size) :
    sliceWeight raws i = rawWeight raws[i] + sliceWeight raws (i + 1) := by
  simp only [sliceWeight_eq]; exact sliceMeas_here rawWeight raws h

/-- The workhorse: any strict advance strictly lightens the slice. -/
private theorem sliceWeight_lt (raws : Array Raw) {i j : Nat}
    (hi : i < raws.size) (hij : i < j) : sliceWeight raws j < sliceWeight raws i := by
  have h1 := sliceMeas_here rawWeight raws hi
  have h2 := sliceMeas_le rawWeight raws (show i + 1 ≤ j by omega)
  have h3 := rawWeight_pos raws[i]
  simp only [sliceWeight_eq]
  omega

/-- An element standing anywhere at or past `i` weighs no more than the
slice from `i`. -/
private theorem elem_weight_le {raws : Array Raw} {j : Nat} {r : Raw}
    (h : raws[j]? = some r) {i : Nat} (hij : i ≤ j) :
    rawWeight r ≤ sliceWeight raws i := by
  simp only [sliceWeight_eq]; exact sliceMeas_elem_le h hij

/-- An extracted tail of a body weighs no more than the body. -/
private theorem extract_weight_le (body : Array Raw) (a b : Nat) :
    rawWeightList (body.extract a b).toList ≤ rawWeightList body.toList := by
  simp only [rawWeightList_eq]; exact measList_extract_le ..

/-- The unknown-environment splice strictly lightens the slice: the kept
body is lighter than the wrapper it replaces, whatever prefix its argument
scan dropped. -/
private theorem sliceWeight_splice {raws : Array Raw} {i : Nat}
    (h : i < raws.size) {name : String} {body : Array Raw} {pos : Pos}
    (hr : raws[i] = .env name body pos) (keptFrom : Nat) :
    sliceWeight (raws.extract 0 i ++ body.extract keptFrom body.size
      ++ raws.extract (i + 1) raws.size) i < sliceWeight raws i := by
  simp only [sliceWeight_eq]
  refine sliceMeas_splice_lt h ?_
  have h2 := measList_extract_le rawWeight body keptFrom body.size
  rw [hr]
  simp only [rawWeight, rawWeightList_eq]
  omega

/-- The measure of every command body the walk can see: the elabBlocks
measure term that makes a user-command expansion decrease — the expanded
body leaves this sum (`visGo_expand`), and what a body `\define` adds to it
is exactly the body the walk paid a heavier group for (`bindCmd_visGo`).
The old `(envLimit, limit, …)` lex is unsound for the block walk: `limit`
rises across a define on the spine; this sum replaces it. Parametrized by
the pointwise body measure `f`; the weight and pars components
instantiate it. -/
private def visGo (f : UserCmd → Nat) (user : Array UserCmd) : Nat → Nat
  | 0 => 0
  | k + 1 => (if h : k < user.size then f user[k] else 0) + visGo f user k

private theorem visGo_mono (f : UserCmd → Nat) (user : Array UserCmd)
    {a b : Nat} (h : a ≤ b) : visGo f user a ≤ visGo f user b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · subst heq; exact Nat.le_refl _
    · have h2 := ih (by omega)
      simp only [visGo]
      omega

private theorem visGo_congr {f : UserCmd → Nat} {u v : Array UserCmd} {n : Nat}
    (h : ∀ m, m < n → u[m]? = v[m]?) : visGo f u n = visGo f v n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have h1 := h m (by omega)
    have h2 := ih fun k hk => h k (by omega)
    simp only [visGo]
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

/-- The weight component of the visible sum. -/
private def visWeightGo (user : Array UserCmd) : Nat → Nat :=
  visGo (fun cmd => rawWeightList cmd.body.toList) user

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

/-- Expanding a visible command moves its measure out of the visible sum:
the body recursed into, plus everything still visible to the callee, never
exceeds what the caller's sum already carried. -/
private theorem visGo_expand {f : UserCmd → Nat} {ctx : Ctx} {name : String}
    {k : Nat} {cmd : UserCmd} (h : lookupUser ctx name = some (k, cmd)) :
    f cmd + visGo f ctx.user k ≤ visGo f ctx.user ctx.limit := by
  have hlt := lookupUser_lt h
  have hfound := lookupUserGo_found h
  obtain ⟨hk, hbody⟩ := Array.getElem?_eq_some_iff.mp hfound
  have hstep : visGo f ctx.user (k + 1) = f cmd + visGo f ctx.user k := by
    simp only [visGo, hk, dite_true, hbody]
  have hmono := visGo_mono f ctx.user (show k + 1 ≤ ctx.limit by omega)
  omega

/-- Expanding a visible command moves its weight out of the visible sum. -/
private theorem visWeight_expand {ctx : Ctx} {name : String} {k : Nat}
    {cmd : UserCmd} (h : lookupUser ctx name = some (k, cmd)) :
    rawWeightList cmd.body.toList + visWeightGo ctx.user k
      ≤ visWeightGo ctx.user ctx.limit := by
  unfold visWeightGo
  exact visGo_expand (f := fun cmd => rawWeightList cmd.body.toList) h

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

/-- Whether a paragraph break inside inline content separates here: yes,
unless a space is already there. A group body keeps a deliberate leading
space (`{ (x)}`); a paragraph's own edges are trimmed by `mkPara`, not here. -/
private def needsSep (acc : Array Inline) (sb : String) : Bool :=
  if sb.isEmpty then
    match acc.back? with
    | some (.text t) => !t.endsWith " "
    | _ => true
  else !sb.endsWith " "

/-- Whether a space token separates here. TeX's input reader makes one
token of a run of blanks and skips the blanks after a control space
(TeXbook ch. 8, state S), so a space against one this scan already holds
adds nothing — the one collapse, a splice's two runs included. A space
after anything else is the second glue TeX sets there too: after the text
a group, a macro or an environment half brought (`{word } next` sets two).
A paragraph's own edges are trimmed by `mkPara`, not here. -/
private def spaceSeps (sb : String) : Bool := !sb.endsWith " "

/-- The one writer of the label store: the flow-ordered table and its key
set move together, so no caller can leave them disagreeing. -/
private def labelStep (st : ESt) (key : String) (target : Option Ir.RefBinding) : ESt :=
  { st with
    labels := st.labels.push (key, target)
    labelKeys := st.labelKeys.insert key }

/-- **The key set is the table's key set.** The duplicate test reads the
set and the backends read the table, so the two must answer the same
question about every key; this is that the one writer keeps them equal,
and `labelKeys_set_eq_empty` is that they start equal. Without it a
`\label` could be accepted twice, or refused once, with nothing to
notice — the set is the only part of this store that can lie. -/
private theorem labelStep_set_eq (st : ESt) (key k : String)
    (target : Option Ir.RefBinding)
    (h : st.labelKeys.contains k = st.labels.any (·.1 == k)) :
    (labelStep st key target).labelKeys.contains k
      = (labelStep st key target).labels.any (·.1 == k) := by
  simp only [labelStep, Std.HashSet.contains_insert, Array.any_push, h]
  exact Bool.or_comm _ _

/-- The store starts with both faces empty, the base case that with
`labelStep_set_eq` makes the equality hold at every point of elaboration. -/
private theorem labelKeys_set_eq_empty (k : String) :
    (∅ : Std.HashSet String).contains k
      = (#[] : Array (String × Option Ir.RefBinding)).any (·.1 == k) := by
  simp

/-- Record one `\label` binding. The first declaration of a key wins,
LaTeX's behaviour; a second is W0350 where it stands and binds nothing. -/
private def recordLabel (ctx : Ctx) (key : String) (target : Option Ir.RefBinding)
    (pos : Pos) : EM Unit := do
  let st ← get
  if st.labelKeys.contains key then
    diag ctx .W0350 s!"'{key}' is already a \\label'ed key; the first wins" (some pos)
      (help := s!"one \\label\{{key}} per key: give this one its own name")
  else
    modify fun st => labelStep st key target

/-- Strip a display-math body's metadata before the math parser sees it:
top-level `\label{...}` keys (returned for binding to the display's
number), `\nonumber`/`\notag` (amsldoc §3: a numbered form opts out), and
the first `\tag{t}`/`\tag*{t}` (amsldoc §3.4: the tag takes the number's
place, parenthesised unless starred, and steps no counter), returned as its
argument's raws for the caller to set as text. None is mathematics; left
in place they would push the whole formula into the W0012 source-text
degradation — with the label spelled inside the rendered text — or set a
tag inside the formula. A second `\tag` stays, so the containment that
names it still does. -/
private def stripMathMeta (ctx : Ctx) (body : Array Raw) :
    EM (Array Raw × Array String × Bool × Option (Array Raw × Bool)) := do
  let mut out : Array Raw := #[]
  let mut keys : Array String := #[]
  let mut nonum := false
  let mut tag : Option (Array Raw × Bool) := none
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
      | .ctrl "tag" pos =>
        let j := skipSpaces body (i + 1)
        let (star, k) := match body[j]? with
          | some (.word "*" _) => (true, skipSpaces body (j + 1))
          | _ => (false, j)
        match body[k]?, tag with
        | some (.group tagRaw _), none =>
          tag := some (tagRaw, star)
          i := k + 1
        | _, _ =>
          out := out.push (.ctrl "tag" pos)
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
  return (out, keys, nonum, tag)

/-- One source length through the shared parser. Dimension consumers admit
only rigid absolute literals; local measures remain typed until layout. -/
private def affineLength (ctx : Ctx) (admits : Measure → Bool) (src : String) :
    Except String (Affine Measure) := do
  let e ← Decl.parseAffineLengthExprFor
    (ctx.tokens.entries ++ ctx.engineTokens) admits src
  if e.rigidAbsolute then return e
  throw "rubber and font-relative terms are not available in this length context"

/-- One `p{...}` column width, resolved against the table's local measure. -/
private def colWidth (ctx : Ctx) (src : String) : Except String Ir.ColWidth := do
  let e ← affineLength ctx (· != .textHeight) src
  return .sized e

private def tableTarget (ctx : Ctx) (src : String) : Except String Ir.TableTarget := do
  let e ← affineLength ctx (· != .textHeight) src
  return .sized e

/-- The `tabular` column spec: `l`/`c`/`r` natural columns, `p{width}`
(and `m`/`b`, set as `p`: the engine has no per-cell vertical alignment),
`@{}` deleting the outer pad on its edge, `|` warned and never drawn —
"Never, ever use vertical rules" (booktabs.dtx §The layout of formal
tables). Returns the columns, the outer-pad flags, and warnings as
(key, message, help) for the caller's `warnOnce`. -/
private def parseColSpec (ctx : Ctx) (spec : Array Raw)
    (flexTarget : Option Ir.TableTarget := none) :
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
          | 'X' =>
            match flexTarget with
            | some target => cols := cols.push { width := .flex target, align := .left }
            | none =>
              warns := warns.push ("colspec",
                "unsupported column type 'X'; set as 'l'", "load tabularx and use its environment")
              cols := cols.push { width := .natural, align := .left }
          | 'p' | 'm' | 'b' =>
            let widthGroup := if ci == last then
              match spec[i + 1]? with
              | some (.group g _) => some (Parse.rawSrc g)
              | _ => none
            else none
            let mut width : Ir.ColWidth := .natural
            if let some src := widthGroup then
              match colWidth ctx src with
              | .ok cw => width := cw
              | .error why =>
                warns := warns.push ("pwidth",
                  s!"unreadable column width '{src}': {why}; the column takes \
the full measure",
                  "use sums, differences, scalar products, local horizontal measures, or absolute lengths")
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
  simp only [sliceWeight_eq]; exact sliceMeas_le rawWeight raws hij

private theorem extract_slice_le (raws : Array Raw) (a b : Nat) :
    rawWeightList (raws.extract a b).toList ≤ sliceWeight raws a := by
  rw [rawWeightList_eq, sliceWeight_eq]; exact sliceMeas_extract_le ..

private theorem extract_lt_slice {raws : Array Raw} {i a : Nat} (b : Nat)
    (h : i < raws.size) (ha : i < a) :
    rawWeightList (raws.extract a b).toList < sliceWeight raws i :=
  Nat.lt_of_le_of_lt (extract_slice_le raws a b) (sliceWeight_lt raws h ha)

/-- A defined environment's body from `j` (past its arguments), its edges
as the definition reads them (`UserEnv.ignoresLead`, `trimsTail`). -/
private def envBody (env : UserEnv) (body : Array Raw) (j : Nat) : Array Raw :=
  let lo := if env.ignoresLead then skipSpaces body j else j
  body.extract lo (if env.trimsTail then spanRawsEnd body (· matches .space) else body.size)

private theorem envBody_le (env : UserEnv) (body : Array Raw) (j : Nat) :
    rawWeightList (envBody env body j).toList ≤ sliceWeight body 0 :=
  Nat.le_trans (extract_slice_le body _ _) (sliceWeight_le body (Nat.zero_le _))

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

/-- One citation note, the `[...]` run at `j`, elaborated by `el` — the
knot's own inline elaborator, handed the weight fact its caller's measure
needs: the note's text and the index past the run and its spaces, or
`none` at the same index when no bracket opens there. An unclosed run
takes the rest, as the option collectors do. -/
private def citeNote (raws : Array Raw) (j w : Nat) (hw : sliceWeight raws j ≤ w)
    (el : (sub : Array Raw) → rawWeightList sub.toList < w → EM (Array Inline)) :
    EM (Option String × { k : Nat // j ≤ k }) := do
  match hj : raws[j]? with
  | some (.sym '[' _) =>
    have hjlt := getElem?_lt hj
    let ⟨c, hc⟩ : { c : Nat // j < c } := match hcl : closeBracketFrom raws (j + 1) with
      | some c => ⟨c, by have := closeBracketFrom_ge hcl; omega⟩
      | none => ⟨raws.size, hjlt⟩
    let note ← el (raws.extract (j + 1) c)
      (Nat.lt_of_lt_of_le (extract_lt_slice c hjlt (Nat.lt_succ_self j)) hw)
    have hk := skipSpaces_ge raws (c + 1)
    return (some (Ir.plainText note), ⟨skipSpaces raws (c + 1), by omega⟩)
  | _ => return (none, ⟨j, Nat.le_refl j⟩)

/-- natbib's citation family (`Ir.natbibCites`), read at `i` with the
knot's inline elaborator `el`: one node per citation group, keys as written
and the form beside them — the brackets, separators and names are the
bibliography's to draw, so elaboration keeps the group whole and
resolution renders it. A star asks for the full author list; one `[...]`
note is the note after the citation, two are the notes before and after
(natbib.sty `\NAT@@citetp`), and a noted `\cite` is the parenthetical form
in either mode (natbib.sty `\NAT@cites`). The keys are read raw — a key is
a name, not text; `\nocite`'s keys only enter the list. `\citetext` is
natbib's `\NAT@open#1\NAT@close` (natbib.sty:739): its body is body text
between two bracket marks, so a citation inside it is one like any other.
Returns the nodes — none when the group is missing, named E0304 — and the
index past what was read. Outside the knot, which stands at its heartbeat
budget: the arm there only dispatches. -/
private def citeArm (ctx : Ctx) (raws : Array Raw) (i : Nat) (name : String)
    (base : Ir.CiteForm) (pos : Pos)
    (el : (sub : Array Raw) → rawWeightList sub.toList < sliceWeight raws i → EM (Array Inline)) :
    EM (Array Inline × { j : Nat // i < j }) := do
  let j0 := skipSpaces raws (i + 1)
  have hj0 := skipSpaces_ge raws (i + 1)
  let j1 := skipStar raws j0
  have hj1 := skipStar_ge raws j0
  let (n1, ⟨j2, hj2⟩) ← citeNote raws j1 (sliceWeight raws i) (sliceWeight_le raws (by omega)) el
  let (n2, ⟨j3, hj3⟩) ← citeNote raws j2 (sliceWeight raws i) (sliceWeight_le raws (by omega)) el
  let (pre, post) := match n1, n2 with
    | some a, some b => (a, b)
    | some a, none => ("", a)
    | none, _ => ("", "")
  let form := { base with
    cmd := if base.cmd == .auto && n1.isSome then .paren else base.cmd
    full := base.full || j1 != j0, pre, post }
  match hk : raws[j3]? with
  | some (.group body _) =>
    have hklt := getElem?_lt hk
    if base.cmd == .text then
      let text ← el body (body_lt_slice hk (by simp only [rawWeight]; omega) (by omega))
      let mark (o : Bool) : Inline := .cite { cmd := .bracket o } #[]
      return (#[mark true] ++ text ++ #[mark false], ⟨j3 + 1, by omega⟩)
    else
      let keys := (((argText ctx body).splitOn ",").map (·.trimAscii.toString)).filter
        (!·.isEmpty)
      if base.cmd == .nocite then
        -- No ink, so nothing for the no-bibliography judge; a space before it
        -- swallows the spaces after it (latex.ltx `\@bsphack`/`\@esphack`).
        let j4 := skipSpaces raws (j3 + 1)
        have hj4 := skipSpaces_ge raws (j3 + 1)
        return (#[.cite form keys.toArray],
          if raws[i - 1]? matches some .space then ⟨j4, by omega⟩ else ⟨j3 + 1, by omega⟩)
      -- Recorded for the no-bibliography judge (elabDoc): a citation cannot
      -- be judged where it stands, because its `\bibliography` may follow it.
      recordCiteSites ctx keys pos
      return (#[.cite form keys.toArray], ⟨j3 + 1, by omega⟩)
  | _ =>
    diag ctx .E0304 s!"'\\{name}' needs a \{keys} group" pos
    return (#[], ⟨j3, by omega⟩)

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

/-- A raw TeX length with macro arguments and kernel unit controls
substituted before the shared string parser reads it. -/
private def inlineLengthSrc (ctx : Ctx) (body : Array Raw) : String :=
  (Compat.lengthSrcBy (fun n _ => match ctx.args.find? (·.1 == n) with
    | some (_, some inlines) => some (Ir.plainText inlines)
    | some (_, none) => some ""
    | none => some n) body).getD ""

/-- A register operation the affine grammar deliberately does not model.
These controls need mutable TeX register state rather than a local geometric
value, so each consumer names the boundary instead of treating the register
name as a token or as zero. -/
private def unsupportedLengthControl (body : Array Raw) : Option String :=
  body.findSome? fun r => match r with
    | .ctrl n _ =>
      if ["wd", "ht", "dp", "advance", "multiply", "divide", "glueexpr",
          "numexpr", "muexpr", "skip", "dimen", "count"].contains n then some n
      else none
    | _ => none

private def lengthFormError (body : Array Raw) (why : String) : String :=
  match unsupportedLengthControl body with
  | some n => s!"register arithmetic '\\{n}' is not supported by affine lengths"
  | none => why

private def lengthStringError (src why : String) : String :=
  match ["wd", "ht", "dp", "advance", "multiply", "divide", "glueexpr",
      "numexpr", "muexpr", "skip", "dimen", "count"].find?
      (fun n => (src.splitOn ("\\" ++ n)).length > 1) with
  | some n => s!"register arithmetic '\\{n}' is not supported by affine lengths"
  | none => why

/-- One `\fontsize` argument through the affine dimension grammar. NFSS
supplies `pt` when the argument is a bare decimal; every other spelling is
the shared parser's unchanged. -/
private def fontDim (ctx : Ctx) (src : String) : Except String (Affine Measure) := do
  let trimmed := src.trimAscii.toString
  let src := if (Decl.parseDecimal trimmed).isSome then trimmed ++ "pt" else trimmed
  let e ← Decl.parseAffineLengthExpr (ctx.tokens.entries ++ ctx.engineTokens) src
  if e.rigid then return e
  throw "rubber is not a font dimension"

/-- Decode the compatibility marker into one typed size declaration. -/
private def readFontSizeStyle (ctx : Ctx) (name : String) (pos : Pos) :
    EM (Option Style) := do
  let payload := (name.drop Compat.fontSizeMark.length).toString
  match payload.splitOn Compat.fontSizeSep with
  | [sizeSrc, leadingSrc] =>
    match fontDim ctx sizeSrc with
    | .error why =>
      diag ctx .E0331
        s!"cannot read font size in '\\fontsize' from '{sizeSrc}': {lengthStringError sizeSrc why}" pos
      return none
    | .ok size =>
      match fontDim ctx leadingSrc with
      | .error why =>
        diag ctx .E0331
          s!"cannot read leading in '\\fontsize' from '{leadingSrc}': {lengthStringError leadingSrc why}" pos
        return none
      | .ok leading => return some (.fontSize size leading)
  | _ =>
    diag ctx .E0331 "cannot read the affine dimensions in '\\fontsize'" pos
    return none

/-- `\hspace` glue through the affine parser; finite TeX glue and infinite
fill keep their existing semantics. -/
private def readHskip (ctx : Ctx) (body : Array Raw) (pos : Pos) :
    EM (Affine Measure) := do
  let parts := body.filter fun r => !(r matches .space)
  let src := match parts.toList with
    | [.ctrl "stretch" _, .group n _] => s!"0pt plus {argText ctx n}fill"
    | _ => inlineLengthSrc ctx body
  let words := (src.splitOn " ").filter (!·.isEmpty)
  let (fil, rest) := match words.span (· != "plus") with
    | (pre, "plus" :: v :: post) =>
      match Decl.filFactor? v with
      | some f => (some f, String.intercalate " " (pre ++ post))
      | none => (none, src)
    | _ => (none, src)
  let parsed : Except String (Affine Measure) :=
    if rest.trimAscii.toString == "fill" then .ok (.lit { fil := true })
    else
      match Decl.parseAffineLengthExpr
          (ctx.tokens.entries ++ ctx.engineTokens) rest with
      | .ok e => .ok e
      | .error why =>
        match Decl.parseGlue rest with
        | some g => .ok (.lit g)
        | none => .error (lengthFormError body why)
  match parsed, fil with
  | .ok e, none => return e
  | .ok e, some ((m, sc), order) =>
    unless m == (sc : Int) && order == 2 do
      warnOnce ctx "ctrl:hspace:fil" .W0104
        s!"'\\hspace\{{src}}' stretches as one fill: fills here have one order" pos
        (help := "write \\hfill when equal sharing is intended")
    return .add e (.lit { fil := true })
  | .error why, _ =>
    diag ctx .E0331 s!"cannot read a length from '{src}': {why}" pos
      (help := "write a length such as 10pt, 1em plus 2pt, or 0.5\\linewidth")
    return .lit {}

/-- `\hspace{g}` and its starred, non-discardable form. -/
private def hspaceArm (ctx : Ctx) (raws : Array Raw) (i : Nat) (pos : Pos) :
    EM (Option Inline × { j : Nat // i < j }) := do
  let j0 := skipSpaces raws (i + 1)
  have hj0 := skipSpaces_ge raws (i + 1)
  let keep := raws[j0]? matches some (.word "*" _)
  let j1 := skipStar raws j0
  have hj1 := skipStar_ge raws j0
  match raws[j1]? with
  | some (.group body _) =>
    let g ← readHskip ctx body pos
    let zero := MeasureValues.horizontal 0 0
    let finite := g.withoutFil
    let isFill := g.hasFil && !finite.anyRef (fun _ => true) && finite.eval zero.find == {}
    return (some (if !keep && isFill then .fill else .hspace g keep),
      ⟨j1 + 1, by omega⟩)
  | _ =>
    diag ctx .E0304 "missing argument 'length' for '\\hspace'" pos
    return (none, ⟨i + 1, by omega⟩)

/-- One rigid dimension through the shared affine parser. -/
private def readInlineDim (ctx : Ctx) (command role : String)
    (body : Array Raw) (pos : Pos) : EM (Affine Measure) := do
  let src := inlineLengthSrc ctx body
  let parsed := Decl.parseAffineLengthExpr (ctx.tokens.entries ++ ctx.engineTokens) src
  match parsed with
  | .ok e =>
    if e.rigid then return e
    diag ctx .E0331 s!"cannot read {role} in '\\{command}' from '{src}': rubber is not a dimension" pos
      (help := "write an affine dimension over local measures, points, em, or ex")
  | .error why =>
    diag ctx .E0331 s!"cannot read {role} in '\\{command}' from '{src}': {lengthFormError body why}" pos
      (help := "write an affine dimension over local measures, points, em, or ex")
  return .lit {}

/-- `\rule[raise]{width}{height}` as one typed rectangle. -/
private def ruleArm (ctx : Ctx) (raws : Array Raw) (i : Nat) (pos : Pos) :
    EM (Option Inline × { j : Nat // i < j }) := do
  let j0 := skipSpaces raws (i + 1)
  have hj0 := skipSpaces_ge raws (i + 1)
  let raiseSrc := bracketRunSrc raws j0
  let j1 := skipBracketRun raws j0
  have hj1 := skipBracketRun_ge raws j0
  let j2 := skipSpaces raws (j1 + 1)
  have hj2 := skipSpaces_ge raws (j1 + 1)
  match raws[j1]?, raws[j2]? with
  | some (.group width _), some (.group height _) =>
    let width ← readInlineDim ctx "rule" "width" width pos
    let height ← readInlineDim ctx "rule" "height" height pos
    let raise ← match raiseSrc with
      | some src => readInlineDim ctx "rule" "raise" src pos
      | none => pure (.lit {})
    return (some (.rule width height raise), ⟨j2 + 1, by omega⟩)
  | _, _ =>
    diag ctx .E0304 "'\\rule' needs {width} and {height} groups" pos
    return (none, ⟨i + 1, by omega⟩)

/-- An image dimension through the shared affine parser. All local
measures are carried to layout; literals stay rigid and absolute. -/
private def imageLenOf (ctx : Ctx) (v : String) : Except String Image.Len := do
  let e ← affineLength ctx (fun _ => true) v
  return ⟨e⟩

/-- The text of an `alt={...}` value: braced or quoted spellings both read
as text — the one reading `\includegraphics` and `tikzpicture` share. -/
private def altValueText (v : String) : String :=
  if v.startsWith "{" && v.endsWith "}" && v.length ≥ 2 then
    String.ofList (v.toList.drop 1).dropLast
  else if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then
    String.ofList (v.toList.drop 1).dropLast
  else v

/-- `\\includegraphics`' option run: the modelled keys — width, height,
scale, keepaspectratio, alt, artifact — and a name for everything else. -/
private def readImageOpts (ctx : Ctx) (optSrc : Option (Array Raw))
    (pos : Pos) : EM (Image.SizeSpec × Ir.Alt) := do
  let mut spec : Image.SizeSpec := {}
  let mut alt : Ir.Alt := .undeclared
  if let some src := optSrc then
    for e in Decl.splitEntries (rawSrc src) do
      match Decl.splitEntry e with
      | some ("width", v) =>
        match imageLenOf ctx v with
        | .ok l => spec := { spec with width := some l }
        | .error _ =>
          diag ctx .E0331 s!"cannot read a length from '{v}'" pos
            (help := "image sizes look like 3cm or 0.8\\textwidth")
      | some ("height", v) | some ("totalheight", v) =>
        -- totalheight is height plus depth, and an image has no
        -- depth, so the two keys coincide here.
        match imageLenOf ctx v with
        | .ok l => spec := { spec with height := some l }
        | .error _ =>
          diag ctx .E0331 s!"cannot read a length from '{v}'" pos
            (help := "image sizes look like 3cm or 0.3\\textheight")
      | some ("scale", v) =>
        match Decl.parseDecimal v with
        | some (m, sc) => spec := { spec with scaleNum := m, scaleDen := sc }
        | none => diag ctx .E0321 s!"'scale' needs a number, got {v.quote}" pos
      | some ("alt", v) =>
        -- graphicx's own alt key (LaTeX News 37, 2023): the text
        -- alternative WCAG 2.2 SC 1.1.1 requires, declared where the
        -- image is.
        alt := Ir.Alt.declare (altValueText v)
      | _ =>
        if e.trimAscii.toString == "keepaspectratio" then
          spec := { spec with keepAspect := true }
        else if e.trimAscii.toString == "artifact" ||
            (Decl.splitEntry e).any (·.1 == "artifact") then
          -- latex-lab-graphic's key for decoration (its value is ignored):
          -- no Figure in the PDF, its ink an artifact.
          alt := .decorative
        else
          warnOnce ctx ("imgopt:" ++ e) .W0110
            s!"'\\includegraphics' option '{e}' is not modelled; ignored" pos
            (help := "modelled keys: width, height, scale, keepaspectratio, alt, artifact")
  return (spec, alt)

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
standing beside each recursive call. The goals arrive already cleaned by
the elaborator's own termination-goal cleanup, so no second simp pass runs
first: that pass over every goal cost the knot more than 10,000 of its
200,000 heartbeats (judged by deletion and rebuild). -/
macro "knot_dec" : tactic =>
  `(tactic| (
    first
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

/-- Appendix numbering is exactly the letter of the section counter:
appendix.sty (v1.2c) `\@resets@pp` makes `\thesection` `\Alph{section}`,
replacing the arabic form classes.dtx §Sectioning defines, and the deeper
levels keep prefixing it — the class numbering contract continues under
`\appendix` with the letter base, gapless because the counter stepping is
untouched by the mark. -/
theorem defaultSecNum_appendix_exact (n1 n2 n3 : Nat) :
    defaultSecNum (n1, n2, n3) true 1 = ListMark.AlphN n1 := rfl

/-- Distinct appendix sections render distinct letters: the letter
assignment is injective on the counter, so the gapless counter is gapless
in its rendered form too. -/
theorem defaultSecNum_appendix_inj (m n : Nat × Nat × Nat)
    (h : defaultSecNum m true 1 = defaultSecNum n true 1) : m.1 = n.1 :=
  match m, n with
  | (_, _, _), (_, _, _) => ListMark.letterN_inj (.inr rfl) h

mutual
/-- Render one level's heading number: the declared format when one
stands (`Counters.secFmts`, last declaration wins), the class default
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
    { st with ctr := { st.ctr with
        secFmts := (st.ctr.secFmts.filter (·.1 != lvl)).push (lvl, parts) } }

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
  let (s1, s2, s3) := st.ctr.secNums
  let cur : Int := Int.ofNat (counterAt st.ctr.secNums lvl)
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
  modify fun st => { st with ctr := { st.ctr with secNums := nums,
                                                  runNums := if step then (0, 0) else st.ctr.runNums } }
  if name == "refstepcounter" then
    let num := renderSecLevel st.ctr.secFmts nums st.ctr.inAppendix secFmtFuel lvl
    -- A bare counter step numbers no node: what a label here names has no
    -- kind, so the binding is kindless — a `\cref` to it is W0380.
    modify fun st => { st with refTarget := some { kind := none, num := num } }

/-- The counters besides the sections that the flow keeps (ltcounts.dtx):
`secnumdepth`, how deep headings number; `footnote` and `equation`, the
last number each gave. Each is its reader and its writer over the state. -/
private def flowCounter? (ctr : String) :
    Option ((Counters → Int) × (Counters → Int → Counters)) :=
  match ctr with
  | "secnumdepth" => some (fun c => c.secDepth, fun c v => { c with secDepth := v })
  | "footnote" => some (fun c => c.fnNum, fun c v => { c with fnNum := v.toNat })
  | "equation" => some (fun c => c.eqNum, fun c v => { c with eqNum := v.toNat })
  | _ => none

/-- Set, add to or step a flow counter, as `applyCounter` does a section's:
a count below zero clamps to zero, and the depth may go negative, as
LaTeX's `-1` turns every heading's number off. -/
private def applyFlowCounter (name : String)
    (rw : (Counters → Int) × (Counters → Int → Counters)) (n : Int) : EM Unit :=
  modify fun st => { st with
    ctr := rw.2 st.ctr (match name with
      | "setcounter" => n
      | "addtocounter" => rw.1 st.ctr + n
      | _ => rw.1 st.ctr + 1) }

/-- A counter command's integer argument, as read where it stands: a
literal, `\value{c}` — the counter's register (ltcounts.dtx) — or one of the
kernel's integer constants (`kernelInt`); the value of a counter `c` the
flow does not keep; or a value no reading here reaches, as written. -/
private inductive CounterArg where
  | int (v : Int)
  | unkept (c : String)
  | unread (shown : String)

/-- The kernel's integer constants a counter value names (plain.tex: `\z@`
is a dimen register at 0pt, read as TeX coerces one to a number; the rest
are `\chardef`, `\mathchardef` and `\countdef` constants). -/
private def kernelInt : String → Option Int
  | "z@" => some 0
  | "m@ne" => some (-1)
  | "@ne" => some 1
  | "tw@" => some 2
  | "thr@@" => some 3
  | "sixt@@n" => some 16
  | "@cclv" => some 255
  | "@cclvi" => some 256
  | "@m" => some 1000
  | "@M" => some 10000
  | "@MM" => some 20000
  | _ => none

/-- Read a counter command's value group (`CounterArg`). -/
private def counterValue (st : ESt) (nRaw : Array Raw) : CounterArg :=
  let shown := (rawSrc nRaw).trimAscii.toString
  let named (r : String) (sign : Int) : CounterArg :=
    ((kernelInt r).map fun v => .int (sign * v)).getD (.unread shown)
  match nRaw.toList.filter (!· matches .space) with
  | [.ctrl "value" _, .group c _] =>
    let c := (rawSrc c).trimAscii.toString
    match sectionLevel c with
      | some lvl => .int (Int.ofNat (counterAt st.ctr.secNums lvl))
      | none => match flowCounter? c with
        | some rw => .int (rw.1 st.ctr)
        | none => .unkept c
  | [.ctrl r _] => named r 1
  | [.sym '-' _, .ctrl r _] => named r (-1)
  | [.word "-" _, .ctrl r _] => named r (-1)
  | _ => (shown.toInt?.map .int).getD (.unread shown)

/-- One counter command with its arguments starting at `i` (just past
the control word): scan, apply over the section counters, name any
other counter (W0104) with its arguments consumed — configuration,
never content — and a value it cannot read (W0104, keyed on the
counter's value), the counter keeping what it held. A missing group is
the one error. Out of the block knot so the fixpoint never unfolds
it; the returned index carries the progress fact the knot's measure
reads. -/
private def counterArm (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (n : String) (pos : Pos) : EM { j : Nat // i ≤ j } := do
  let j := skipSpaces raws i
  have hjge : i ≤ j := skipSpaces_ge raws i
  match raws[j]? with
  | some (.group ctrRaw _) =>
    let ctr := (rawSrc ctrRaw).trimAscii.toString
    let st ← get
    let ⟨(amt, j2), hj2⟩ : { t : Option CounterArg × Nat // j + 1 ≤ t.2 } ←
      if n == "addtocounter" || n == "setcounter" then
        let ja := skipSpaces raws (j + 1)
        have hja : j + 1 ≤ ja := skipSpaces_ge raws (j + 1)
        match raws[ja]? with
        | some (.group nRaw _) =>
          pure ⟨(some (counterValue st nRaw), ja + 1), by omega⟩
        | _ => pure ⟨(none, j + 1), Nat.le_refl _⟩
      else
        pure ⟨(some (.int 1), j + 1), Nat.le_refl _⟩
    let unmodelled (c : String) : EM Unit :=
      warnOnce ctx ("ctrl:" ++ n ++ ":" ++ c) .W0104
        s!"counter '{c}' is not modelled; '\\{n}' changes nothing" pos
    let unread (shown : String) : EM Unit :=
      warnOnce ctx ("ctrl:" ++ n ++ ":" ++ ctr ++ ":value") .W0104
        s!"'\\{n}\{{ctr}}' names '{shown}', a value this engine cannot read: skipped, and \
the counter keeps its value" pos
    match sectionLevel ctr, amt with
    | some lvl, some (.int v) => applyCounter n lvl v
    | some _, some (.unkept c) => unmodelled c
    | some _, some (.unread s) => unread s
    | some _, none =>
      diag ctx .E0304 s!"'\\{n}' needs an integer \{value} group" pos
    | none, _ =>
      match flowCounter? ctr, amt with
      | some rw, some (.int v) => applyFlowCounter n rw v
      | some _, some (.unkept c) => unmodelled c
      | some _, some (.unread s) => unread s
      | some _, none => diag ctx .E0304 s!"'\\{n}' needs an integer \{value} group" pos
      | none, _ => unmodelled ctr
    return ⟨j2, by omega⟩
  | _ =>
    diag ctx .E0304 s!"'\\{n}' needs a \{counter} group" pos
    return ⟨i, Nat.le_refl _⟩

/-- A run-in heading's title as it sets: bold, after its number where
`secnumdepth` reaches its level (classes.dtx: `\paragraph` is level four,
`\subparagraph` five; `\@startsection` steps and numbers only there). The
number is its parent's and its own (`\theparagraph` is
`\thesubsubsection.\arabic{paragraph}`), followed by `\@seccntformat`'s
`\quad`, and it is the `\ref` target from here on. Out of the inline knot. -/
private def runInHead (ctx : Ctx) (name : String) (starred : Bool) (title : Array Inline) :
    EM Inline := do
  let st ← get
  let level : Int := if name == "paragraph" then 4 else 5
  -- premise: counterChecks — a run-in level past secnumdepth ships no
  -- number, and one it reaches ships its parent's and its own
  if starred || !ctx.numberHeadings || level > st.ctr.secDepth then
    return .styled .bold title
  let (n4, n5) := st.ctr.runNums
  let runs := if level == 4 then (n4 + 1, 0) else (n4, n5 + 1)
  let parent := renderSecLevel st.ctr.secFmts st.ctr.secNums st.ctr.inAppendix secFmtFuel 3
  let num := if level == 4 then s!"{parent}.{runs.1}" else s!"{parent}.{runs.1}.{runs.2}"
  modify fun st => { st with ctr := { st.ctr with runNums := runs }
                             refTarget := some { kind := some .heading, num := num } }
  return .styled .bold (#[.text (num ++ "\u2003")] ++ title)

-- The well-founded translation whnf-reduces through the knot's body when it
-- assembles the fixpoint and its equations; the string machinery in the
-- arms is data to that process, never proof material, and unfolding it is
-- what blew the elaboration budget (measured: String.Slice.skipPrefixWhile
-- alone at 184k reductions). Sealed for the knot, unsealed right after.
seal String.trimAscii Parse.rawSrc Parse.rawSrcOne Decl.splitEntries
seal Decl.splitEntry Decl.parseValue Decl.parseDecimal smartPunct
seal String.Slice.trimAscii String.Slice.trimAsciiStart String.Slice.trimAsciiEnd
seal String.Slice.dropWhile String.Slice.dropEndWhile String.Slice.skipPrefixWhile

/-- The bracketed number of `\footnote[num]{...}`: the raws between the
brackets as text, read as a number. `none` when no bracket argument stands
there or its text is not a number. Outside the knot (and sealed for it):
its string machinery is data, never proof material. -/
private def footnoteOverride (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (pos : Pos) : Option Nat :=
  match scanBracketArg raws i pos with
  | .took k =>
    (argText ctx (raws.extract (skipSpaces raws i + 1) (k - 1)))
      |>.trimAscii.toString.toNat?
  | _ => none

/-- Does a group's body carry a paragraph break at its top level? The
W0371 test, outside the knot. -/
private def hasParRaw (body : Array Raw) : Bool :=
  body.any (fun r => r matches .par _)

/-- W0371, outside the knot: the arm calls one sealed action. -/
private def footnoteWarnPar (ctx : Ctx) (pos : Pos) : EM Unit :=
  warnOnce ctx "footnote:par" .W0371
    "a paragraph break inside '\\footnote' is set as a space" pos
    (help := "a footnote is one paragraph; split a long note into \
two \\footnote calls")

/-- W0374, outside the knot: one face of display text has no note
apparatus, so the text stays inline where it stands, named. -/
private def footnoteWarnFace (ctx : Ctx) (pos : Pos) : EM Unit :=
  warnOnce ctx "footnote:face" .W0374
    "a footnote on this card is kept inline; a card face has no \
note apparatus" pos
    (help := "write the aside in the running text, or declare \
\\documentclass{article} to give notes a page foot")

/-- W0373, outside the knot: fnsymbol marks and the title-foot placement
are owed, so the content stays inline in the title block, named. -/
private def thanksWarn (ctx : Ctx) (pos : Pos) : EM Unit :=
  warnOnce ctx "ctrl:thanks" .W0373
    "'\\thanks' content is kept inline in the title block" pos
    (help := "a plain \\footnote in the body text renders as a page footnote")

/-- Step the footnote counter through `Ir.footnoteMark` and return the
mark's number: an override is itself and steps nothing. -/
private def footnoteStepNum (override : Option Nat) : EM Nat := do
  let k0 := (← get).ctr.fnNum
  let (num, fn) := Ir.footnoteMark k0 override
  modify fun st => { st with ctr := { st.ctr with fnNum := fn } }
  return num

/-- The missing-group diagnostic the two note arms share, outside the knot. -/
private def noteNeedsGroup (ctx : Ctx) (name : String) (pos : Pos) : EM Unit :=
  diag ctx .E0304 s!"'\\{name}' needs a \{...} group" pos

/-- The clause a dropped option run contributes to the refusing construct's
own message: the run's fate, named once, inside the accounting of the
construct whose argument list it was part of. Written as a wrapper around
the construct's own recovery clause rather than a prefix to it, so one
spelling reads as one sentence at both refusal doors. -/
private def optionRunClause (optionRun : Bool) (kept : String) : String :=
  if optionRun then s!"its [...] options were dropped and {kept}" else kept

/-- The same clause for a *group* of sites rather than one call: the wording
the visible line carries, which must be true of every site the number beside
it counts. A group whose calls all led with a run, or none of which did, is
the single-site wording; a group that met both shapes says so. That line is
the first site's own diagnostic reworded in place (`bumpRunShape`), so the
first site reads the group's rule, not its own event, under `-v` and in
`--porcelain` alike; every later site keeps its own event as a note. -/
private def RunShape.clause (s : RunShape) (kept : String) : String :=
  if !s.withRun then kept
  else if !s.withoutRun then optionRunClause true kept
  else s!"any [...] options were dropped and {kept}"

/-- The advice a dropped option run carries, appended to the refusing
construct's own help rather than delivered by a second code: one spelling,
so the two refusal doors cannot disagree about what a reader should do with
a bracket run they meant as content. -/
private def optionRunAdvice (optionRun : Bool) : String :=
  if optionRun then "; content, not options? start the '[' on the next line" else ""

/-- The help an unknown command's warning points at: the generic
declaration route, except where the engine knows what the construct is
usually for and can name the native key instead — `\AddToHook`'s shipout
hooks are how a LaTeX document draws its own printer's marks, and those
are a declared key here. A leading `[...]` run adds its own advice here,
in the command's own help. -/
private def unknownCmdHelp (name : String) (optionRun : Bool) : String :=
  let route :=
    if name == "AddToHook" || name == "AddToHookNext" then
      "a hook body cannot be interpreted; \\page{ marks = cut } declares \
printer's cut marks, derived from the trim and bleed"
    else "\\define \\name(...) {body} declares it"
  s!"{route}{optionRunAdvice optionRun}"

/-- **A refused command's recovery accounts for all of its arguments.** The
code, message and help a refusal earns, as a value — the pure half of
`warnUnknownCmd`, split out because the invariant is about *which* diagnostic
the construct earns. `unknownCmdDiag_code_exact` is the statement that the
code is fixed by the construct's name alone.

The argument is a `RunShape`, the set of argument shapes the diagnostic
speaks for: one site's own shape at a per-site note, the whole group's at the
line that carries the total. A leading `[...]` run earns no code of its own —
its fate is a clause of *this* message, because the run is part of this
construct's own recovery: those bytes addressed the command, not the
sentence, and kept as text they printed ink nobody wrote. It was a second
code (W0341, retired) naming a fragment of the argument list this message
already covers, and the two doors disagreed about being counted: this one
goes through `warnOnce` with subject `ctrl:<name>`, that one went through the
raw door with none, so `tallySites` put `(2 sites)` on one line while the
other printed at every site.

The one named exception is still the `\footnotemark`/`\footnotetext` pair,
which is pending (W0370, cross-command state — a minipage's notes too) and
never "unknown". The retired code called it an unknown command at its own
span, which was false; with one diagnostic there is nothing left to say it. -/
private def unknownCmdDiag (name : String) (shape : RunShape) :
    DiagCode × String × String :=
  if name == "footnotemark" || name == "footnotetext" then
    let kept := shape.clause "its text is kept in place"
    let route := "\\footnote{...} where the mark should stand sets the note \
at the page foot"
    let advice := optionRunAdvice shape.withRun
    (.W0370, s!"'\\{name}' is not paired with its partner yet; {kept}",
     s!"{route}{advice}")
  else
    let kept := shape.clause "its {...} arguments were kept as text"
    (.W0301, s!"unknown command '\\{name}'; {kept}", unknownCmdHelp name shape.withRun)

/-- One site's own shape. -/
private def RunShape.one (optionRun : Bool) : RunShape := ({} : RunShape).add optionRun

/-- **The line that carries a group's total says what is true of every site
it counts.** Fold this site's shape into the group's, and when that widens
the set — the second shape arriving — reword the line the total is read off
so its clause covers both. The index is the one this emitter recorded, never
a search, so only the diagnostic *this* emitter wrote is ever touched: the
preamble's own refusal shares the key but not the wording, and stays as it
is. -/
private def runShapeReword (name : String) (new : RunShape) (idx : Nat)
    (ds : Array Diag) : Array Diag :=
  let (_, msg, help) := unknownCmdDiag name new
  match ds[idx]? with
  | none => ds
  | some d => ds.setIfInBounds idx
      { d with message := msg, help := d.help.map fun _ => help }

/-- Rewording preserves the count: no site is added or removed by making the
visible line honest. -/
theorem runShapeReword_size_exact (name : String) (new : RunShape) (idx : Nat)
    (ds : Array Diag) : (runShapeReword name new idx ds).size = ds.size := by
  unfold runShapeReword
  dsimp only
  split <;> simp

private def bumpRunShape (name key : String) (optionRun : Bool) (st : ESt) : ESt :=
  match st.runShapes.find? (·.1 == key) with
  | none =>
    { st with runShapes := st.runShapes.push (key, RunShape.one optionRun, st.diags.size) }
  | some (_, old, idx) =>
    let new := old.add optionRun
    { st with
      runShapes := (st.runShapes.filter (·.1 != key)).push (key, new, idx)
      diags := if new == old then st.diags else runShapeReword name new idx st.diags }

theorem bumpRunShape_size_exact (name key : String) (optionRun : Bool) (st : ESt) :
    (bumpRunShape name key optionRun st).diags.size = st.diags.size := by
  unfold bumpRunShape
  split
  · rfl
  · dsimp only
    split <;> simp [runShapeReword_size_exact]

/-- The refusal a command earns, through the counted door. Outside the knot:
the arm calls one sealed action. The demotion is W0301's alone — a spliced
`.sty`'s TeX internals are refused per line and unactionable
(`Compat.styInternal`), while the pending pair is neither. -/
private def warnUnknownCmd (ctx : Ctx) (name : String) (optionRun : Bool)
    (pos : Pos) : EM Unit :=
  let key := "ctrl:" ++ name
  let (code, msg, help) := unknownCmdDiag name (RunShape.one optionRun)
  modify fun st =>
    warnOnceState ctx key code msg pos help
      (code == .W0301 && Compat.styInternal ctx.file name)
      (bumpRunShape name key optionRun st)

/-- The index past an unknown command's `{...}` groups: up to `n` of them,
each after any spaces. Spaces after the last group stay where they stand, as
TeX leaves them after a macro's arguments. -/
def argGroupsEnd (raws : Array Raw) (j : Nat) : Nat → Nat
  | 0 => j
  | n + 1 =>
    let k := skipSpaces raws j
    match raws[k]? with
    | some (.group _ _) => argGroupsEnd raws (k + 1) n
    | _ => j

theorem argGroupsEnd_ge (raws : Array Raw) (j n : Nat) : j ≤ argGroupsEnd raws j n := by
  induction n generalizing j with
  | zero => simp [argGroupsEnd]
  | succ n ih =>
    simp only [argGroupsEnd]
    split
    · have h1 := skipSpaces_ge raws j
      have h2 := ih (skipSpaces raws j + 1)
      omega
    · omega

/-- Is the raw at `m` a `{...}` group? -/
def groupAt (raws : Array Raw) (m : Nat) : Bool :=
  match raws[m]? with
  | some (.group _ _) => true
  | _ => false

/-- Is the raw at `m` a space or a `{...}` group, the two things an argument
list holds between a command and its last group? -/
def spaceOrGroupAt (raws : Array Raw) (m : Nat) : Bool :=
  match raws[m]? with
  | some .space | some (.group _ _) => true
  | _ => false

/-- How many `{...}` groups stand among the `len` raws from `j`. -/
def groupsIn (raws : Array Raw) (j : Nat) : Nat → Nat
  | 0 => 0
  | len + 1 => (if groupAt raws j then 1 else 0) + groupsIn raws (j + 1) len

theorem skipSpaces_spaces (raws : Array Raw) (i : Nat) :
    ∀ m, i ≤ m → m < skipSpaces raws i → raws[m]? = some .space := by
  fun_induction skipSpaces raws i with
  | case1 i h hs ih =>
    intro m h1 h2
    by_cases hm : m = i
    · subst hm
      rw [Array.getElem?_eq_getElem h]
      revert hs
      cases raws[m] <;> simp
    · exact ih m (by omega) h2
  | case2 => intro m h1 h2; omega
  | case3 => intro m h1 h2; omega

theorem groupsIn_add (raws : Array Raw) (j a b : Nat) :
    groupsIn raws j (a + b) = groupsIn raws j a + groupsIn raws (j + a) b := by
  induction a generalizing j with
  | zero => simp [groupsIn]
  | succ a ih =>
    rw [Nat.succ_add, groupsIn, groupsIn, ih (j + 1)]
    have : j + 1 + a = j + (a + 1) := by omega
    rw [this]
    omega

theorem groupsIn_spaces (raws : Array Raw) (j len : Nat)
    (h : ∀ m, j ≤ m → m < j + len → raws[m]? = some .space) : groupsIn raws j len = 0 := by
  induction len generalizing j with
  | zero => rfl
  | succ len ih =>
    have hj : groupAt raws j = false := by
      unfold groupAt
      rw [h j (by omega) (by omega)]
    rw [groupsIn, hj, ih (j + 1) (fun m h1 h2 => h m (by omega) (by omega))]
    rfl

theorem groupsIn_one (raws : Array Raw) (j : Nat) :
    groupsIn raws j 1 = if groupAt raws j then 1 else 0 := rfl

/-- **The index covers the argument list, and only it.** What
`argGroupsEnd` passes over is spaces and `{...}` groups and nothing else, at
most `n` groups; and it stops short of a further group only at the bound —
otherwise the next raw after any spaces is no group. So every group that
could be one of the command's arguments lies behind the index, and nothing
that could not be is consumed. -/
theorem argGroupsEnd_covers (raws : Array Raw) (j n : Nat) :
    (∀ m, j ≤ m → m < argGroupsEnd raws j n → spaceOrGroupAt raws m = true) ∧
      groupsIn raws j (argGroupsEnd raws j n - j) ≤ n ∧
      (groupsIn raws j (argGroupsEnd raws j n - j) = n ∨
        groupAt raws (skipSpaces raws (argGroupsEnd raws j n)) = false) := by
  induction n generalizing j with
  | zero =>
    refine ⟨fun m h1 h2 => ?_, ?_, Or.inl ?_⟩
    · simp only [argGroupsEnd] at h2; omega
    · simp [argGroupsEnd, groupsIn]
    · simp [argGroupsEnd, groupsIn]
  | succ n ih =>
    unfold argGroupsEnd
    dsimp only
    split
    · rename_i _ _ hk
      have hs := skipSpaces_ge raws j
      have hsp := skipSpaces_spaces raws j
      obtain ⟨ih1, ih2, ih3⟩ := ih (skipSpaces raws j + 1)
      have hge := argGroupsEnd_ge raws (skipSpaces raws j + 1) n
      generalize argGroupsEnd raws (skipSpaces raws j + 1) n = k at ih1 ih2 ih3 hge ⊢
      generalize skipSpaces raws j = s at hk hsp ih1 ih2 ih3 hge hs ⊢
      have hgs : groupAt raws s = true := by unfold groupAt; rw [hk]
      have hcount : groupsIn raws j (k - j) = 1 + groupsIn raws (s + 1) (k - (s + 1)) := by
        have e : k - j = (s - j) + (1 + (k - (s + 1))) := by omega
        have e2 : j + (s - j) = s := by omega
        rw [e, groupsIn_add, groupsIn_add raws (j + (s - j)) 1,
          groupsIn_spaces raws j (s - j) (fun m h1 h2 => hsp m h1 (by omega)), e2,
          groupsIn_one, hgs]
        simp
      refine ⟨fun m h1 h2 => ?_, ?_, ?_⟩
      · rcases Nat.lt_trichotomy m s with hm | hm | hm
        · unfold spaceOrGroupAt; rw [hsp m h1 hm]
        · subst hm; unfold spaceOrGroupAt; rw [hk]
        · exact ih1 m (by omega) h2
      · rw [hcount]; omega
      · rw [hcount]
        rcases ih3 with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h
    · rename_i hk
      refine ⟨fun m h1 h2 => absurd h2 (by omega), by simp [groupsIn], Or.inr ?_⟩
      unfold groupAt
      split
      · rename_i body p hg; exact (hk body p hg).elim
      · rfl

/-- The key an unknown LaTeX internal in package code is counted under: its
own, never the document's `ctrl:` one. The two sites have different fates —
a document's arguments stand as text, package code's go — so a shared key
would put one fate's words on the other's line and ride the second as a
note under the first. -/
def pkgCodeKey (name : String) : String := "pkgcode:" ++ name

/-- The words a LaTeX internal in package code is refused in. They name what
went and nothing more: a word run after the command is no `{...}` group and
stays where it stands. -/
private def pkgCodeMsg (name : String) : String :=
  s!"unknown command '\\{name}' in package code; any [...] options and its " ++
    "{...} arguments were dropped, not set as text"

/-- **A LaTeX internal in package code sets none of its arguments.** A
control word with `@` in it is written only where `@` is a letter, a style
or class file being read, and names the kernel's or a package's own code
(`Compat.codeInternal`). The groups after it are that code's operands; set
as text, they printed a style file's own package test on a paper's first
line. The arm skips the command's option runs, and the recovery returns the
index past the `{...}` groups after them, up to TeX's nine: the arm walks on
from there with its text accumulator as it came, so the groups never reach
the walk. The loss is still accounted for, once per site, under the
construct's own key, demoted as a TeX internal is in the preamble
(`Compat.styInternal`). `recoverPackageCmd_accounts` states both halves.
Any other unknown command in package code keeps the document's recovery:
`\fbox` or `\hbox` there sets its group in LaTeX. The rule's one known cost
is an internal that sets an operand, the kernel's `\@firstofone`: its
operand goes too. -/
private def recoverPackageCmd (ctx : Ctx) (name : String) (raws : Array Raw) (j : Nat)
    (pos : Pos) : EM { k : Nat // j ≤ k } := do
  modify (warnOnceState ctx (pkgCodeKey name) .W0391 (pkgCodeMsg name)
    pos (some (unknownCmdHelp name false)) (Compat.styInternal ctx.file name))
  return ⟨argGroupsEnd raws j 9, argGroupsEnd_ge raws j 9⟩

/-- Record what a refusal recovered: the code that named the loss, the
command it stood for, and the source the kept groups carried. Outside the
inline knot for the same reason `warnUnknownCmd` is — the arm calls one
sealed action. Empty salvage records nothing: a refused command with no
group put no ink on the page, and an entry for it would make the census
claim ink that is not there. -/
private def noteSalvage (code : DiagCode) (name text : String) : EM Unit := do
  let t := text.trimAscii.toString
  unless t.isEmpty do
    modify fun st =>
      { st with salvage := st.salvage.push { code := code, command := name, text := t } }

/-- The misplaced-declaration diagnostics (E0347 for running content,
W0346 for configuration), outside the knot: the arm calls one sealed
action, as `warnUnknownCmd` does. -/
private def warnMisplacedDecl (ctx : Ctx) (name : String) (pos : Pos) : EM Unit :=
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

/-- The reserved-control skip warning, outside the knot. -/
private def warnReservedCtrl (ctx : Ctx) (name : String) (code : DiagCode)
    (pos : Pos) : EM Unit :=
  warnOnce ctx ("ctrl:" ++ name) code s!"'\\{name}' is not implemented yet; skipped" pos

/-- The one W0304: a palette name that resolves to nothing keeps its
content uncoloured. Both colour doors — the inline `\textcolor` arm and
the flow block form — speak through here, so the message has one
spelling. Outside the knot. -/
private def warnPaletteMiss (ctx : Ctx) (key : String) (pos : Pos) : EM Unit :=
  warnOnce ctx ("palette:" ++ key) .W0304
    s!"'{key}' is not in the palette; content kept uncoloured" pos
    (help := if ctx.palette.entries.isEmpty then
        "declare colours with \\palette{ name = #RRGGBB }"
      else s!"declared: {String.intercalate ", "
        (ctx.palette.entries.toList.map (·.1))}")

private inductive ColorRead where
  | resolved (color : Color) (token : Option String)
  | missing
  | rejected

/-- Parse and resolve one source colour through `Palette.resolveSource`.
This is the only elaboration door for model syntax; callers differ only in
how an unresolved named expression is reported. -/
private def readColor (ctx : Ctx) (pal : Palette) (model : Option String)
    (src : String) (pos : Pos) : EM ColorRead := do
  let label := match model with
    | some m => s!"{m.trimAscii.toString}({src.trimAscii.toString})"
    | none => src.trimAscii.toString
  match pal.resolveSource model src with
  | .ok (some c) =>
    let token := if model.isNone && (pal.find? label).isSome then some label else none
    return .resolved c token
  | .ok none => return .missing
  | .error (.unsupported m) =>
    diag ctx .W0102
      s!"colour model '{m}' is not supported; use {String.intercalate ", " Decl.colorModelNames}" pos
    return .rejected
  | .error (.malformed m detail) =>
    diag ctx .E0321 s!"cannot read {m} colour {src.trimAscii.toString.quote}: {detail}" pos
      (help := "model values use their documented component count and range")
    return .rejected

/-- The one W0105 for an overlay specification the step model cannot
number, outside the knot: one spelling for its three doors. -/
private def warnOverlaySpec (ctx : Ctx) (w : String) (pos : Pos) : EM Unit :=
  warnOnce ctx "spec:overlay" .W0105
    s!"overlay specification '{w}' does not name a step; its content is \
shown on every step" pos
    (help := "write a numbered spec: <2>, <2->, or <2-3>; incremental \
specs are not modelled")

/-- The one W0105 for `\alt` without a numbered specification, outside
the knot. An alternation inks exactly one alternative per step page, and
an unnumberable spec does not lift that: the step model cannot say which
page the switch happens on, so the honest degradation is the active
alternative on every step — the styled reading for `\alert<spec>{body}`,
as beamer reads an alert-with-spec — never both alternatives at once. -/
private def warnAltSpec (ctx : Ctx) (pos : Pos) : EM Unit :=
  warnOnce ctx "spec:overlay" .W0105
    "'\\alt' without a numbered specification shows its first \
alternative on every step" pos
    (help := "write a numbered spec: <2>, <2->, or <2-3>; incremental \
specs are not modelled")

/-- The reference commands and the form each resolves with: LaTeX's
`\ref`/`\eqref` and cleveref's family (manual v0.21.4 §2) — one key
group each; the `\crefrange` pair arrives desugared to its two halves
(`@crefrange` + `labelcref`, Compat's rewrite). Outside the knot: the
inline dispatch reads one lookup where it read two name tests. -/
private def refCtrlForm? (name : String) : Option Ir.RefForm :=
  [("ref", Ir.RefForm.plain), ("eqref", .paren),
   ("cref", .cref false), ("Cref", .cref true),
   ("labelcref", .labelOnly),
   ("namecref", .name false), ("nameCref", .name true),
   ("@crefrange", .crefRange false), ("@Crefrange", .crefRange true)].lookup name

/-- The forms whose rendering needs the target's kind — a kindless
binding under one of these is W0380's case. -/
def refFormNeedsKind : Ir.RefForm → Bool
  | .cref _ | .crefRange _ | .name _ => true
  | .plain | .paren | .labelOnly => false

seal footnoteOverride hasParRaw footnoteWarnPar footnoteWarnFace
seal thanksWarn footnoteStepNum noteNeedsGroup warnUnknownCmd noteSalvage recoverPackageCmd
seal warnMisplacedDecl warnReservedCtrl optionRunAdvice optionRunClause
seal warnPaletteMiss warnOverlaySpec warnAltSpec
seal argText skipBracketRun bracketRunSrc
seal warnUnclosed warnDroppedArgs
seal refCtrlForm? refFormNeedsKind

/-- The leading `[...]` of a `tikzpicture` body split at its top-level
commas — a `{...}` group is one raw, so a braced value never splits — each
entry with the spaces around it, so the run can be rebuilt as written. A
comma is not special to the lexer, so it rides inside a word: `alt=,` or
`},` split at each one. -/
private def pictureOptEntries (opts : Array Raw) : Array (Array Raw) := Id.run do
  let mut out : Array (Array Raw) := #[]
  let mut cur : Array Raw := #[]
  for r in opts do
    match r with
    | .word s p =>
      let pieces := s.splitOn ","
      for piece in pieces, i in [0:pieces.length] do
        if i > 0 then
          out := out.push cur
          cur := #[]
        if !piece.isEmpty then cur := cur.push (.word piece p)
    | r => cur := cur.push r
  return out.push cur

/-- latex-lab-tikz's per-picture keys, consumed from the leading option run
before the rendered subset or the boundary sees it: `alt={...}` describes
the picture, `artifact` makes it decoration, and an empty `alt=` says
nothing. Every other entry stays as written, and the whitespace a removed
entry opened with passes to the entry that takes its place, so a body
without the keys is returned unchanged and one with them is exactly the
body its author would have written without them — the boundary's
standalone never meets a key plain TikZ does not define, and the
picture's content hash (`Ir.picHash`, the boundary cache's key) is a fact
about its ink, never its words. -/
private def splitPictureAlt (body : Array Raw) (pos0 : Pos) : Ir.Alt × Array Raw := Id.run do
  let j0 := Parse.skipSpaces body 0
  let some opts := bracketRunSrc body j0 | return (.undeclared, body)
  let some c := closeBracketFrom body (j0 + 1) | return (.undeclared, body)
  let mut alt : Ir.Alt := .undeclared
  let mut kept : Array (Array Raw) := #[]
  let mut removed := false
  let mut lead : Option (Array Raw) := none
  let leadOf (e : Array Raw) : Array Raw := (e.toList.takeWhile (· matches .space)).toArray
  let bodyOf (e : Array Raw) : Array Raw := (e.toList.dropWhile (· matches .space)).toArray
  for e in pictureOptEntries opts do
    let text := (rawSrc e).trimAscii.toString
    let key := ((text.splitOn "=").headD "").trimAscii.toString
    if key == "artifact" then
      alt := .decorative
    else if key == "alt" then
      alt := match Decl.splitEntry text with
        | some (_, v) => Ir.Alt.declare (altValueText v)
        | none => .undeclared
    if key == "artifact" || key == "alt" then
      removed := true
      if lead.isNone then lead := some (leadOf e)
    else
      match lead with
      | some l => kept := kept.push (l ++ bodyOf e); lead := none
      | none => kept := kept.push e
  if !removed then return (alt, body)
  let mut rebuilt : Array Raw := body.extract 0 j0
  if kept.any (fun e => !(rawSrc e).isEmpty) then
    rebuilt := rebuilt.push (.sym '[' pos0)
    let mut first := true
    for e in kept do
      if first then first := false
      else rebuilt := rebuilt.push (.sym ',' pos0)
      rebuilt := rebuilt ++ e
    rebuilt := rebuilt.push (.sym ']' pos0)
  return (alt, rebuilt ++ body.extract (c + 1) body.size)

/-- The rendered subset's drawing of one picture body, with what it names:
the one elaboration both the block arm and the in-line arm read, so the
two cannot disagree about what the subset draws. -/
private def subsetPicture (ctx : Ctx) (body : Array Raw) :
    Ir.Pic.Picture × Array Picture.PDiag :=
  let mathOf (d : Bool) (raws : Array Parse.Raw) :
      Ir.Inline × Array Picture.PDiag :=
    let expanded := expandMathList ctx.user ctx.limit #[] raws.toList
    match MathParse.parseMath d expanded with
    | .ok (l, _) => (.formula d (Parse.rawSrc raws) l, #[])
    | .error what => (.math d (Parse.rawSrc raws),
        #[(.W0012, s!"math with {what} is not rendered yet; the \
formula {floorWording (Parse.rawSrc raws)}")])
  Picture.elabPicture ctx.palette body mathOf ctx.pic.sets ctx.pic.metric
    ctx.pic.macros argStyles ctx.page.scale declStyles

/-- One picture sent to the boundary: its request stated once, a picture
the subset draws in part recorded as a fallback the driver may withdraw
(`ReqSpans.fallbacks`), its span, the N0023 note, and the image that stands
where the picture does — named by the words its own labels set
(`Ir.Pic.Picture.said`), as the subset's drawing would have been named. -/
private def routePicture (ctx : Ctx) (body : Array Raw) (pic : Ir.Pic.Picture) (pos : Pos) :
    EM Ir.Inline := do
  let src := Parse.rawSrc body
  let id := Ir.picHash src
  let tool := ctx.pic.tool.getD "lualatex"
  let img := Ir.picSrcPrefix ++ id
  modify fun st =>
    let st := if st.pictures.any (fun p => p.1 == id) then st
      else { st with pictures := st.pictures.push (id, src) }
    if pic.shapes.isEmpty || st.spans.fallbacks.contains id then st
    else { st with spans := { st.spans with fallbacks := st.spans.fallbacks.push id } }
  recordImageSpan ctx img pos
  warnOnce ctx ("picture:boundary:" ++ id) .N0023
    s!"this picture is drawn by {tool} at the boundary; its text is not \
in the document's census" pos
    (help := "the box is measured and placed by the engine; alt={...} or \
artifact on the picture, or a figure caption, names it for assistive technology")
  return .image img {} pic.alternative

/-- **A picture in a line of text stands in its line, drawn by the
boundary.** TeX sets a `tikzpicture` as a box of its line, bottom on the
baseline (pgfmanual §12.2.1), and the boundary's image is exactly such a
box, so a picture met inside inline content — a table cell, a group's text,
a command's argument — is the image the boundary draws for it, wherever the
boundary is open and the request was not withdrawn. The rendered subset
sets a picture only as a block, which a line cannot hold, so where the
boundary is closed (or withdrew the request) the picture is named and not
drawn — never the false "not implemented" of an unknown environment. -/
private def inlinePicture (ctx : Ctx) (body : Array Raw) (pos : Pos) :
    EM (Option Ir.Inline) := do
  let (alt, body) := splitPictureAlt body pos
  let id := Ir.picHash (Parse.rawSrc body)
  -- premise: pictureInlineLineChecks — a picture in a line either ships the
  -- boundary's image there or names that it is not drawn, and a withdrawn
  -- request takes the second door.
  if ctx.pic.tool.isSome && !body.isEmpty && !ctx.pic.withdrawn.contains id then
    let (pic, _) := subsetPicture ctx body
    return some (← routePicture ctx body { pic with alt := alt } pos)
  warnOnce ctx ("picture:inline:" ++ id) .W0334
    "a picture inside a line of text is not drawn: the rendered subset sets a \
picture only as a block" pos
    (help := "a boundary tool (lualatex) draws it in its line; standing in a \
paragraph of its own, the rendered subset draws it")
  return none

seal pictureOptEntries splitPictureAlt subsetPicture routePicture inlinePicture
seal secFmtOfBody applySecFmt applyCounter counterCtrl counterArm runInHead
seal theCounterLevel? sectionLevel String.toInt? String.toNat?

mutual
/-- A pure declaration chain: an inline that is nothing but nested style
wrappers around emptiness — what a 0-ary definition whose body *ends* in
declarations (`\newcommand{\cardlight}{\fontseries{l}\selectfont}`,
`\newcommand{\strong}{\bfseries}`) elaborates to in isolation. Outermost
style first. `none` when any real content is present. -/
-- conserves: none — a census, not a rewrite: it reads a shape and returns
-- the styles it is made of; the tree is reassembled by the caller.
private def declChainOne : Ir.Inline → Option (Array Ir.Style)
  | .styled st inner => (declChainList inner.toList).map (#[st] ++ ·)
  | _ => none

private def declChainList : List Ir.Inline → Option (Array Ir.Style)
  | [] => some #[]
  | [x] => declChainOne x
  -- Two or more elements carry content beside any style wrapper: no chain.
  | _ => none
end

/-- Split a 0-ary expansion into its content and the declaration chain it
ends with, if any. Expansion is token replacement, so a trailing
declaration must style the rest of the *enclosing* group, exactly as the
same declaration written directly would — elaborating the body in
isolation had it styling the empty rest of the body instead, and the
card's `{\cardlight …}` runs rendered in the upright face while an empty
`<strong></strong>` marked where the style went. The chain is outermost
style first. -/
private def splitTrailingDecls (xs : Array Ir.Inline) :
    Array Ir.Inline × Array Ir.Style :=
  match xs.back? with
  | some x =>
    match declChainOne x with
    | some styles => if styles.isEmpty then (xs, #[]) else (xs.pop, styles)
    | none => (xs, #[])
  | none => (xs, #[])

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
      -- A run of blanks was one token at the lexer; a splice that puts two
      -- runs side by side sets one separator, and a paragraph never opens
      -- with one: a leading space glue would indent the line (`spaceSeps`).
      elabInlinesFrom ctx raws (i + 1) acc
        (if spaceSeps sb then sb.push ' ' else sb)
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
        -- no block to hang a number on: it sets unnumbered, named — a
        -- `\tag` as much as a counter's number.
        let (cleaned, keys, _, tag) ← stripMathMeta ctx body
        let mut acc := acc
        for key in keys do
          recordLabel ctx key (← get).refTarget pos
          acc := acc.push (.label key)
        if numbered || tag.isSome then
          warnOnce ctx ("math:eqnum:" ++ name) .W0015
            s!"equation numbers are not rendered here; '\{{name}}' sets unnumbered" pos
            (help := if numbered
              then some s!"'\{{name}}*' spells the unnumbered form, which renders the same"
              else none)
        let x ← elabMathInline ctx true cleaned pos
        elabInlinesFrom ctx raws (i + 1) (acc.push x) ""
      else if let some (kind, numbered) := alignEnvs.lookup name then
        let acc := flushText acc sb
        let (cleaned, keys, _, tag) ← stripMathMeta ctx body
        let mut acc := acc
        for key in keys do
          recordLabel ctx key none pos
          acc := acc.push (.label key)
        let x ← elabMathEnv ctx name kind (numbered || tag.isSome) cleaned pos
        elabInlinesFrom ctx raws (i + 1) (acc.push x) ""
      else if name == "tikzpicture" then
        let acc := flushText acc sb
        let x? ← inlinePicture ctx body pos
        elabInlinesFrom ctx raws (i + 1) (acc ++ x?.toArray) ""
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
          let ⟨inner, hw2⟩ : { a : Array Raw // rawWeightList a.toList < sliceWeight raws i } :=
            ⟨envBody env body j, Nat.lt_of_le_of_lt (envBody_le env body j) hb0⟩
          let ⟨next, hnext⟩ : { n : Nat // i + 1 ≤ n } :=
            if env.ignoresAfterEnd then ⟨skipSpaces raws (i + 1), skipSpaces_ge raws (i + 1)⟩
            else ⟨i + 1, Nat.le_refl _⟩
          have hadvN : sliceWeight raws next < sliceWeight raws i :=
            Nat.lt_of_le_of_lt (sliceWeight_le raws hnext) hadv1
          let a1 ← elabInlines envCtx env.beginBody
          let a2 ← elabInlines ctx inner
          let a3 ← elabInlines envCtx env.endBody
          elabInlinesFrom ctx raws next (acc ++ a1 ++ a2 ++ a3) ""
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
    | .verb env s vpos =>
      -- Verbatim inside inline content: kept as mono text, spaces held as
      -- no-break spaces, lines separated by forced breaks. A listing's
      -- option head is a declaration a paragraph cannot carry — stripped
      -- and named, never set as code text. `\verb`'s one line has no head.
      let acc := flushText acc sb
      if env == "verb" then
        let kept := s.map fun c => if c == ' ' then '\u00a0' else c
        elabInlinesFrom ctx raws (i + 1)
          (if kept.isEmpty then acc else acc.push (.styled .mono #[.text kept])) ""
      else
      let start := listingContentStart env s
      if start > 0 then
        warnOnce ctx ("verb-inline:" ++ env) .W0346
          s!"a '\{{env}}' option head inside inline content is ignored" vpos
      elabInlinesFrom ctx raws (i + 1)
        (acc.push (.styled .mono (Ir.verbatimInlines ((s.drop start).toString)))) ""
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
          if cmd.params.isEmpty then
            -- A spelling is token replacement, so a declaration chain its
            -- body ends with styles the rest of the enclosing group — the
            -- same scope the declaration written directly takes below.
            let (expanded, decls) := splitTrailingDecls expanded
            let acc := acc ++ expanded
            if decls.isEmpty then
              have hadv : sliceWeight raws j < sliceWeight raws i :=
                Nat.lt_of_le_of_lt (sliceWeight_le raws hj) hadv1
              elabInlinesFrom ctx raws j acc ""
            else
              have hw : rawWeightList (raws.extract j raws.size).toList
                  < sliceWeight raws i :=
                extract_lt_slice raws.size h (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hj)
              let rest ← elabInlines ctx (raws.extract j raws.size)
              let acc := acc ++ decls.foldr (fun st inner => #[Ir.Inline.styled st inner]) rest
              have hadv : sliceWeight raws raws.size < sliceWeight raws i :=
                sliceWeight_lt raws h h
              elabInlinesFrom ctx raws raws.size acc ""
          else
            let acc := acc.push (.role cmd.name expanded)
            have hadv : sliceWeight raws j < sliceWeight raws i :=
              Nat.lt_of_le_of_lt (sliceWeight_le raws hj) hadv1
            elabInlinesFrom ctx raws j acc ""
        | none =>
        if name == "hfill" then
          let acc := flushText acc sb
          elabInlinesFrom ctx raws (i + 1) (acc.push .fill) ""
        else if name == "qedhere" then
          -- amsthm's `\qedhere` in text (amsthm.sty:290): its `\qed` where it
          -- stands, the space before taken back; the proof sets the mark
          -- (`thmClose`). Outside a proof amsthm's stack is empty: nothing.
          let acc := if (← get).ctr.thm.proofs == 0 then flushText acc sb
            else unskipText acc sb ++ qedHereRun
          elabInlinesFrom ctx raws (i + 1) acc ""
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
        else if let some composed := raws[i + 1]?.bind (accentCompose name) then
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
            have hwc : rawWeightList (fontCmdContent body).toList < sliceWeight raws i := by
              exact Nat.lt_of_le_of_lt (by
                simpa [fontCmdContent] using
                  rawWeightList_filter_monotone (fun r => !fontCmdNocorr r) body.toList) hw
            let inner ← elabInlines argCtx (fontCmdContent body)
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1)
              (fontCmdPush acc style (fontCmdEdges body.toList raws[j + 1]?) inner) ""
          | some (.word s p) =>
            have hjlt := getElem?_lt hj
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1)
              (fontCmdPush (flushText acc sb) style (fontCmdEdges [.word s p] raws[j + 1]?)
                #[.text s]) ""
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
        else if let some axes := phantomAxes.lookup name then
          -- A phantom sets a box of its argument's size and no ink
          -- (plain.tex ll. 1024-1031): the group is sizing, never content,
          -- so it is consumed unread — no ink, no label, no reference, no
          -- diagnostic from inside it. `sb` is carried through rather than
          -- flushed, so the words on either side stay one run and a
          -- zero-width box costs the line nothing.
          --
          -- One answer per axis the member actually reserves (`phantomAxes`),
          -- and none of them silent by accident. The height and depth are
          -- already in force when the argument borrows the running face
          -- (`phantomBorrows`, the hypothesis `Layout.line_box_glyph_free`
          -- earns): the hand-written alignment fix is then inert rather than
          -- lost, and N0100 says so in the shape every read-and-no-effect
          -- idiom uses. An argument in another face or size is a triple the
          -- line may not carry, so that prop really goes unreserved — named,
          -- never dropped quietly. A width has no carrier at all: W0104, the
          -- code `\makebox`'s declared width already takes.
          let j := skipSpaces raws (i + 1)
          have hjge := skipSpaces_ge raws (i + 1)
          let say (borrows : Bool) : EM Unit := do
            if axes.width then
              warnOnce ctx ("ctrl:" ++ name) .W0104
                s!"'\\{name}' reserves its argument's width; no width is set for it" pos
                (help := "a declared width reads \\hspace{1em}")
            if axes.extent then
              if borrows then
                warnOnce ctx ("ctrl:nothing:" ++ name) .N0100
                  s!"'\\{name}' → nothing: a line's height and depth are its \
fonts' declared metrics, so the prop is already in force" pos
              else
                warnOnce ctx ("ctrl:extent:" ++ name) .W0104
                  s!"'\\{name}' props its argument in another face or size; \
no extent is reserved for it" pos
                  (help := "a declared height reads \\rule{0pt}{1ex}")
          match hj : raws[j]? with
          | some (.group body _) =>
            have hjlt := getElem?_lt hj
            say (phantomBorrows body)
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1) acc sb
          | some (.word s _) =>
            -- TeX takes one token, so a bare word gives its first character
            -- and keeps the rest: `\vphantom value` props a `v` and still
            -- ships "alue". Consuming the whole word would drop content in
            -- silence, which is the one recovery no phantom may choose.
            have hjlt := getElem?_lt hj
            say true
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1) acc (sb ++ (s.drop 1).toString)
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
        else if hform : (refCtrlForm? name).isSome then
          let form := (refCtrlForm? name).get hform
          let j := skipSpaces raws (i + 1)
          have hjge := skipSpaces_ge raws (i + 1)
          match hj : raws[j]? with
          | some (.group keyRaw _) =>
            have hjlt := getElem?_lt hj
            let key := argText ctx keyRaw
            -- Unresolved until the whole document's labels are known:
            -- `resolveRefs` fills the number at the end of elaboration, so
            -- a forward reference costs no second pass over the source.
            let acc := (flushText acc sb).push (.ref key form "??" none)
            modify fun st => { st with refSites := st.refSites.push (key, form, pos) }
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
          -- below article's secnumdepth of 3, so neither numbers unless a
          -- document raises it (`runInHead`).
          let j0 := skipSpaces raws (i + 1)
          have hj0 := skipSpaces_ge raws (i + 1)
          let j1 := skipStar raws j0
          have hj1 := skipStar_ge raws j0
          if scanBracketArg raws j1 pos matches .took _ then
            warnOnce ctx ("section:short:" ++ name) .N0103
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
            let acc := acc.push (← runInHead ctx name (j1 != j0) inner)
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
        else if name == "hyperlink" || name == "hypertarget" then
          -- hyperref.sty defines both as two-group content wrappers: the
          -- first group names a destination, the second is set unchanged.
          let j := skipSpaces raws (i + 1)
          have hjge := skipSpaces_ge raws (i + 1)
          let j2 := skipSpaces raws (j + 1)
          have hj2ge := skipSpaces_ge raws (j + 1)
          match hj : raws[j]?, hj2 : raws[j2]? with
          | some (.group keyRaw _), some (.group body _) =>
            have hj2lt := getElem?_lt hj2
            have hw : rawWeightList body.toList < sliceWeight raws i :=
              body_lt_slice hj2 (by simp only [rawWeight]; omega) (by omega)
            let key := argText ctx keyRaw
            let inner ← elabInlines ctx body
            let acc := flushText acc sb
            let anchor := Ir.labelAnchor key
            let acc := if name == "hyperlink" then
                acc.push (.link ("#".append anchor) inner)
              else
                (acc.push (.label key)) ++ inner
            have hadv : sliceWeight raws (j2 + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j2 + 1) acc ""
          | _, _ =>
            diag ctx .E0304 s!"'\\{name}' needs a \{target}\{content}" pos
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
        else if name == "urlstyle" then
          -- url.sty's face selector for `\url`/`\nolinkurl`: four values,
          -- `tt`/`rm`/`sf` naming a family and `same` the running face.
          -- Flow scope, as `\centering` and `\palette` are: it applies to
          -- the URLs after it, with no brace revert.
          let j := skipSpaces raws (i + 1)
          have hjge := skipSpaces_ge raws (i + 1)
          match hj : raws[j]? with
          | some (.group vRaw _) =>
            have hjlt := getElem?_lt hj
            let v := (Parse.rawSrc vRaw).trimAscii.toString
            match urlStyleFamily? v with
            | some fam => modify fun st => { st with urlFamily := fam }
            | none =>
              warnOnce ctx ("ctrl:urlstyle:" ++ v) .W0104
                s!"'\\urlstyle\{{v}}' names no URL face; skipped" pos
                (help := "url.sty defines tt, rm, sf and same")
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1) acc sb
          | _ =>
            diag ctx .E0304 s!"'\\{name}' needs a \{tt|rm|sf|same} group" pos
            elabInlinesFrom ctx raws (i + 1) acc sb
        else if name == "url" || name == "nolinkurl" then
          -- hyperref/url/xurl's one-argument sibling of `\href`: the URL is
          -- its own text, set in the family `\urlstyle` names — url.sty's
          -- own semantics, whose default is `tt` (mono) and whose `same`
          -- asks for the running face, so no family style at all.
          -- `\nolinkurl` is the same command minus the link (hyperref
          -- manual, "User macros": "\nolinkurl{URL} ... without a link"),
          -- so it resolves HERE, from the same group, the same text and the
          -- same face — one site, one difference. Two sites is how the face
          -- went missing: the URL was set as plain text elsewhere, which is
          -- byte-identical to dropping an unknown command.
          --
          -- The selector is read here rather than refused in the compat
          -- layer because that refusal was false twice over: it told a
          -- reader who asked for the running face that the engine sets URLs
          -- mono, and the slot census then counted the URL as mono the
          -- document had lost.
          let j := skipSpaces raws (i + 1)
          have hjge := skipSpaces_ge raws (i + 1)
          let fam := (← get).urlFamily
          match hj : raws[j]? with
          | some (.group urlRaw _) =>
            have hjlt := getElem?_lt hj
            let url := argText ctx urlRaw
            let set : Ir.Inline := match fam with
              | some s => .styled s #[.text url]
              | none => .text url
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1)
              ((flushText acc sb).push
                (if name == "url" then .link url #[set] else set)) ""
          | _ =>
            diag ctx .E0304 s!"'\\{name}' needs a \{url} group" pos
            elabInlinesFrom ctx raws (i + 1) acc sb
        else if let some base := Ir.natbibCites.lookup name then
          let (nodes, ⟨j, hj⟩) ← citeArm ctx raws i name base pos
            fun sub _hsub => elabInlines ctx sub
          have hadv : sliceWeight raws j < sliceWeight raws i :=
            sliceWeight_lt raws h hj
          elabInlinesFrom ctx raws j (flushText acc sb ++ nodes) ""
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
    (hadv1 : sliceWeight raws (i + 1) < sliceWeight raws i) :
    EM (Array Inline) := do
  if name == "hspace" then
    let (node, ⟨j, hj⟩) ← hspaceArm ctx raws i pos
    let acc := flushText acc sb
    let acc := match node with | some x => acc.push x | none => acc
    have hadv : sliceWeight raws j < sliceWeight raws i := sliceWeight_lt raws h hj
    elabInlinesFrom ctx raws j acc ""
  else if name == "rule" then
    let (node, ⟨j, hj⟩) ← ruleArm ctx raws i pos
    let acc := flushText acc sb
    let acc := match node with | some x => acc.push x | none => acc
    have hadv : sliceWeight raws j < sliceWeight raws i := sliceWeight_lt raws h hj
    elabInlinesFrom ctx raws j acc ""
  else if name == "includegraphics" then
    -- graphicx's command, native. The keys that size figures in real
    -- documents are modelled — width, height, scale, keepaspectratio —
    -- and anything else (rotation included) is named and skipped: a
    -- silently dropped key would misplace the figure without a word.
    let j0 := skipSpaces raws (i + 1)
    have hj0 := skipSpaces_ge raws (i + 1)
    let optSrc := bracketRunSrc raws j0
    let j := skipBracketRun raws j0
    have hjb := skipBracketRun_ge raws j0
    let (spec, alt) ← readImageOpts ctx optSrc pos
    match hj : raws[j]? with
    | some (.group pathRaw _) =>
      have hjlt := getElem?_lt hj
      let src := argText ctx pathRaw
      recordImageSpan ctx src pos
      have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
        sliceWeight_lt raws h (by omega)
      elabInlinesFrom ctx raws (j + 1)
        ((flushText acc sb).push (.image src spec alt)) ""
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
      match FaIcons.byName.get[iconName]? with
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
  else if let some e := FaIcons.byMacro.get[name]? then
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
    let j0 := skipSpaces raws (i + 1)
    have hj0ge := skipSpaces_ge raws (i + 1)
    let model := (bracketRunSrc raws j0).map fun opt =>
      (rawSrc opt).trimAscii.toString
    let j := skipBracketRun raws j0
    have hjge : i + 1 ≤ j := Nat.le_trans hj0ge (skipBracketRun_ge raws j0)
    let j2 := skipSpaces raws (j + 1)
    have hj2ge := skipSpaces_ge raws (j + 1)
    match hj : raws[j]?, hj2 : raws[j2]? with
    | some (.group cname _), some (.group body _) =>
      have hj2lt := getElem?_lt hj2
      have hw : rawWeightList body.toList < sliceWeight raws i :=
        body_lt_slice hj2 (by simp only [rawWeight]; omega) (by omega)
      have hadv : sliceWeight raws (j2 + 1) < sliceWeight raws i :=
        sliceWeight_lt raws h (by omega)
      let source := argText ctx cname
      let label := match model with
        | some m => s!"{m}({source})"
        | none => source
      match ← readColor ctx ctx.palette model source pos with
      | .resolved c cssName =>
        recordColorSpan ctx label c cssName.isSome pos
        let acc := flushText acc sb
        let inner ← elabInlines ctx body
        elabInlinesFrom ctx raws (j2 + 1) (acc.push (.colored c cssName inner)) ""
      | .missing =>
        warnPaletteMiss ctx source pos
        let acc := flushText acc sb
        let inner ← elabInlines ctx body
        elabInlinesFrom ctx raws (j2 + 1) (acc ++ inner) ""
      | .rejected =>
        let acc := flushText acc sb
        let inner ← elabInlines ctx body
        elabInlinesFrom ctx raws (j2 + 1) (acc ++ inner) ""
    | _, _ =>
      diag ctx .E0304 "'\\textcolor' needs {name} and {content}" pos
      elabInlinesFrom ctx raws (i + 1) acc sb
  else
    elabInlinesCtrl2 ctx raws i acc sb name pos h hadv1
termination_by (ctx.envLimit, ctx.limit, sliceWeight raws i, 2)
decreasing_by all_goals knot_dec

/-- The chain's tail: colour declarations, overlays, notes, and the
recovery arms. Same measure, same step shape. -/
def elabInlinesCtrl2 (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (acc : Array Inline) (sb : String) (name : String) (pos : Pos)
    (h : i < raws.size)
    -- Load-bearing despite the underscore (judged by deletion+rebuild):
    -- knot_dec's trailing `assumption` consumes it on the fall-through
    -- edges. The linter cannot see that use, so the name must stay
    -- underscore-prefixed.
    (_hadv1 : sliceWeight raws (i + 1) < sliceWeight raws i) :
    EM (Array Inline) := do
  let inkMarker := name.startsWith "@ink:"
  let source := if inkMarker then (name.drop "@ink:".length).toString else name
  let read ← if inkMarker then
      readColor ctx ctx.palette none source pos
    else
      pure <| match ctx.palette.resolve source with
        | some c => .resolved c (if (ctx.palette.find? source).isSome then some source else none)
        | none => .missing
  if let .resolved c cssName := read then

    -- With a group, that group is the argument: `\primary{Alex}` means
    -- colour Alex, which is what it looks like. Without one it is a
    -- declaration colouring the rest of the group, as `\bfseries` does.
    recordColorSpan ctx source c cssName.isSome pos
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
  else if inkMarker then
    match read with
    | .missing => warnPaletteMiss ctx source pos
    | _ => pure ()
    elabInlinesFrom ctx raws (i + 1) acc sb
  else if name.startsWith Compat.fontSizeMark then
    let style ← readFontSizeStyle ctx name pos
    have hw : rawWeightList (raws.extract (i + 1) raws.size).toList
        < sliceWeight raws i :=
      extract_lt_slice raws.size h (Nat.lt_succ_self i)
    let rest ← elabInlines ctx (raws.extract (i + 1) raws.size)
    let acc := match style with
      | some s => (flushText acc sb).push (.styled s rest)
      | none => flushText acc sb ++ rest
    have hadv : sliceWeight raws raws.size < sliceWeight raws i :=
      sliceWeight_lt raws h h
    elabInlinesFrom ctx raws raws.size acc ""
  else if let some style := declStyleOf source then
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
      match Ir.overlayRange w with
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
        warnOverlaySpec ctx w pos
        have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        elabInlinesFrom ctx raws (j + 1) acc sb
    | none =>
      elabInlinesFrom ctx raws (i + 1) acc sb
  else if name == "alt" then
    -- `\alt<spec>{active}{otherwise}`: one node carrying both alternatives,
    -- because exactly one of them is inked on each step page — the declared
    -- exception to dim-not-hide (`Ir.Inline.alt`). A pair of `step` nodes
    -- cannot say it: the complement of a mid-deck range is two ranges, so
    -- the selection has to see both alternatives at once.
    let j := skipSpaces raws (i + 1)
    have hjge := skipSpaces_ge raws (i + 1)
    match raws[j]?.bind specWord? with
    | some w =>
      let spec := Ir.overlayRange w
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
          -- Page order, not spec order (`Ir.Inline.alt`): step 1 ships the
          -- in-range group only when the range already covers it.
          let onFirst := if Ir.stepPending n last 1 then ib else ia
          let onOther := if Ir.stepPending n last 1 then ia else ib
          elabInlinesFrom ctx raws (j3 + 1) (acc.push (.alt n last onFirst onOther)) ""
        | none =>
          -- One reading, never two: the warning says the step model cannot
          -- number this spec, so the active alternative — the styled one
          -- under `\alert<spec>{body}`, as beamer reads an alert with a
          -- spec — stands on every step, and the other is never inked.
          warnAltSpec ctx pos
          let ia ← elabInlines ctx ga
          elabInlinesFrom ctx raws (j3 + 1) (acc ++ ia) ""
      | _, _ =>
        diag ctx .E0304 "'\\alt' needs <spec>{content}{content}" pos
          (help := "'\\alt<2>{on step 2}{on the others}' takes a spec and TWO \
braced groups: the second is what every other step shows, so give it even \
when it is empty — '{}'")
        elabInlinesFrom ctx raws (i + 1) acc sb
    | none =>
      let j3 := skipSpaces raws (j + 1)
      have hj3ge := skipSpaces_ge raws (j + 1)
      match hj2 : raws[j]?, hj3 : raws[j3]? with
      | some (.group ga _), some (.group _ _) =>
        have hj3lt := getElem?_lt hj3
        have hwa : rawWeightList ga.toList < sliceWeight raws i :=
          body_lt_slice hj2 (by simp only [rawWeight]; omega) (by omega)
        have hadv : sliceWeight raws (j3 + 1) < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        let acc := flushText acc sb
        warnAltSpec ctx pos
        let ia ← elabInlines ctx ga
        elabInlinesFrom ctx raws (j3 + 1) (acc ++ ia) ""
      | _, _ =>
        diag ctx .E0304 "'\\alt' needs <spec>{content}{content}" pos
          (help := "'\\alt<2>{on step 2}{on the others}' takes a spec and TWO \
braced groups: the second is what every other step shows, so give it even \
when it is empty — '{}'")
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
        -- No body: malformed, and said so — a bare `\note` once vanished
        -- with no word at all (the silence-is-fidelity audit).
        noteNeedsGroup ctx "note" pos
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
        noteNeedsGroup ctx "note" pos
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
  else if (Ir.raggedSideOf? name).isSome then
    -- The ragged declarations are block declarations the same way.
    warnOnce ctx ("ctrl:" ++ name) .W0108
      s!"'\\{name}' aligns nothing inside an argument; content keeps its alignment" pos
      (help := s!"move '\\{name}' to the start of the group or environment body")
    elabInlinesFrom ctx raws (i + 1) acc sb
  else if name == "footnote" then
    -- `\footnote[num]{text}`: the mark takes the next counter value, or
    -- the override without stepping (`footnoteStepNum`; the sourcing lives
    -- on `Ir.footnoteMark`, the contract on `Ir.footnote_numbers_gapless`).
    let override : Option Nat := footnoteOverride ctx raws (i + 1) pos
    let (⟨j1, hj1⟩, _, _) ← skipOptArg ctx name raws (i + 1) pos
    let j := skipSpaces raws j1
    have hjge := skipSpaces_ge raws j1
    match hj : raws[j]? with
    | some (.group body _) =>
      have hjlt := getElem?_lt hj
      have hw : rawWeightList body.toList < sliceWeight raws i :=
        body_lt_slice hj (by simp only [rawWeight]; omega) (by omega)
      -- A note is one paragraph by design: a break inside it is a space.
      if hasParRaw body then
        footnoteWarnPar ctx pos
      let acc := flushText acc sb
      let inner ← elabInlines ctx body
      have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
        sliceWeight_lt raws h (by omega)
      if ctx.face then
        footnoteWarnFace ctx pos
        elabInlinesFrom ctx raws (j + 1) (acc ++ inner) ""
      else
        let num ← footnoteStepNum override
        elabInlinesFrom ctx raws (j + 1) (acc.push (.footnote (some num) inner)) ""
    | _ =>
      noteNeedsGroup ctx "footnote" pos
      elabInlinesFrom ctx raws (i + 1) acc sb
  else if name == "thanks" then
    thanksWarn ctx pos
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
      elabInlinesFrom ctx raws (j + 1) (acc ++ inner) ""
    | _ =>
      noteNeedsGroup ctx "thanks" pos
      elabInlinesFrom ctx raws (i + 1) acc sb
  else if let some code := reservedCtrl.lookup name then
    warnReservedCtrl ctx name code pos
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
    -- the key/value rest is configuration (W0346) — `warnMisplacedDecl`.
    warnMisplacedDecl ctx name pos
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
  else if Compat.nativeSetCtrls.contains name ||
      (ctx.pic.tool.isSome && Compat.boundaryCtrls.contains name) then
    -- A tikz-family set line is not unknown wherever it stands. Its group
    -- addresses the picture machinery, never the sentence: kept as text it
    -- printed the definition's own source into the paragraph. The engine
    -- reads `\tikzset` itself now (`Compat.nativeSetCtrls`), so that line
    -- is consumed whichever renderer draws; the rest are the boundary's
    -- while it is open (`Compat.boundaryDecls` collected them — body-level
    -- lines included, `boundaryDecls_covers`), and a declared refusal
    -- (`tool = none`) makes those unknown again, arguments and all. What a
    -- read line left unread is named at the line itself, in `elabDoc`.
    let jr := skipReservedArgs raws (i + 1) pos
    if let some bpos := jr.2 then
      warnUnclosed ctx s!"'\\{name}'" bpos
    have hge : i + 1 ≤ jr.1 := skipReservedArgs_ge raws (i + 1) pos 1
    have hadv : sliceWeight raws jr.1 < sliceWeight raws i :=
      sliceWeight_lt raws h (by omega)
    elabInlinesFrom ctx raws jr.1 acc sb
  else if (unknownCmdDiag name {}).1 == .W0301 && Compat.packageFile ctx.file &&
      Compat.codeInternal name && !ctx.atUse then
    -- premise: packageCodeChecks — a style's spans, and the hooks it
    -- registers, carry the style's own file; that block builds both sides
    -- A LaTeX internal in package code sets no text: its option runs and
    -- `{...}` groups are its code and go with it (`recoverPackageCmd`), and
    -- `acc`/`sb` pass on as they came. Any other unknown command there
    -- takes the document's recovery below. A definition's trial reads as
    -- its use (`atUse`).
    let j0 := skipSpaces raws (i + 1)
    have hj0 := skipSpaces_ge raws (i + 1)
    let j1 := skipStar raws j0
    have hj1 := skipStar_ge raws j0
    let jr := skipOptionRuns raws j1 pos
    have hjr : j1 ≤ jr.1 := skipOptionRuns_ge raws j1 pos
    let ⟨j3, hj3⟩ ← recoverPackageCmd ctx name raws jr.1 pos
    if let some bpos := jr.2 then
      warnUnclosed ctx s!"'\\{name}'" bpos
    have hadv : sliceWeight raws j3 < sliceWeight raws i :=
      sliceWeight_lt raws h (by omega)
    elabInlinesFrom ctx raws j3 acc sb
  else
    -- Best effort: the {...} arguments are content, and content is
    -- never dropped for want of a command. Only the formatting is lost.
    -- (The one named exception, `warnUnknownCmd`: the \footnotemark pair
    -- is pending, W0370, never "unknown".)
    let j0 := skipSpaces raws (i + 1)
    have hj0 := skipSpaces_ge raws (i + 1)
    -- A starred form's `*` belongs to the command, not to the text.
    let j1 := skipStar raws j0
    have hj1 := skipStar_ge raws j0
    -- A leading [...] run is how the author addressed the command,
    -- never their content: kept, it is ink nobody wrote ('[16]'
    -- printed in front of a URL). It goes with the command, and the
    -- command's own diagnostic says so — the run is part of this
    -- construct's recovery, so it is one accounting and not two.
    let jr := skipOptionRuns raws j1 pos
    have hjr : j1 ≤ jr.1 := skipOptionRuns_ge raws j1 pos
    warnUnknownCmd ctx name (jr.1 > j1) pos
    if let some bpos := jr.2 then
      warnUnclosed ctx s!"'\\{name}'" bpos
    let j2 := skipSpaces raws jr.1
    have hj2 := skipSpaces_ge raws jr.1
    have hcall : sliceWeight raws j2 < sliceWeight raws i :=
      sliceWeight_lt raws h (by omega)
    let (acc2, sb2, ⟨j3, hj3⟩, kept, sp) ← elabUnknownArgs ctx raws j2 0 acc sb false
    -- What the floor kept, recorded as salvage: this ink is the engine's
    -- recovery, not the author's prose, and nothing downstream could tell
    -- the two apart from the bytes alone.
    noteSalvage .W0301 name (Parse.rawSrc (raws.extract j2 j3))
    -- The control word swallowed a space after it; give back only one
    -- that was really there — `\x{a} b` keeps its space, `\x{a}.b`
    -- gains no ink the author never wrote.
    let sbF := if kept > 0 && sp && j3 < raws.size then " " else sb2
    have hadv : sliceWeight raws j3 < sliceWeight raws i :=
      sliceWeight_lt raws h (by omega)
    elabInlinesFrom ctx raws j3 acc2 sbF
termination_by (ctx.envLimit, ctx.limit, sliceWeight raws i, 1)
decreasing_by all_goals knot_dec


end

unseal String.trimAscii Parse.rawSrc Parse.rawSrcOne Decl.splitEntries
unseal Decl.splitEntry Decl.parseValue Decl.parseDecimal smartPunct
unseal footnoteOverride hasParRaw footnoteWarnPar footnoteWarnFace
unseal thanksWarn footnoteStepNum noteNeedsGroup warnUnknownCmd noteSalvage recoverPackageCmd
unseal warnMisplacedDecl warnReservedCtrl optionRunAdvice optionRunClause
unseal warnPaletteMiss warnOverlaySpec warnAltSpec
unseal argText skipBracketRun bracketRunSrc
unseal warnUnclosed warnDroppedArgs
unseal refCtrlForm? refFormNeedsKind
unseal secFmtOfBody applySecFmt applyCounter counterCtrl counterArm runInHead
unseal pictureOptEntries splitPictureAlt subsetPicture routePicture inlinePicture
unseal theCounterLevel? sectionLevel String.toInt? String.toNat?
unseal String.Slice.trimAscii String.Slice.trimAsciiStart String.Slice.trimAsciiEnd
unseal String.Slice.dropWhile String.Slice.dropEndWhile String.Slice.skipPrefixWhile

/-- **The code a refusal earns is fixed by the construct's name alone.** A
construct the engine knows and defers is named as pending, everything else as
unknown, and the call's argument shape does not enter: a leading `[...]` run
earns no code of its own. The message and help *do* depend on the shape — the
run's fate is a clause of them — so this states the code and nothing more.
The wording is the golden's to witness
(`tests/golden/diagnostics.txt`), and that the wording on the counted line is
true of every site it counts is `runShape_fold_exact` plus
`optionRunAccountingChecks`' mixed-shape rows in both orders.

The retired W0341 is why the code matters on its own: it named a fragment of
the argument list this diagnostic already covers, at the same span, and for
the pending pair it called a construct the engine knows an unknown command.
With one code at the span there is nothing left to make that claim. -/
theorem unknownCmdDiag_code_exact (name : String) (shape : RunShape) :
    (unknownCmdDiag name shape).1 =
      (if name == "footnotemark" || name == "footnotetext" then .W0370 else .W0301) := by
  unfold unknownCmdDiag
  split <;> rfl

/-- The option run earns no code: the *code* naming a refused command is the
same whatever shapes its sites carried, so the run is accounted for inside
that diagnostic and never beside it. Message and help differ by design —
the run's fate is a clause of them — and this says only that the choice of
code is shape-blind. -/
theorem unknownCmdDiag_shape_id (name : String) (shape : RunShape) :
    (unknownCmdDiag name shape).1 = (unknownCmdDiag name {}).1 := by
  rw [unknownCmdDiag_code_exact, unknownCmdDiag_code_exact]

/-- **One refusal, one diagnostic, with a subject.** The emitter fact the
census needs and the fold cannot state: every call of `warnUnknownCmd` pushes
exactly one diagnostic, carrying the construct's code and the subject
`ctrl:<name>`. Rewriting the group's counted line (`bumpRunShape`) happens in
place and is not a push, which is why this is stated as one more element at
the end rather than as `st.diags.push d`.

This is the hypothesis `Diag.tallySites_exact` carries and could not get:
that theorem — the number on the line is the number of sites of that loss —
assumes `subject.isSome`, so it was *vacuous* on exactly the class that
miscounted. Here it is discharged by construction for every refused command.
`subjectCensusChecks` and `siteAccountingChecks` hold the surface-wide
gates. -/
theorem warnUnknownCmd_push_exact (ctx : Ctx) (name : String) (optionRun : Bool)
    (pos : Pos) (st : ESt) :
    ∃ d, ((warnUnknownCmd ctx name optionRun pos).run st).2.diags.size
          = st.diags.size + 1 ∧
      ((warnUnknownCmd ctx name optionRun pos).run st).2.diags.back? = some d ∧
      d.kind = (unknownCmdDiag name (RunShape.one optionRun)).1 ∧
      d.subject = some ("ctrl:" ++ name) := by
  have hrun : ((warnUnknownCmd ctx name optionRun pos).run st).2 =
      warnOnceState ctx ("ctrl:" ++ name)
        (unknownCmdDiag name (RunShape.one optionRun)).1
        (unknownCmdDiag name (RunShape.one optionRun)).2.1 pos
        (unknownCmdDiag name (RunShape.one optionRun)).2.2
        ((unknownCmdDiag name (RunShape.one optionRun)).1 == .W0301 &&
          Compat.styInternal ctx.file name)
        (bumpRunShape name ("ctrl:" ++ name) optionRun st) := rfl
  refine ⟨warnOnceDiag ctx ("ctrl:" ++ name)
      (unknownCmdDiag name (RunShape.one optionRun)).1
      (unknownCmdDiag name (RunShape.one optionRun)).2.1 pos
      (unknownCmdDiag name (RunShape.one optionRun)).2.2
      ((unknownCmdDiag name (RunShape.one optionRun)).1 == .W0301 &&
        Compat.styInternal ctx.file name)
      (!(bumpRunShape name ("ctrl:" ++ name) optionRun st).warnedUnknown.contains
        ("ctrl:" ++ name)),
    ?_, ?_, warnOnceDiag_kind_exact .., warnOnceDiag_subject_exact ..⟩
  · rw [hrun, warnOnceState_diags_exact]
    simp [bumpRunShape_size_exact]
  · rw [hrun, warnOnceState_diags_exact]
    simp

/-- **Package code sets no text: a LaTeX internal's arguments are consumed,
and its refusal is paid for by exactly one diagnostic.** The empty recovery
`_accounts` names. The index the recovery returns stands past a run of
spaces and `{...}` groups and nothing else — at most nine groups, TeX's
limit, and at the bound or before a raw that is no group — so every group
that could be one of the internal's arguments is behind it
(`argGroupsEnd_covers`), and the arm, which walks on from that index with
its text accumulator as it came, never walks them as text. It records no
salvage, so the census can attribute no ink to it. What it does push is one
diagnostic at the end, W0391, under the construct's own key: the loss named
once per site, as every counted refusal is (`Diag.tallySites_exact` reads
that subject). -/
theorem recoverPackageCmd_accounts (ctx : Ctx) (name : String) (raws : Array Raw)
    (j : Nat) (pos : Pos) (st : ESt) :
    ((recoverPackageCmd ctx name raws j pos).run st).2.salvage = st.salvage ∧
      (∃ d, ((recoverPackageCmd ctx name raws j pos).run st).2.diags = st.diags.push d ∧
        d.kind = .W0391 ∧ d.subject = some (pkgCodeKey name)) ∧
      (∀ m, j ≤ m → m < ((recoverPackageCmd ctx name raws j pos).run st).1.1 →
        spaceOrGroupAt raws m = true) ∧
      groupsIn raws j (((recoverPackageCmd ctx name raws j pos).run st).1.1 - j) ≤ 9 ∧
      (groupsIn raws j (((recoverPackageCmd ctx name raws j pos).run st).1.1 - j) = 9 ∨
        groupAt raws (skipSpaces raws ((recoverPackageCmd ctx name raws j pos).run st).1.1) =
          false) := by
  have hrun : (recoverPackageCmd ctx name raws j pos).run st =
      (⟨argGroupsEnd raws j 9, argGroupsEnd_ge raws j 9⟩,
        warnOnceState ctx (pkgCodeKey name) .W0391 (pkgCodeMsg name) pos
          (some (unknownCmdHelp name false)) (Compat.styInternal ctx.file name) st) := rfl
  rw [hrun]
  obtain ⟨h1, h2, h3⟩ := argGroupsEnd_covers raws j 9
  exact ⟨rfl, ⟨_, warnOnceState_diags_exact .., warnOnceDiag_kind_exact ..,
    warnOnceDiag_subject_exact ..⟩, h1, h2, h3⟩

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
  ["itemize", "enumerate", "center", "flushleft", "flushright", "document", "frame",
   "columns", "tabularx", "figure",
   "figure*", "table", "table*", "quote", "quotation", "verse", "description",
   "thebibliography", "abstract", "titlepage", "ifbackend",
   "nav", "minipage", "block", "alertblock", "exampleblock", "appendices"]

/-- Environment names a document cannot redefine, the environment mirror of
`builtinNames`: everything the engine gives a meaning of its own. -/
def builtinEnvNames : List String :=
  blockEnvs ++ (alignEnvs.map (·.1)) ++ (displayMathEnvs.map (·.1)) ++
  ["verbatim", "tabular", "tabular*", "column", "array",
   "algorithm", "algorithm*", "algorithm2e", "algorithmic"] ++
  reservedEnv

/-- The text-block width the page yields: `width − 2·hmargin`, spelled
once — a page fact has one resolving def. -/
private def _root_.LeanTex.Core.Ir.PageSpec.textWidth (p : PageSpec) : Sp :=
  p.width - 2 * p.hmargin

/-- The text-block height the page yields: `height − 2·vmargin`. -/
private def _root_.LeanTex.Core.Ir.PageSpec.textHeight (p : PageSpec) : Sp :=
  p.height - 2 * p.vmargin

/-- The page the class yields for a declared spec and options: the one
resolving site for class page geometry, read by `engineLengthTokens` and
the `elabDoc` fold alike so the preamble's token environment and the
shipped page cannot drift (`engine_tokens_agree`). A face takes the class
option's US (3.5 × 2 in) or Japanese (91 × 55 mm) card trade size, else
the class record's `trimDefault`, with `safeMargin` on both margins, and
sets display-text policy: no hyphenation, and — below the 40-character
working minimum for justified text (Bringhurst, Elements 2.1.2) — ragged.
A frame fills beamer's stage (`slidesStageOf`) with the slides margins.
Flow reads the `*paper`/`paper=` options against `pageSizes` and
`landscape` swaps the axes — the reading the geometry package documents
for exactly these options (geometry manual §5.2). A document that declared
its own geometry keeps every value it named: a class option is a default,
never a lock. The flow classes' undeclared text block (Bringhurst's 26
picas, `Ir.articleTextBlock`) is deliberately not applied here — it is the
fold's own `!sawPage` step, after the whole preamble has spoken. -/
private def classPageDefaults (record : Ir.ClassRecord) (opts : List String)
    (page : PageSpec) : PageSpec := Id.run do
  let dflt : PageSpec := {}
  let mut page := page
  if record.model == .flow then
    if page.width == dflt.width && page.height == dflt.height then
      let sized := opts.findSome? fun o =>
        let o := if o.startsWith "paper=" then
          (o.drop "paper=".length).toString ++ "paper" else o
        if o.endsWith "paper" then
          pageSizes.lookup ((o.dropEnd "paper".length).toString)
        else none
      if let some (w, h) := sized then
        page := { page with width := w, height := h }
      if opts.contains "landscape" then
        page := { page with width := page.height, height := page.width }
  if record.model == .frame then
    if page.width == dflt.width && page.height == dflt.height then
      let (w, h) := slidesStageOf opts
      page := { page with width := w, height := h }
    if page.hmargin == dflt.hmargin then
      page := { page with hmargin := Ir.slidesHMargin }
    if page.vmargin == dflt.vmargin then
      page := { page with vmargin := Ir.slidesVMargin }
  else if record.model == .face then
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
    if page.justify.isNone then
      page := { page with justify := some false }
  return page

/-- A box's declared width (`{minipage}`, `\parbox`, `{column}`): a fraction
of the enclosing measure in per mille (`0.48\textwidth`, `.5\linewidth`, a
bare factor, or `\textwidth` alone — a factor of one, as TeX reads a
coefficient-less internal dimen), or an absolute length. `none` is
unreadable.

Three spellings name the width indirectly and all three are resolved here,
because a width the reader cannot read is a box that takes the whole
measure. A declared token (`\begin{column}{\colwidth}`, the beamerposter
idiom) resolves to its length. A document command whose body is one width
(`\newcommand{\panelw}{.45\textwidth}`) is expanded once and re-read — one
step, not a fixpoint: a width is a length, and a length that needs two
expansions to become one is a macro program rather than a declaration. -/
private def columnWidth (ctx : Ctx) (src : String) : Option Ir.BoxWidth := Id.run do
  let s := src.trimAscii.toString
  match affineLength ctx (· != .textHeight) s with
  | .ok e => return some (.sized e)
  | .error _ =>
    if s.startsWith "\\" then
      let name := (s.drop 1).toString.trimAscii.toString
      match lookupUser ctx name with
      | some (_, cmd) =>
        if cmd.params.isEmpty then
          let body := (rawSrc cmd.body).trimAscii.toString
          if body != s then
            return (affineLength ctx (· != .textHeight) body).toOption.map .sized
          else return none
        else return none
      | none => return none
    else
      match Decl.parseDecimal s with
      | some (m, sc) =>
        if m ≥ 0 && sc > 0 then
          return some (.sized (Affine.scaleQ m sc (.ref .lineWidth)))
        else return none
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
      || n == "bibliography" || n == "bibliographystyle" || n == "@natbib"
      -- A definition or a counter command makes the body
      -- declaration-shaped: it must expand through the block walk,
      -- where the define door and the counter arm stand.
      || n == "define" || counterCtrl n
      || ["section", "subsection", "subsubsection"].contains n
  | .par _ => true
  | .verb env _ _ => env != "verb"
  | .math display _ _ => display
  | .env n body _ =>
    if (Parse.inputEnvFile? n).isSome then bodyIsBlockList body.toList
    else
      blockEnvs.contains n || isMathEnv n
        || n == "tabular" || n == "tabular*"
        || n == "algorithm" || n == "algorithm*" || n == "algorithm2e"
        || n == "algorithmic"
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

/-- Does a two-group content wrapper carry block-shaped content in its second
argument? Hyperref's `\\hyperlink` and `\\hypertarget` use exactly this
signature; the first group names the destination and the second is content. -/
private def contentWrapperTakesBlocks (raws : Array Raw) (i : Nat) : Bool :=
  let j := skipSpaces raws (i + 1)
  let j2 := skipSpaces raws (j + 1)
  match raws[j]?, raws[j2]? with
  | some (.group _ _), some (.group body _) => bodyIsBlock body
  | _, _ => false

/-- The number an unstarred heading takes, stepped in flow order — or
`none`, which is also the answer for every heading of a class that does
not number. classes.dtx §Sectioning: `\thesection` is `\arabic{section}`
(`\Alph` after `\appendix`), each deeper level prefixes its parent, a
starred form neither numbers nor steps, and neither does a heading deeper
than `secnumdepth` (`Counters.secDepth`: 3, article's, unless the document sets
it), so `\paragraph` and below never number. A document's own
`\renewcommand{\the<counter>}{...}` format (`Counters.secFmts`) renders
instead where one stands. Stepping a level zeroes the deeper
ones, so `2.1` after a fresh `\section` is impossible by construction. -/
private def sectionNumber (ctx : Ctx) (level : Nat) (starred : Bool) :
    EM (Option String) := do
  let st ← get
  if starred || !ctx.numberHeadings || level == 0 || level > 3 ||
      (level : Int) > st.ctr.secDepth then
    return none
  let (s1, s2, s3) := st.ctr.secNums
  let nums := match level with
    | 1 => (s1 + 1, 0, 0)
    | 2 => (s1, s2 + 1, 0)
    | _ => (s1, s2, s3 + 1)
  let num := renderSecLevel st.ctr.secFmts nums st.ctr.inAppendix secFmtFuel level
  -- The heading is the numbered thing in force from here on: a \label in
  -- the flow after it binds to this number, as a heading (`\cref` says
  -- "section").
  modify fun st => { st with ctr := { st.ctr with secNums := nums, runNums := (0, 0) }
                             refTarget := some { kind := some .heading, num := num } }
  return some num

/-- A declaration standing in a group applies to the rest of the group:
`\Huge`, `\bfseries`, `\centering`, a palette name used bare. -/
private def isDeclaration (ctx : Ctx) : Raw → Bool
  | .ctrl n _ =>
    n == "centering" || n.startsWith Compat.fontSizeMark || (Ir.raggedSideOf? n).isSome
      || (declStyles.lookup n).isSome || (ctx.palette.find? n).isSome
  | _ => false

/-- The block reading of a declaration met between blocks — the `isB` row
and its arm's one computation: the `Ir.Decl` the rest of the scope is
elaborated under, when `n` is a style declaration or a bare palette name
and the open paragraph holds nothing but space. Bare: `\accent{word}`
opening a paragraph keeps its argument reading. Mid-paragraph a
declaration keeps the inline reading, as the ink marker does.
`\centering` keeps its block wrapper, the `@lang:` marker its
flow-state arm, and `\ttfamily` its inline arm. -/
private def declBlockOf (ctx : Ctx) (n : String) (raws : Array Raw) (i : Nat)
    (cur : Array Raw) : Option Ir.Decl :=
  -- `\ttfamily` keeps its inline reading: its literal treatment of
  -- punctuation lives on the inline context, not in the flow state.
  if !cur.all isSpaceOrPar || n.startsWith "@lang:" || n == "ttfamily" then none
  else match declStyleOf n with
    | some s => some (.style s)
    | none =>
      (ctx.palette.find? n).bind fun c =>
        match raws[skipSpaces raws (i + 1)]? with
        | some (.group _ _) => none
        | _ => some (.color c (some n))

/-- The `isB` row of the declaration's block reading: one Bool for the
knot, computed outside it. -/
private def isDeclBlock (ctx : Ctx) (n : String) (raws : Array Raw) (i : Nat)
    (cur : Array Raw) : Bool :=
  (cur.all isSpaceOrPar && n.startsWith Compat.fontSizeMark) ||
    (declBlockOf ctx n raws i cur).isSome

/-- Enter the rest of a declaration's scope: the declaration joins the open
ones innermost (unchanged for `\centering` and the ragged pair). Returns
the list to restore on leaving. -/
private def enterBlockDecl (ctx : Ctx) (n : String) (raws : Array Raw) (i : Nat)
    (cur : Array Raw) (pos : Pos) : EM (List Ir.Decl) := do
  let saved := (← get).blockDecls
  if n.startsWith Compat.fontSizeMark then
    if let some style ← readFontSizeStyle ctx n pos then
      modify fun st => { st with blockDecls := saved ++ [.style style] }
  else
    match declBlockOf ctx n raws i cur with
    | some d => modify fun st => { st with blockDecls := saved ++ [d] }
    | none => pure ()
  return saved

/-- Leave the scope: restore what `enterBlockDecl` saved. -/
private def leaveBlockDecl (saved : List Ir.Decl) : EM Unit :=
  modify fun st => { st with blockDecls := saved }

/-- The declaration arm's whole effect but the recursion: the elaborated
rest of the scope, centred or ragged as one block wrapper (an empty scope
wraps nothing); a style or colour declaration already reached every
region inside through `ctx.blockDecls`. -/
private def declScopeWrap (n : String) (inner : Array Block) : Array Block :=
  if n == "centering" then (if inner.isEmpty then #[] else #[.center inner])
  else match Ir.raggedSideOf? n with
    | some side => (if inner.isEmpty then #[] else #[.ragged side inner])
    | none => inner

/-- The block form's whole effect but the recursion: resolve the explicit
ink source through the typed colour door, declare the flow ink, and bump the
flow state. -/
private def inkFlowDecl (ctx : Ctx) (marker : String) (pos : Pos) :
    EM (Option Ir.Palette) := do
  let source := (marker.drop "@ink:".length).toString
  match ← readColor ctx ctx.palette none source pos with
  | .resolved c _ =>
    let pal := ctx.palette.declare "fg" c
    modify fun st => { st with flowPalette := some pal
                               flowGen := st.flowGen + 1 }
    return some pal
  | .missing =>
    warnPaletteMiss ctx source pos
    return none
  | .rejected => return none

private def warnPageColorMiss (ctx : Ctx) (source : String) (pos : Pos) : EM Unit :=
  warnOnce ctx ("palette:" ++ source) .W0304
    s!"'{source}' is not in the palette; the page ground is unchanged" pos
    (help := "declare the colour before using it as a page ground")

private def pageGroundDecl (ctx : Ctx) (marker : String) (pos : Pos) :
    EM (Option Ir.Palette) := do
  let source := (marker.drop Compat.pageColorMarkPrefix.length).toString
  match ← readColor ctx ctx.palette none source pos with
  | .resolved c _ => return some (ctx.palette.declare "bg" c)
  | .missing =>
    warnPageColorMiss ctx source pos
    return none
  | .rejected => return none

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

/-- The bridge from the pars recursion into the parametrized family,
mirroring `rawWeightList_eq`. -/
private theorem rawParsList_eq (l : List Raw) :
    rawParsList l = measList rawPars l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [rawParsList, measList, ih]

private theorem nestedParsList_eq (l : List Raw) :
    nestedParsList l = measList nestedPars l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [nestedParsList, measList, ih]

private theorem rawParsList_append (a b : List Raw) :
    rawParsList (a ++ b) = rawParsList a + rawParsList b := by
  simp only [rawParsList_eq]; exact measList_append ..

private theorem nestedParsList_append (a b : List Raw) :
    nestedParsList (a ++ b) = nestedParsList a + nestedParsList b := by
  simp only [nestedParsList_eq]; exact measList_append ..

private theorem nestedParsList_le (l : List Raw) :
    nestedParsList l ≤ rawParsList l := by
  simp only [nestedParsList_eq, rawParsList_eq]
  exact measList_le_of_le (fun r => by have := rawPars_split r; omega) l

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
  | .ctrl n _ => n == "centering" || (Ir.raggedSideOf? n).isSome
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

/-- An extracted piece of a body nests no more pars than the body. -/
private theorem extract_pars_le (body : Array Raw) (a b : Nat) :
    rawParsList (body.extract a b).toList ≤ rawParsList body.toList := by
  simp only [rawParsList_eq]; exact measList_extract_le ..

private theorem extract_nested_le (body : Array Raw) (a b : Nat) :
    nestedParsList (body.extract a b).toList ≤ nestedParsList body.toList := by
  simp only [nestedParsList_eq]; exact measList_extract_le ..

/-- The pars companion of `sliceWeight`: what still nests below the
spine's own boundary depth, from `i` on. Kept definitionally over
`nestedParsList` for the same reason as `sliceWeight`. -/
private def slicePars (raws : Array Raw) (i : Nat) : Nat :=
  nestedParsList (raws.toList.drop i)

private theorem slicePars_eq (raws : Array Raw) (i : Nat) :
    slicePars raws i = sliceMeas nestedPars raws i := by
  unfold slicePars sliceMeas; rw [nestedParsList_eq]

private theorem slicePars_here (raws : Array Raw) {i : Nat} (h : i < raws.size) :
    slicePars raws i = nestedPars raws[i] + slicePars raws (i + 1) := by
  simp only [slicePars_eq]; exact sliceMeas_here nestedPars raws h

private theorem slicePars_le (raws : Array Raw) {i j : Nat} (hij : i ≤ j) :
    slicePars raws j ≤ slicePars raws i := by
  simp only [slicePars_eq]; exact sliceMeas_le nestedPars raws hij

/-- An element standing anywhere at or past `i` nests no more pars than the
slice from `i`. -/
private theorem elem_pars_le {raws : Array Raw} {j : Nat} {r : Raw}
    (h : raws[j]? = some r) {i : Nat} (hij : i ≤ j) :
    nestedPars r ≤ slicePars raws i := by
  simp only [slicePars_eq]; exact sliceMeas_elem_le h hij

private theorem extract_slice_pars_le (raws : Array Raw) (a b : Nat) :
    nestedParsList (raws.extract a b).toList ≤ slicePars raws a := by
  rw [nestedParsList_eq, slicePars_eq]; exact sliceMeas_extract_le ..

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
  simp only [slicePars_eq]
  refine sliceMeas_splice_lt h ?_
  rw [hr]
  simp only [nestedPars]
  rw [← nestedParsList_eq]
  exact splitAtPars_pars_lt ctx body pos hp

/-- The pars component of the visible sum, mirroring `visWeightGo` through
the same `visGo`: the component a user-command expansion must not raise. -/
private def visParsGo (user : Array UserCmd) : Nat → Nat :=
  visGo (fun cmd => rawParsList cmd.body.toList) user

/-- Expanding a visible command moves its pars out of the visible sum,
mirroring `visWeight_expand`. -/
private theorem visPars_expand {ctx : Ctx} {name : String} {k : Nat}
    {cmd : UserCmd} (h : lookupUser ctx name = some (k, cmd)) :
    rawParsList cmd.body.toList + visParsGo ctx.user k
      ≤ visParsGo ctx.user ctx.limit := by
  unfold visParsGo
  exact visGo_expand (f := fun cmd => rawParsList cmd.body.toList) h

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
  return some (paraUnder (← get).flowLang (Ir.wrapDecls (← get).blockDecls inlines))

/-- Store one `\title`-family part; both doors — the body's
`takeTitleDecl` and the preamble's `.titleDecl` arm — write through
here. -/
private def storeTitlePart (name : String) (content : Array Inline) : EM Unit :=
  modify fun st => match name with
    | "title" => { st with title := some content }
    | "subtitle" => { st with subtitle := some content }
    | "author" => { st with author := some content }
    | "institute" => { st with institute := some content }
    | _ => { st with date := some content }

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
    storeTitlePart name (← elabInlines ctx body)
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
  -- A title page that declares slots is its slots: each sets its datum (or
  -- its own content) in its own font and alignment, inside the role its
  -- placement is found by. The title stays the document's one level-0
  -- heading wherever its slot stands.
  unless tps.slots.isEmpty do
    let datumOf : Ir.TitleDatum → Option (Array Inline)
      | .title => part st.title
      | .subtitle => part st.subtitle
      | .author => part st.author
      | .institute => part st.institute
      | .date => part st.date
    let mut out : Array Block := #[]
    for (sl, i) in tps.slots.zipIdx do
      let mut lines : Array
          (Array Inline × Option String × Option SymGlue × Bool) := #[]
      for (p, k) in sl.parts.zipIdx do
        let content := match p.datum with
          | some d => datumOf d
          | none => part (some p.content)
        if let some xs := content then
          let xs := match p.font with
            | some tpl => Ir.fillTemplate tpl xs
            | none => xs
          let xs : Array Inline := #[.role (Ir.titlePartRole i k) xs]
          let isTitle := p.datum == some .title
          match lines.back? with
          | some (prev, align, before, hasTitle) =>
            if p.newLine then
              lines := lines.push (xs, p.align, p.before, isTitle)
            else
              lines := lines.pop.push
                (prev ++ #[.text " "] ++ xs, align <|> p.align, before, hasTitle || isTitle)
          | none => lines := lines.push (xs, p.align, none, isTitle)
      let blks : Array Block := lines.zipIdx.map fun ((xs, align, before, hasTitle), k) =>
        let blk : Block :=
          if hasTitle then .section 0 true none xs else .para xs
        let blk : Block := match align with
          | some "center" => .center #[blk]
          | some "right" => .ragged .right #[blk]
          | _ => .ragged .left #[blk]
        if k > 0 then
          match before with
          | some g => .spaced (Ir.Sourced.bare g) #[blk]
          | none => blk
        else blk
      unless blks.isEmpty do
        out := out.push (.role (Ir.titleSlotRole i) blks)
    return out
  let push (inner : Array Block) (before : Option (Sourced SymGlue)) (b : Block) : Array Block :=
    match before, inner.isEmpty with
    | some g, false => inner.push (.spaced g #[b])
    | _, _ => inner.push b
  let mut inner : Array Block := #[]
  let mut pending : Option (Sourced SymGlue) := none
  if let some xs := part st.title then
    -- The document title is a heading at level 0, not a decorated
    -- paragraph: the heading outline starts here (HTML §4.3.11 renders it
    -- as the one <h1>, markdown as the one #), and layout gives it the
    -- scale's LARGE step in the bold face — classes.dtx's \@maketitle sets
    -- {\LARGE \@title \par}. Starred: a title is never numbered.
    inner := push inner none (.section 0 true none xs)
  if let some xs := part st.subtitle then
    inner := push inner (ctx.tokens.findSourced? "subtitlegap") (.para #[.styled (.size "large") xs])
  if let some (c, nm) := tps.separator then
    unless inner.isEmpty && (part st.author).isNone && (part st.institute).isNone
        && (part st.date).isNone do
      -- moloch's own default, `titleseparator linewidth=0.5pt`
      -- (beamerinnerthememoloch.dtx, \moloch@inner@setdefaults), when no
      -- token names one. A default is nobody's declaration, so it carries no
      -- name and the HTML prints the length rather than deferring to a
      -- property `tokenVars` never emitted.
      let th := (ctx.tokens.findSourced? "separatorheight").getD
        (Ir.Sourced.bare { width := Dim.Length.ofSp (Dim.pt 1 / 2) })
      -- The separator stands its declared gap on both sides — the one
      -- `separatorgap` token, above the rule here and below it through
      -- `pending`: under the rule convention (`Layout.interlineFor`) the
      -- gap runs from the title matter's baseline to the rule's top edge
      -- and from its bottom edge to the author's cap line, so one token
      -- means equal visible gaps. It used to stand on the rule line's
      -- phantom body strut, which the convention removed.
      inner := push inner (ctx.tokens.findSourced? "separatorgap") (.rule c nm th)
      pending := ctx.tokens.findSourced? "separatorgap"
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
    pending := ctx.tokens.findSourced? "authorgap"
  if let some xs := part st.institute then
    inner := push inner pending (.para #[.styled (.size "small") xs])
    pending := ctx.tokens.findSourced? "institutegap"
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
      | some g => blocks.push (.spaced (Ir.Sourced.bare g) #[])
      | none => blocks

/-- One keyed declaration accepted from the document, remembered for the
`\theme` site: replacing it there is worth a word (W0348). The store logic
is `applyEvent`'s `.declared` arm — one meaning, two doors. -/
private def noteDeclared (ctx : Ctx) (decl key : String) : EM Unit :=
  modify fun st => applyEvent ctx st (.declared decl key)

/-- The engine tokens over the finished page, for body reads: every value
is determined once the class defaults are applied, so all four resolve. -/
private def engineLengthTokensOfPage (page : PageSpec) :
    Array (String × Dim.SymGlue) :=
  #[("paperwidth", { width := Dim.Length.ofSp page.width }),
    ("paperheight", { width := Dim.Length.ofSp page.height }),
    ("textwidth", { width := Dim.Length.ofSp page.textWidth }),
    ("textheight", { width := Dim.Length.ofSp page.textHeight })]

/-- The engine's own length tokens, LaTeX's page dimen parameters read
onto the token namespace: `paperwidth`/`paperheight` (the physical page),
`textwidth`/`textheight` (the measure between the margins — TeX's own
parameters, TeXbook ch. 23). Resolved eagerly at the read site, as every
token reference is (the `\setlength{\x}{2\x}` rule) — the offered keys of
the one resolving site, `engineLengthTokensOfPage ∘ classPageDefaults`:
offered from the declared page where one is declared, else where the class
already fixes the value. A dimension the class will still adjust after the
preamble fold — the flow classes' text block — is deliberately not
offered: an expression reading it keeps its named error (E0321) rather
than capturing a value the finished page would contradict. -/
private def engineLengthTokens (docClass : Ir.DocClass) (classOptions : String)
    (page : PageSpec) : Array (String × Dim.SymGlue) :=
  let record := docClass.record
  let dflt : PageSpec := {}
  let opts := (classOptions.splitOn ",").map (·.trimAscii.toString)
  let whKnown := !(page.width == dflt.width && page.height == dflt.height) ||
    (match record.model with
     | .face => opts.contains "us" || opts.contains "jis" || record.trimDefault.isSome
     | .frame => true
     | .flow => true)
  let hmKnown := page.hmargin != dflt.hmargin ||
    (match record.model with
     | .face => record.safeMargin.isSome
     | .frame => true
     | .flow => false)
  let vmKnown := page.vmargin != dflt.vmargin ||
    (match record.model with
     | .face => record.safeMargin.isSome
     | .frame => true
     | .flow => true)
  let offered (key : String) : Bool :=
    match key with
    | "paperwidth" | "paperheight" => whKnown
    | "textwidth" => whKnown && hmKnown
    | "textheight" => whKnown && vmKnown
    | _ => false
  (engineLengthTokensOfPage (classPageDefaults record opts page)).filter
    (fun kv => offered kv.1)

/-- The preamble's engine token environment and the shipped page are one
value (shape: `_set_eq` over the token array, as an inclusion — the offered
keys are exactly those the class already fixes): every binding
`engineLengthTokens` offers is the corresponding entry of the resolved
page's environment. The one deliberate remainder is the flow classes'
undeclared text block, applied by the fold's `!sawPage` step — and exactly
then `textwidth` is withheld here, so no offered token can disagree with
the page that ships. This is the statement whose absence would let a
preamble `\setlength` read a different page than the document renders
on. -/
private theorem engine_tokens_agree (docClass : Ir.DocClass)
    (classOptions : String) (page : PageSpec) :
    ∀ kv ∈ engineLengthTokens docClass classOptions page,
      kv ∈ engineLengthTokensOfPage (classPageDefaults docClass.record
        ((classOptions.splitOn ",").map (·.trimAscii.toString)) page) := by
  intro kv h
  exact (Array.mem_filter.mp h).1

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


/-- The `\palette` option run: `decorative` marks the block's entries as
deliberately low-contrast and exempt from the pairing check. An
unrecognised option skips the block (W0316) rather than applying it as the
base palette — a variant block applied as base would silently restyle the
document. Returns (decorative, skipBlock); both `\palette` doors — the
preamble's `.palette` arm and the body arm — read their options here. -/
private def parsePaletteOpts (ctx : Ctx) (src : String) (pos : Pos) :
    EM (Bool × Bool) := do
  let mut decorative := false
  let mut skipBlock := false
  for e in Decl.splitEntries src do
    if e == "decorative" then
      decorative := true
    else
      diag ctx .W0316 s!"unknown option in '\\palette': {e.quote}; block skipped" pos
        (help := "options: decorative")
      skipBlock := true
  return (decorative, skipBlock)

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
      else if builtinNames.contains key || (escapeOf key).isSome then
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
        match ← readColor ctx pal none valueSrc pos with
        | .resolved c _ => pal := ← put pal c
        | .rejected => pure ()
        | .missing =>
          match Decl.parseValue valueSrc with
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
  rw [sliceWeight_eq]; exact sliceMeas_end rawWeight raws h

private theorem slicePars_end (raws : Array Raw) {j : Nat}
    (h : raws.size ≤ j) : slicePars raws j = 0 := by
  rw [slicePars_eq]; exact sliceMeas_end nestedPars raws h

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
  /-- A `\vskip` stands here. Its length is not read: the venue
  contributes the bars' weights, and the gaps beside them are the
  engine's rhythm (`Ir.titleBarGap`/`Ir.titleBarSkip`) unless the
  document declares its own through `\style{titlepage}`. The event
  survives to close the author block's trailing skip; `\vskip -\parskip`
  emits nothing — under the engine's gap model a declared gap already
  replaces the paragraph skip, so the venue's cancellation is the
  identity. -/
  | gap
  /-- An `\hrule`; `none` when its declared height cannot be read, which
  abandons that side's extraction entirely. -/
  | bar (w : Option Dim.SymGlue)
  /-- `\@title`, with the size, weight, and alignment declarations in
  force where it stands. -/
  | title (size : Option String) (bold : Bool) (align : Option String)
  /-- `\@author`, with the weight in force and whether a zero-width
  `\rule` strut props its line — the NeurIPS-lineage author `tabular`
  (`\begin{tabular}[t]{c}\bf\rule{\z@}{24\p@}\@author`), read off the
  environment that holds it (`authorStrutList`). Ink, like `.content`: it
  closes the bottom bar's trailing skip. -/
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
  strut : Bool := false

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

/-- **beamer's spelling of the LaTeX internals a refused body's read-out
already knows.** A theme writes its title page over `\inserttitle` and
`\insertauthor`; latex.ltx's own title code writes `\@title` and
`\@author`. They name the same declared datum — beamer defines each insert
as the document's own metadata (beamerbasetitle.sty, the `\insert...`
family) — so the read-out must not know one spelling and miss the other.

One table, resolved once (`barCtrlName`), so the scans below match a
single name: the whole vocabulary difference is here, and a scan cannot
learn one alias and not another (`barScan_alias_agree`). A datum with no
event of its own (`\insertdate`, the institute, a frame number) aliases to
`\@date`, which is what the scan already spells "ink that is not the
title". -/
def beamerInsertAlias : List (String × String) :=
  [("inserttitle", "@title"),
   ("insertshorttitle", "@title"),
   ("insertauthor", "@author"),
   ("insertshortauthor", "@author"),
   ("insertdate", "@date"),
   ("insertshortdate", "@date"),
   ("insertsubtitle", "@date"),
   ("insertinstitute", "@date"),
   ("insertshortinstitute", "@date")]

/-- The name a refused body's scans read: beamer's insert resolved to the
internal it aliases, every other control word itself. -/
def barCtrlName (n : String) : String := (beamerInsertAlias.lookup n).getD n

/-- The zero-width `\rule` strut that props an author's line — the
NeurIPS-lineage author `tabular`
(`\begin{tabular}[t]{c}\bf\rule{\z@}{24\p@}\@author`), read off the
environment that holds it. The strut's own height is not taken; the
engine's is `Ir.titleAuthorStrut`. Groups are looked through; everything
else stays the refusal's.

Only the strut: the weight in force and the author datum itself are the
scan's own business, threaded and emitted where they stand
(`barScanList`). Folding the whole shape here instead cost the read-out
every other datum the same environment held — a theme's title and its
author share one canvas, and an environment answered for by its author
alone reported no title. -/
private def authorStrutList (found : Bool) : List Raw → Bool
  | [] => found
  | .group body _ :: rest =>
    authorStrutList (authorStrutList found body.toList) rest
  | .ctrl "rule" _ :: rest =>
    let strut := match barSkipSp rest with
      | .group w _ :: _ => match barSkipSp w.toList with
        | .ctrl "z@" _ :: _ => true
        | _ => false
      | _ => false
    authorStrutList (found || strut) rest
  | _ :: rest => authorStrutList found rest
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
    else if let some side := Ir.raggedSideOf? n then
      envStyleScanList { st with align := some side.align } rest
    else envStyleScanList st rest
  | _ :: rest => envStyleScanList st rest
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    (have hb : sizeOf body = 1 + sizeOf body.toList := rfl; omega)

/-- The size the environment's *body* sets at, read off a refused
redefinition's begin body with TeX's scoping: a size switch standing at the
begin body's top level holds to the environment's end, one inside a group
(the heading's `\centerline{\large ...}`) only to its brace. The begin
body's last item, when it is an environment, is the one the definer's split
idiom leaves open for the body (`\begin{quote}` in the begin body,
`\end{quote}` in the end body), so its own top level counts too. -/
private def envBodySizeList (acc : Option String) : List Raw → Option String
  | [] => acc
  | [.env _ body _] => envBodySizeList acc body.toList
  | .ctrl n _ :: rest =>
    envBodySizeList (if sizeCtrlNames.contains n then some n else acc) rest
  | _ :: rest => envBodySizeList acc rest
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    (have hb : sizeOf body = 1 + sizeOf body.toList := rfl; omega)

/-- The kernel's commands that take argument groups and set no ink where they
stand, with how many (latex.ltx: `\addcontentsline{file}{type}{text}`,
`\addtocontents{file}{text}`, `\markboth{left}{right}`, `\markright{right}`,
`\label{key}`, `\index{entry}`, `\vspace{skip}`, `\hspace{skip}`,
`\thispagestyle{style}`): what a heading reader leaves unread. -/
private def inklessArgs : List (String × Nat) :=
  [("addcontentsline", 3), ("addtocontents", 2), ("markboth", 2), ("markright", 1),
   ("label", 1), ("index", 1), ("vspace", 1), ("hspace", 1), ("thispagestyle", 1)]

/-- The words a redefined environment's begin body sets ahead of the body —
the heading a venue writes (`\centerline{\large\bf Summary}`) — with the
body's own container left out: the begin body's last environment, which
the definer's split idiom leaves open for the body. A word that reads as a
length, or a glue keyword beside one, is a skip's argument (`\vskip 2ex
plus 1ex`), one inside `[…]` an option's (`\vspace` arrives as
`\block[before = …]`), and the groups of a command that sets no ink
(`\addcontentsline{toc}{section}{…}`, `\label`) its arguments — never
heading text. `skip` counts the groups still owed such a command. -/
private def envHeadWords (acc : Array String) (opt : Bool) (skip : Nat) :
    List Raw → Array String
  | [] => acc
  | [.env _ _ _] => acc
  | .sym '[' _ :: rest => envHeadWords acc true skip rest
  | .sym ']' _ :: rest => envHeadWords acc false skip rest
  | .space :: rest => envHeadWords acc opt skip rest
  | .word w _ :: rest =>
    let skipped := opt || (Decl.parseLength w).isSome || ["plus", "minus", "*"].contains w
    envHeadWords (if skipped then acc else acc.push w) opt (if w == "*" then skip else 0) rest
  | .group body _ :: rest =>
    if skip > 0 then envHeadWords acc opt (skip - 1) rest
    else envHeadWords (envHeadWords acc opt 0 body.toList) opt 0 rest
  | .env _ body _ :: rest => envHeadWords (envHeadWords acc opt 0 body.toList) opt 0 rest
  | .ctrl n _ :: rest => envHeadWords acc opt ((inklessArgs.lookup n).getD 0) rest
  | _ :: rest => envHeadWords acc opt 0 rest
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    (have hb : sizeOf body = 1 + sizeOf body.toList := rfl; omega)

/-- The size × bold font fragment `envStyleInterpret` and `barInterpret`
both spell: the inline tree the closed style vocabulary can honour. -/
private def fontFragment (size : Option String) (bold : Bool) :
    Option (Array Ir.Inline) :=
  match size, bold with
  | some s, true => some #[.styled (.size s) #[.styled .bold #[]]]
  | some s, false => some #[.styled (.size s) #[]]
  | none, true => some #[.styled .bold #[]]
  | none, false => none

/-- `envStyleScanList`'s verdict as the style fragment the built-in can
honour, `barInterpret`'s font shape. -/
private def envStyleInterpret (sc : BarSt) : Option Ir.ElementStyle :=
  let font := fontFragment sc.size sc.bold
  if font.isNone && sc.align.isNone then none
  else some { font := font, align := sc.align }

/-- The scan: one pass over the refused body, expanding the user commands
visible below `bound` (the definition-order rule that terminates every
expansion here), descending into groups with a copy of the declarations in
force so a scoped declaration does not escape. Unrecognised commands are
transparent — the refusal already counted them; this pass only collects
what the closed list can honour.

An environment is a grouping like any other and is descended into on the
same terms, its author strut read off it first (`authorStrutList`) so a
propped author line still declares one. A theme writes its title page
inside one — a `tikzpicture`, a `minipage` — so an environment answered for
by one opaque event hid every declaration and every datum the body placed,
and the read-out found no title to style. -/
private def barScanList (user : Array UserCmd) (bound : Nat) (st : BarSt)
    (events : Array BarEvent) : List Raw → Array BarEvent
  | [] => events
  | .space :: rest => barScanList user bound st events rest
  | .par _ :: rest => barScanList user bound st events rest
  | .sym _ _ :: rest => barScanList user bound st events rest
  | .word w _ :: rest =>
    let events := if barWordTransparent w then events else events.push .content
    barScanList user bound st events rest
  | .verb _ _ _ :: rest => barScanList user bound st (events.push .content) rest
  | .math _ _ _ :: rest => barScanList user bound st (events.push .content) rest
  | .env _ body _ :: rest =>
    let st := { st with strut := st.strut || authorStrutList false body.toList }
    let events := barScanList user bound st events body.toList
    barScanList user bound st events rest
  | .group body _ :: rest =>
    let events := barScanList user bound st events body.toList
    barScanList user bound st events rest
  | .ctrl n0 _ :: rest =>
    let n := barCtrlName n0
    if n == "vskip" then
      let events := match barLength rest with
        | .cancel => events
        | _ => events.push .gap
      barScanList user bound st events rest
    else if n == "hrule" then
      barScanList user bound st (events.push (.bar (barRuleWeight rest))) rest
    else if sizeCtrlNames.contains n then
      barScanList user bound { st with size := some n } events rest
    else if n == "bf" || n == "bfseries" then
      barScanList user bound { st with bold := true } events rest
    else if n == "centering" then
      barScanList user bound { st with align := some "center" } events rest
    else if let some side := Ir.raggedSideOf? n then
      barScanList user bound { st with align := some side.align } events rest
    else if n == "@title" then
      barScanList user bound st (events.push (.title st.size st.bold st.align)) rest
    else if n == "@author" then
      barScanList user bound st (events.push (.author st.bold st.strut)) rest
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

/-- **The invariant the read-out owed: a theme's spelling of a declared
datum reads as the engine's own.** A refused redefinition's declarative
content is read through one closed vocabulary, and a control word reaches
that vocabulary only after `barCtrlName` has resolved it — so beamer's
insert and the LaTeX internal it aliases are not merely read to the same
style, they are the same scan step in the same state. The read-out knew
`\@title` and not `\inserttitle`, so a theme-authored title page read as no
title page at all: the refusal stood alone and the declarative appearance
the body carried went with the layout code that could not be expressed.

Two spellings that resolve alike scan alike, at the head of a run and
therefore — the scan being a fold that reads no other name — at any
occurrence. `barCtrlName_alias_resolves` supplies both hypotheses for every
row of the table, so the property is the table's, not one name's. -/
theorem barScan_alias_agree (user : Array UserCmd) (bound : Nat) (st : BarSt)
    (events : Array BarEvent) (post : List Raw) (p q : Pos) (b l : String)
    (hb : barCtrlName b = l) (hl : barCtrlName l = l) :
    barScanList user bound st events (.ctrl b p :: post)
      = barScanList user bound st events (.ctrl l q :: post) := by
  rw [barScanList, barScanList, hb, hl]

/-- Every row of the alias table resolves its beamer spelling to the
internal, and the internal to itself: the two hypotheses
`barScan_alias_agree` asks for, discharged for the whole vocabulary at
once. -/
theorem barCtrlName_alias_resolves :
    (beamerInsertAlias.all fun r =>
      barCtrlName r.1 == r.2 && barCtrlName r.2 == r.2) = true := by
  decide +kernel

/-- Read the event sequence relative to `\@title` into the style fragment
the built-in can honour: the last bar before the title and the first after
it — their declared *weights* only; the skips beside a venue's bars are
the engine's rhythm (`Ir.titleBars`'s defaults), never the venue's
`\vskip`s — plus the size, weight, and alignment the title stood under. A
body with no `\@title` is not a title restyling — rule (b) stands alone
and nothing is extracted. A bar whose weight cannot be read extracts
nothing on its side. -/
private def barInterpret (events : Array BarEvent) : Option Ir.ElementStyle := Id.run do
  let some t := events.findIdx? (· matches .title _ _ _) | return none
  let mut st : Ir.ElementStyle := {}
  if let some (.title size bold align) := events[t]? then
    st := { st with
      align := align
      font := fontFragment size bold }
  let mut above : Option Nat := none
  for i in [0:t] do
    if h : i < events.size then
      if events[i] matches .bar _ then above := some i
  if let some i := above then
    if h : i < events.size then
      if let .bar (some w) := events[i] then
        st := { st with ruleAbove := some w }
  let mut below : Option Nat := none
  for i in [t + 1:events.size] do
    if h : i < events.size then
      if below.isNone && (events[i] matches .bar _) then below := some i
  if let some j := below then
    if h : j < events.size then
      if let .bar (some w) := events[j] then
        st := { st with ruleBelow := some w }
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
              | .gap => return true
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
elabBlocks measure still falls — in every component at once, since the
bound is parametrized by the pointwise body measure. -/
private theorem bindCmd_visGo (f : UserCmd → Nat) (ctx : Ctx) (cmd : UserCmd) :
    visGo f (bindCmd ctx cmd).user (bindCmd ctx cmd).limit
      ≤ visGo f ctx.user ctx.limit + f cmd := by
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
  simp only [visGo]
  obtain ⟨hlt, hcmd⟩ := Array.getElem?_eq_some_iff.mp hat
  rw [visGo_congr fun m hm => hsame m hm]
  simp only [hlt, dite_true, hcmd]
  have := visGo_mono f ctx.user (show min ctx.limit ctx.user.size ≤ ctx.limit by omega)
  omega

/-- The weight instance of `bindCmd_visGo`. -/
private theorem bindCmd_visWeight (ctx : Ctx) (cmd : UserCmd) :
    visWeightGo (bindCmd ctx cmd).user (bindCmd ctx cmd).limit
      ≤ visWeightGo ctx.user ctx.limit + rawWeightList cmd.body.toList := by
  unfold visWeightGo; exact bindCmd_visGo _ ctx cmd

/-- The pars instance of `bindCmd_visGo`. -/
private theorem bindCmd_visPars (ctx : Ctx) (cmd : UserCmd) :
    visParsGo (bindCmd ctx cmd).user (bindCmd ctx cmd).limit
      ≤ visParsGo ctx.user ctx.limit + rawParsList cmd.body.toList := by
  unfold visParsGo; exact bindCmd_visGo _ ctx cmd

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

/-- Discharges the block knot's termination goals: the lexicographic fall
first (`lex6_of`, then `omega` over the `have` facts standing beside each
recursive call), on the goal as the elaborator's own cleanup left it; only
a goal that needs more normal form (a list's length under a cons) takes a
second simp pass before the same two steps. Running that pass on every
goal cost the knot more than 10,000 of its 200,000 heartbeats (judged by
deletion and rebuild). -/
macro "blocks_dec" : tactic =>
  `(tactic| (
    first
      | (apply lex6_of; omega)
      | (simp_wf
         <;> (first
           | omega
           | (apply lex6_of; omega)))))

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

private theorem itemsW_eq (l : List (Array Raw)) :
    itemsW l = measList (fun it => rawWeightList it.toList) l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [itemsW, measList, ih]

private theorem itemsP_eq (l : List (Array Raw)) :
    itemsP l = measList (fun it => nestedParsList it.toList) l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [itemsP, measList, ih]

private theorem itemsW_push (a : Array (Array Raw)) (it : Array Raw) :
    itemsW (a.push it).toList = itemsW a.toList + rawWeightList it.toList := by
  simp only [itemsW_eq]; exact measList_push ..

private theorem itemsP_push (a : Array (Array Raw)) (it : Array Raw) :
    itemsP (a.push it).toList = itemsP a.toList + nestedParsList it.toList := by
  simp only [itemsP_eq]; exact measList_push ..

private theorem itemsW_elem_le {a : Array (Array Raw)} {m : Nat}
    {it : Array Raw} (h : a[m]? = some it) :
    rawWeightList it.toList ≤ itemsW a.toList := by
  obtain ⟨hm, hget⟩ := Array.getElem?_eq_some_iff.mp h
  rw [itemsW_eq]
  exact measList_mem_le (μ := fun it => rawWeightList it.toList)
    (hget ▸ Array.getElem_mem_toList hm)

private theorem itemsP_elem_le {a : Array (Array Raw)} {m : Nat}
    {it : Array Raw} (h : a[m]? = some it) :
    nestedParsList it.toList ≤ itemsP a.toList := by
  obtain ⟨hm, hget⟩ := Array.getElem?_eq_some_iff.mp h
  rw [itemsP_eq]
  exact measList_mem_le (μ := fun it => nestedParsList it.toList)
    (hget ▸ Array.getElem_mem_toList hm)

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
private def itemSplitGo (ctx : Ctx) (body : Array Raw) (pos : Pos) (desc : Bool) (j : Nat)
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
        itemSplitGo ctx body pos desc (j + 1) (items.push curItem)
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
        itemSplitGo ctx body pos desc (j + 1) items steps itemPauses pauses #[]
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
        itemSplitGo ctx body pos desc (j + 1) items steps itemPauses (pauses + 1)
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
        itemSplitGo ctx body pos desc (j + 1) items steps itemPauses (pauses + 1)
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
        itemSplitGo ctx body pos desc (j + 1) items steps itemPauses pauses curItem
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
          -- A description item's label is its content (`descItems`), not
          -- an override of a marker.
          unless desc do
            warnOnce ctx "item:marker" .W0110
              "'\\item' [marker] override is not modelled; the level's marker stands" pos
              (help := "\\style{itemize}{ marker = {...} } declares a level's marker")
          itemSplitGo ctx body pos desc (j + 1) items steps itemPauses pauses curItem
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
          let curStep ← match Ir.overlayRange w with
            | some s => pure (some s)
            | none => do
              warnOverlaySpec ctx w pos
              pure curStep
          itemSplitGo ctx body pos desc (j + 1) items steps itemPauses pauses curItem
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
          itemSplitGo ctx body pos desc (j + 1) items steps itemPauses pauses
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
        itemSplitGo ctx body pos desc (j + 1) items steps itemPauses pauses
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
        if let .ctrl c _ := item then
          if counterCtrl c then
            -- A counter command before the first `\item` sets its counter,
            -- as LaTeX allows there (ltlists.dtx: the list's own settings
            -- follow `\list`'s): a declaration, never content.
            let ⟨k, hk⟩ ← counterArm ctx body (j + 1) c pos
            return ← itemSplitGo ctx body pos desc k items steps itemPauses pauses curItem
              curStep curPauses awaitSpec inOpt seen strayDiagged bound pbound
              (by
                have hwj := sliceWeight_here body h
                have hle := sliceWeight_le body hk
                omega)
              (by
                have hpj := slicePars_here body h
                have h2 := rawPars_split body[j]
                have hle := slicePars_le body hk
                omega)
        if !isSpaceOrPar item && !strayDiagged then
          diag ctx .E0310 s!"content before the first '\\item'" pos
        itemSplitGo ctx body pos desc (j + 1) items steps itemPauses pauses curItem
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

/-- `\multicolumn{n}{spec}{text}` read from `raws`, whose element `j` is the
command: the count when it is a numeral; the one column its spec declares,
read by the table's own spec reader so `p{…}` keeps its width, with what
that reader names — a `|`, an unknown column type — and an `@{}`, whose pad
a span does not model; the text group; and the index after it. `none` when
the three groups are not there. -/
private def readMulticolumn (ctx : Ctx) (raws : Array Raw) (j : Nat) :
    Option (Option Nat × Ir.ColSpec × Array (String × String × String) × Array Raw × Nat) :=
  let j0 := skipSpaces raws (j + 1)
  let j1 := skipSpaces raws (j0 + 1)
  let j2 := skipSpaces raws (j1 + 1)
  match raws[j0]?, raws[j1]?, raws[j2]? with
  | some (.group count _), some (.group spec _), some (.group text _) =>
    let (cols, padL, padR, warns) := parseColSpec ctx spec
    let warns := if padL && padR then warns else warns.push ("multicolumn-pad",
      "'@{}' in a '\\multicolumn' spec is not modelled: the span keeps its column pads", "")
    some ((Parse.rawSrc count).trimAscii.toString.toNat?,
      cols[0]?.getD { width := .natural, align := .left }, warns, text, j2 + 1)
  | _, _, _ => none

/-- The span a `\multicolumn` at a cell's head declares, when its count is
a numeral, with every loss its spec and count carry named where it stands:
what the spec reader named, and a count the engine cannot read, whose text
then fills one cell. -/
private def spanOf (ctx : Ctx) (count : Option Nat) (spec : Ir.ColSpec)
    (warns : Array (String × String × String)) (pos : Pos) :
    EM (Option (Nat × Ir.ColSpec)) := do
  for (key, msg, help) in warns do
    warnOnce ctx ("tabular:" ++ key) .W0104 msg pos
      (help := if help.isEmpty then none else some help)
  match count with
  | some c => return some (max c 1, spec)
  | none =>
    warnOnce ctx "ctrl:multicolumn:unread" .W0337
      "'\\multicolumn' span is not a numeral the engine reads: its text fills one \
cell in its column's alignment" pos
    return none

/-- A user command at a cell's head whose definition opens with
`\multicolumn`: the invocation's expansion, and how many elements of `raws`
it took (the command, at `j`, and its arguments). TeX expands a cell's
first tokens looking for the `\omit` a `\multicolumn` begins with; the
expansion is the math path's raw-level one, terminating by definition
order (`expandMathList`). -/
private def expandSpanHead (ctx : Ctx) (raws : Array Raw) (j : Nat) (name : String) :
    Option (Array Raw × Nat) :=
  (lookupUser ctx name).bind fun (k, cmd) =>
    if (trimRaws cmd.body)[0]? matches some (Raw.ctrl "multicolumn" _) then
      let rest := raws.extract (j + 1) raws.size
      let (bindings, rest') := bindMathArgs cmd.params rest
      some (trimRaws (expandMathList ctx.user k bindings cmd.body.toList),
        1 + (rest.size - rest'.size))
    else none

/-- Close a cell that a `\multicolumn` opened: record its span at the cell
just pushed, and push the `n − 1` cells it covers, empty, so the grid stays
rectangular. -/
private def closeSpan (spans : Array Ir.ColSpan) (cells : Array (Array Inline))
    (row : Nat) : Option (Nat × Ir.ColSpec) → Array Ir.ColSpan × Array (Array Inline)
  | none => (spans, cells)
  | some (n, spec) =>
    (spans.push { row := row, col := cells.size - 1, n := n, spec := spec },
      cells ++ Array.replicate (n - 1) #[])

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
  let mut flexTarget : Option Ir.TableTarget := none
  if n == "tabularx" then
    match body[k]? with
    | some (.group targetRaw _) =>
      let src := rawSrc targetRaw
      match tableTarget ctx src with
      | .ok target => flexTarget := some target
      | .error why =>
        diag ctx .E0331 s!"cannot read tabularx target width from '{src}': {why}" pos
          (help := "use sums, differences, scalar products, local horizontal measures, or absolute lengths")
        flexTarget := some (.frac 1000)
      k := skipSpaces body (k + 1)
    | _ =>
      diag ctx .E0304 "'tabularx' needs a {target width} before its {column spec}" pos
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
    let (cs, pl, pr, warns) := parseColSpec ctx spec flexTarget
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
  let mut spans : Array Ir.ColSpan := #[]
  let mut cells : Array (Array Inline) := #[]
  let mut cellRaws : Array Raw := #[]
  -- the span a `\multicolumn` at the head of the cell being collected
  -- declares, recorded when the cell closes
  let mut spanHere : Option (Nat × Ir.ColSpec) := none
  let mut j := k
  let ruleNames := ["toprule", "midrule", "bottomrule", "hline",
    "cmidrule", "cline", "addlinespace"]
  for _ in [k:body.size] do
    if h' : j < body.size then
      match body[j] with
      | .ctrl "\\" bpos =>
        cells := cells.push (Ir.wrapDecls (← get).blockDecls (← elabInlines ctx (trimRawEdges cellRaws)))
        (spans, cells) := closeSpan spans cells rows.size spanHere
        spanHere := none
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
        cells := cells.push (Ir.wrapDecls (← get).blockDecls (← elabInlines ctx (trimRawEdges cellRaws)))
        (spans, cells) := closeSpan spans cells rows.size spanHere
        spanHere := none
        cellRaws := #[]
        j := j + 1
      | .ctrl "multicolumn" rpos =>
        -- At a cell's head the text is the cell and the count and spec its
        -- span; anywhere else LaTeX refuses it, and the text stays in place.
        match readMulticolumn ctx body j with
        | some (count, spec, warns, text, next) =>
          if cellRaws.all isSpaceOrPar && spanHere.isNone then
            spanHere ← spanOf ctx count spec warns rpos
          else
            warnOnce ctx "ctrl:multicolumn:misplaced" .W0337 Compat.multicolumnMisplaced rpos
              (help := Compat.multicolumnMisplacedHelp)
          cellRaws := cellRaws.push (.group text rpos)
          j := next
        | none =>
          cellRaws := cellRaws.push body[j]
          j := j + 1
      | .ctrl name rpos =>
        if ruleNames.contains name &&
            cellRaws.all isSpaceOrPar && cells.isEmpty then
          j := j + 1
          cellRaws := #[]
          -- booktabs' optional [width] per rule is not modelled:
          -- the three weights are the design, one source.
          if let .took j' := scanBracketArg body j rpos then
            warnOnce ctx ("tabular:rulewidth:" ++ name) .N0102
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
          -- A command whose definition opens with `\multicolumn`, at a
          -- cell's head, is read as the `\multicolumn` it expands to; its
          -- expansion must stay inside the cell.
          let head := if cellRaws.all isSpaceOrPar && spanHere.isNone then
              (expandSpanHead ctx body j name).bind fun (exp, took) =>
                (readMulticolumn ctx exp 0).bind fun (count, spec, warns, text, next) =>
                  let tail := exp.extract next exp.size
                  if tail.any (fun r => r matches .sym '&' _ | .ctrl "\\" _) then none
                  else some (count, spec, warns, text, tail, took)
            else none
          match head with
          | some (count, spec, warns, text, tail, took) =>
            spanHere ← spanOf ctx count spec warns rpos
            cellRaws := (cellRaws.push (.group text rpos)) ++ tail
            j := j + took
          | none =>
            cellRaws := cellRaws.push body[j]
            j := j + 1
      | r' =>
        cellRaws := cellRaws.push r'
        j := j + 1
    else break
  if cellRaws.any (!isSpaceOrPar ·) || !cells.isEmpty then
    cells := cells.push (Ir.wrapDecls (← get).blockDecls (← elabInlines ctx (trimRawEdges cellRaws)))
    (spans, cells) := closeSpan spans cells rows.size spanHere
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
  blocks := blocks.push (.table cols padL padR rows rules spans)
  return blocks

/-- One listing block from a lexically blind capture. `{verbatim}` is the
default spec, as always. `{lstlisting}` reads listings' per-environment
keys from its option head, `{minted}` its option head and its mandatory
language argument. Honoured keys: `caption` (numbered in flow order — the
listing counter steps exactly as the equation counter does), `label`
(bound to the caption's number), `numbers=left`/`none` and minted's
`linenos`, `language` (named data the engine does not colour by: the
spelling normalizes through `Ir.listingLang?` to the one token both text
artifacts carry, and a spelling outside the token grammar is named W0110
and carries nothing — never raw text into an attribute), and a
`basicstyle` at the engine's own listing step (mono at footnotesize —
the code-frame convention Layout sets). Every other key, and a value
asking for what the engine does not draw, is named W0110 — never a
silent drop. The caption is kept as its literal text: a listing caption
is plain prose; markup inside one is out of the blind capture's reach. -/
private def listingBlock (ctx : Ctx) (env s : String) (pos : Pos) : EM Block := do
  if env == "verbatim" then
    return .verbatim none s {}
  let (opts, afterOpt) := (Parse.listingOptHead s).getD ("", 0)
  let mut content := s
  let mut caption : Option String := none
  let mut label : Option String := none
  let mut numbers := false
  let mut language : Option Ir.ListingLang := none
  let langOf (raw : String) : EM (Option Ir.ListingLang) := do
    match Ir.listingLang? raw with
    | some l => pure (some l)
    | none =>
      diag ctx .W0110 s!"listing language '{raw.trimAscii.toString}' is not a plain name; the \
listing carries no language" (some pos)
        (help := "spell it as letters, digits, +, #, - or . (python, c++, c#)")
      pure none
  for entry in Decl.splitEntries opts do
    let bare := entry.trimAscii.toString
    if bare.isEmpty then
      continue
    match Decl.splitEntry entry with
    | some ("caption", v) =>
      let v := listingVal v
      caption := if v.isEmpty then none else some v
    | some ("label", v) => label := some (listingVal v)
    | some ("numbers", v) =>
      let v := v.trimAscii.toString
      if v == "left" then numbers := true
      else if v == "none" then numbers := false
      else
        diag ctx .W0110 s!"'numbers={v}' asks for a numbering the engine \
does not draw; lines keep no numbers" (some pos)
          (help := "numbers=left draws them")
    | some ("linenos", v) =>
      numbers := v.trimAscii.toString != "false"
    | some ("language", v) => language ← langOf (listingVal v)
    | some ("basicstyle", v) =>
      match Ir.sizeScale.find? (fun p => p.1 != "footnotesize"
          && (v.splitOn ("\\" ++ p.1)).length > 1) with
      | some (nm, _) =>
        diag ctx .W0110 s!"'basicstyle' asks for \\{nm}; listings set at \
the engine's own step, mono at footnotesize" (some pos)
      | none => pure ()
    | some (k, _) =>
      diag ctx .W0110 s!"listing key '{k}' is not honoured; ignored" (some pos)
    | none =>
      if bare == "linenos" then numbers := true
      else diag ctx .W0110 s!"listing key '{bare}' is not honoured; ignored" (some pos)
  if env == "minted" then
    match mintedLangHead s afterOpt with
    | some (lang, _) => language ← langOf lang
    | none =>
      diag ctx .E0304 s!"'\\begin\{minted}' needs its \{language} argument" (some pos)
    content := (s.drop (listingContentStart env s)).toString
  else
    content := (s.drop afterOpt).toString
  let spec : Ir.ListingSpec ← match caption with
    | some cap => do
      let num := (← get).ctr.lstNum + 1
      modify fun st => { st with ctr := { st.ctr with lstNum := num } }
      match label with
      | some key =>
        -- The anchor rides in the caption, as an equation's rides in its
        -- content: the reference's target must ship on the page. The kind
        -- is `none` until RefKind grows a listing constructor (the cref
        -- prefix is the resolver slice's): a \cref meanwhile sets the
        -- plain number, named W0380 — degraded, never silently wrong.
        recordLabel ctx key (some { kind := none, num := toString num }) pos
        pure { caption := some (num, #[.label key, .text cap]), numbers := numbers,
               language := language }
      | none =>
        pure { caption := some (num, #[.text cap]), numbers := numbers,
               language := language }
    | none => do
      if let some key := label then
        recordLabel ctx key (← get).refTarget pos
      pure { caption := none, numbers := numbers, language := language }
  return .verbatim none content spec

/-- `(t)`: amsmath's `\tagform@` (`\maketag@@@{(\ignorespaces#1\unskip…)}`)
around an elaborated tag, the parentheses joining the tag's first and last
runs of text where it has them — so a plain tag is the one run a counter's
number is, and ships the same ink. -/
private def tagForm (t : Array Ir.Inline) : Array Ir.Inline :=
  let opened : Array Ir.Inline := match t[0]? with
    | some (Ir.Inline.text s) => t.set! 0 (.text ("(" ++ s))
    | _ => #[Ir.Inline.text "("] ++ t
  match opened.back? with
  | some (Ir.Inline.text s) => opened.pop.push (.text (s ++ ")"))
  | _ => opened.push (.text ")")

/-- A caption word the document may redefine (`\proofname`, `\qedsymbol`):
its definition where one stands, else `dflt`. -/
private def definedOr (ctx : Ctx) (name : String) (pos : Pos) (dflt : EM (Array Inline)) :
    EM (Array Inline) := do
  if (lookupUser ctx name).isSome then elabInlines ctx #[.ctrl name pos] else dflt

/-- The `\qedsymbol` in force: the document's definition where one stands,
else amsthm's box as the math face's □ (amsthm.sty's `\openbox` draws it in
rules). -/
private def qedMark (ctx : Ctx) (pos : Pos) : EM (Array Inline) :=
  definedOr ctx "qedsymbol" pos (return #[← elabMathInline ctx false #[.ctrl "square" pos] pos])

/-- A display's top-level `\qedhere`, taken out before the math parser reads
the body, and where the first one stood. -/
private def dropQedHere (body : Array Raw) : Array Raw × Option Pos :=
  body.foldl (fun (out, at?) r => match r with
    | .ctrl "qedhere" p => (out, at?.orElse fun _ => some p)
    | r => (out.push r, at?)) (#[], none)

/-- A `\qedhere` in a display whose QED this engine cannot stand where amsthm
sets it — beside an alignment's row, under a number — is named, and the
proof's end sets the QED on a line of its own after the display. -/
private def qedHereLost (ctx : Ctx) (env : String) (p : Pos) : EM Unit := do
  if (← get).ctr.thm.proofs == 0 then return
  warnOnce ctx ("qedhere:" ++ env) .W0435
    s!"'\\qedhere' in '\{{env}}' does not set its QED where amsthm sets it; the QED \
stands on a line of its own after the display" p
    (help := "an unnumbered \\[ ... \\] sets it beside the formula")

/-- The QED a display's `\qedhere` sets in the number's slot (amsthm.sty
`\displaymath@qed`: `\eqno\hbox{\qedsymbol}`), inside a proof — outside one
amsthm's stack is empty and it sets nothing — and the proof told its end
sets none. -/
private def qedHereTag (ctx : Ctx) (p : Pos) : EM (Option (Array Inline)) := do
  if (← get).ctr.thm.proofs == 0 then return none
  let mark ← qedMark ctx p
  modify fun st => { st with ctr := { st.ctr with thm := { st.ctr.thm with qedPlaced := true } } }
  return some (Ir.wrapDecls (← get).blockDecls mark)

/-- A display-math environment, outside the knot to keep the pack small. -/
private def displayMathArm (ctx : Ctx) (numbered : Bool) (body : Array Raw) (pos : Pos)
    (blocks : Array Block) : EM (Array Block) := do
  let mut blocks := blocks
  let (body, qedAt) := dropQedHere body
  let (cleaned, keys, nonum, tag) ← stripMathMeta ctx body
  let inl ← elabMathInline ctx true cleaned pos
  let qed ← match qedAt with
    | some p =>
      if tag.isNone && (!numbered || nonum) then qedHereTag ctx p
      else do qedHereLost ctx (if numbered then "equation" else "displaymath") p; pure none
    | none => pure none
  if let some q := qed then
    for key in keys do
      recordLabel ctx key (← get).refTarget pos
    let content := keys.map (Ir.Inline.label ·) |>.push inl
    blocks := blocks.push (.equation q content)
  else if let some (raws, star) := tag then
    -- `\tag{t}` stands in the number's place, `(t)` unless starred, and
    -- steps no counter (amsldoc §3.4). Its argument is text set in an
    -- `\hbox` (amsmath's `\maketag@@@`), so it elaborates as inline content
    -- — markup and math are ink, never source — with the spaces at its
    -- edges dropped (`\ignorespaces…\unskip`). A label binds to the tag's
    -- text, so `\ref` sets `t` and `\eqref` `(t)`, as it would a number.
    let t ← elabInlines ctx (trimRaws raws)
    for key in keys do
      recordLabel ctx key (some { kind := some .equation, num := Ir.plainText t }) pos
    let content := keys.map (Ir.Inline.label ·) |>.push inl
    blocks := blocks.push (.equation (if star then t else tagForm t) content)
  else if numbered && !nonum then
    -- The display takes the next equation number (amsldoc §3);
    -- its labels bind to it, scoped to the environment as
    -- LaTeX's \refstepcounter group is.
    let num := (← get).ctr.eqNum + 1
    modify fun st => { st with ctr := { st.ctr with eqNum := num } }
    for key in keys do
      recordLabel ctx key (some { kind := some .equation, num := toString num }) pos
    let content := keys.map (Ir.Inline.label ·) |>.push inl
    blocks := blocks.push (.equation #[.text s!"({num})"] content)
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
  let (body, qedAt) := dropQedHere body
  if let some p := qedAt then qedHereLost ctx n p
  let (cleaned, keys, _, tag) ← stripMathMeta ctx body
  for key in keys do
    recordLabel ctx key none pos
  let inl ← elabMathEnv ctx n kind (numbered || tag.isSome) cleaned pos
  let content := keys.map (Ir.Inline.label ·) |>.push inl
  return blocks.push (.center #[.para content])

/-- **A picture inside a sentence is named where it stands.** LaTeX sets a
`tikzpicture` as a box of its line, so the sentence runs on around it; the
engine sets a picture as a block, which breaks the sentence into two
paragraphs with the picture between. The sentence is the paragraph's text
before the picture (`cur`, what the block walk holds) and after it, up to
the next paragraph break or environment; a word, a symbol or inline math
counts, a declaration or a spacing command does not. A box followed by a
picture on its own line is a row (`Compat.boxRows`), and never reaches
here. Outside the knot. -/
private def pictureInSentence (ctx : Ctx) (n : String) (cur raws : Array Raw) (i : Nat)
    (pos : Pos) : EM Unit := do
  if n != "tikzpicture" then return
  let text (r : Raw) : Bool := r matches .word _ _ || r matches .sym _ _ || r matches .math false _ _
  let after := (raws.extract (i + 1) raws.size).toList.takeWhile fun r =>
    !(r matches .par _) && !(r matches .env _ _ _)
  if cur.any text || after.any text then
    warnOnce ctx "picture:inline" .W0334
      "a picture inside a paragraph is set as its own block: the paragraph's text breaks \
at it instead of running on beside it" pos

/-- The in-sentence naming for a command whose body is a picture: expanded
at the block level (`bodyIsBlock`), the picture is set as its own block and
the sentence around the command breaks at it, exactly as a picture written
there does, so it is named the same way (`pictureInSentence`). -/
private def macroPictureInSentence (ctx : Ctx) (n : String) (cur raws : Array Raw) (i : Nat)
    (pos : Pos) : EM Unit := do
  if let some (_, cmd) := lookupUser ctx n then
    if cmd.body.any (· matches .env "tikzpicture" _ _) then
      pictureInSentence ctx "tikzpicture" cur raws i pos

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
  let (alt, body) := splitPictureAlt body pos
  let (pic, pdiags) := subsetPicture ctx body
  let pic := { pic with alt := alt }
  -- **The boundary draws what the subset would draw with a loss.** A
  -- picture the subset draws whole stays native: the engine owns that ink.
  -- One it draws nothing of, or draws with a named loss
  -- (`Picture.namesLoss`), goes to the real TikZ at the edge, so the page is
  -- LaTeX's rather than a departure the tool could have avoided (PLAN,
  -- Heavy machinery: isolate, then absorb). The subset's drawing is kept
  -- as the request's fallback, not thrown away: when fulfilment draws
  -- nothing — no tool on this machine and a cold cache, or a tool that
  -- failed — the driver withdraws the request and elaborates again with its
  -- id in `picWithdrawn` (`Cli.Boundary.withdraw`, N0419), and the drawing
  -- ships with its refusals named exactly as `\pictures{ tool = none }`
  -- names them. So a boundary failure never costs a page the subset could
  -- draw in part — the trade that once made native-first the rule.
  -- The tool is the build environment's, exactly as fonts are: the request
  -- rides the IR — content hash of the wrapped standalone source — and the
  -- driver fulfils it, cached by content, so a warm cache needs no TeX
  -- installed and a machine with none gets the driver's W0379 with the
  -- placeholder where the subset drew nothing. `\pictures{ tool = none }`
  -- is the declared refusal that keeps the subset's named diagnostics
  -- instead. The trust label: the engine claims placement and measurement
  -- of the returned box, never its contents.
  let src := Parse.rawSrc body
  let id := Ir.picHash src
  -- premise: pictureRouteChecks — a routed picture's losses are never dropped
  -- in silence: a drawn request ships the boundary's box, and a withdrawn one
  -- the refused door's drawing with the refused door's diagnostics.
  if ctx.pic.tool.isSome && !body.isEmpty &&
      (pic.shapes.isEmpty ||
        (Picture.namesLoss pdiags && !ctx.pic.withdrawn.contains id)) then
    return blocks.push (.para #[← routePicture ctx body pic pos])
  for (code, msg) in pdiags do
    -- A note names a decision, not a construct outside the subset, so the
    -- subset's reach is no help to it.
    let help : Option String := match code.loss with
      | .info => none
      | _ => some "the rendered subset is \\fill...rectangle, \\node at, \
\\foreach, and \\pgfmath(truncate)setmacro"
    warnOnce ctx ("picture:" ++ msg) code msg pos (help := help)
  -- A refused boundary (`tool = none`) keeps the subset's diagnostics and
  -- no door warning: the declaration is the acceptance. W0379 is the
  -- driver's, for a stated request no available tool can fulfil.
  unless pic.shapes.isEmpty do
    recordNativePictureSpan ctx pos
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
    recordNativePictureSpan ctx pos
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
    -- A slotted title page aligns per slot (`titleBlocks`), never as one.
    let content := if tps.align == some "left" || !tps.slots.isEmpty then inner
      else #[.center inner]
    blocks := blocks.push (.frame #[] false .golden false content)
  else
    -- The flow classes centre the title block, as `\@maketitle`
    -- does — unless the `titlepage` style declares its matter
    -- ragged left, the same declaration the slides branch reads.
    modify fun st => { st with titleDone := true }
    let tps := (ctx.styles.find? "titlepage").getD {}
    let content := if tps.align == some "left" then inner else #[.center inner]
    blocks := blocks ++ content
  return blocks

/-- **A page model nests no page: one frame never contains another.**

`\titlepage` inside an author's own `\begin{frame}` is beamer's documented
idiom and what every real deck writes, and the title arm opens a frame of its
own to carry the golden split — so the body walk produced `frame > frame`.
The PDF backend flattened that and placed the page correctly; the HTML
backend gives each frame a `section.slide` with vertical fills of its own, so
two nested slide-height containers pushed the title matter a full viewport
down and out of sight. The divergence was in neither backend: the IR should
not have carried the nesting. The inner frame's vertical distribution is the
one to keep — its `.golden` is a deliberate declaration, where the outer
frame's is whatever the page model defaults to — which is also beamer's own
arrangement, the title-page template's glue sitting inside the frame the
author opened. Breakability is either frame's to ask for.

Guarded on both titles being empty: a titled outer frame around a titled
inner one is not this shape and keeps its nesting, so the flatten cannot
silently drop a frame title. Outside the block knot, as a function of its
arguments only, so the measure machinery never sees a match on a recursive
call's result. -/
private def flattenFrame (title : Array Inline) (standout : Bool)
    (valign : Ir.VAlign) (breakable : Bool) (inner : Array Block) : Block :=
  match inner with
  | #[.frame it _ ival ibrk ibody] =>
    if title.isEmpty && it.isEmpty then
      .frame title standout ival (breakable || ibrk) ibody
    else .frame title standout valign breakable inner
  | _ => .frame title standout valign breakable inner

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
seal elabMathInline elabMathEnv applyPalette parsePaletteOpts applyTokens parseColSpec
seal titleBlocks Picture.elabPicture MathParse.parseMath
seal Decl.parseBlock Decl.parseLength Decl.parseGlue skipOptArg takeTitleDecl
seal sectionNumber columnWidth cmidRange trimRawEdges
seal recordLabel refuseRedef dropEnvArgs skipReservedArgs takeDefine
/-- Enter appendix.sty's `{appendices}` scope when `b` (the environment's
own arm shares its branch, so the flag): save the section counters and the
mark, zero the counters, set the mark (`\@resets@pp`). Outside the block
knot so the shared arm stays three lines. -/
private def enterAppendicesIf (b : Bool) : EM (Option ((Nat × Nat × Nat) × Bool)) := do
  if !b then return none
  let st ← get
  modify fun st => { st with ctr := { st.ctr with inAppendix := true, secNums := (0, 0, 0) } }
  return some (st.ctr.secNums, st.ctr.inAppendix)

/-- Leave the `{appendices}` scope: restore what `enterAppendicesIf` saved
(`\@ppsavesec`/`\@pprestoresec`), so numbering after the environment
continues where it left off. -/
private def leaveAppendices (saved : Option ((Nat × Nat × Nat) × Bool)) : EM Unit :=
  match saved with
  | none => pure ()
  | some s =>
    modify fun st => { st with ctr := { st.ctr with inAppendix := s.2, secNums := s.1 } }

/-- The node a block-sequence wrapper environment ships: `{quote}` and
`{quotation}` are one node (they differ only in `\listparindent`, which
nothing here binds to — the constructor's docstring), `{verse}` is that
node too (latex.ltx: `\list{}{\itemsep\z@ \itemindent -1.5em
\listparindent\itemindent \rightmargin\leftmargin \advance\leftmargin
1.5em}` under `\let\\\@centercr`: both margins in, each `\\` a new line at
the leading, a stanza a paragraph — what a quotation of lines sets; a line
too long for the measure wraps at the quotation's margin, where LaTeX hangs
it 1.5 em further, the one thing the node cannot say), `{abstract}` is
article's unnumbered titled block, and `{appendices}` wraps nothing — its
meaning is the numbering scope `enterAppendicesIf` carries, so its blocks
splice. One def outside the knot: the environments share one branch and
one recursion site there. -/
def wrapScopedEnv (n : String) (blocks inner : Array Block) : Array Block :=
  if n == "abstract" then blocks.push (.abstract inner)
  else if n == "appendices" then blocks ++ inner
  else blocks.push (.quote inner)

/-- The wrapper node ships exactly its body's census: `{quote}` and
`{abstract}` are body-transparent constructors (`blockTextOne` reads
straight through both) and the `{appendices}` splice is the identity, so
the shared environment arm conserves the text whatever the name. -/
theorem wrapScopedEnv_text (n : String) :
    Ir.Conserves Ir.blocksText (wrapScopedEnv n #[]) := fun inner => by
  unfold wrapScopedEnv
  split
  · rfl
  · split
    · simp
    · rfl

/-- The theorem-like environment `n` names, when a `\newtheorem` declared it. -/
private def thmOf? (thm : ThmDecls) (n : String) : Option ThmDef :=
  thm.defs.find? (·.env == n)

/-- `n` opens a theorem-like scope: an environment a `\newtheorem` declared,
or amsthm's `proof` once amsthm is loaded (amsthm.sty defines it; the kernel
does not, so without amsthm it stays unknown, as LaTeX has it). -/
def thmEnv (thm : ThmDecls) (n : String) : Bool :=
  (thmOf? thm n).isSome || (n == "proof" && thm.ams)

/-- `\labelsep`, .5 em (article.cls, `\setlength\labelsep{.5em}`): what a
list's `\item` sets between its label and the text (ltlists.dtx `\@item`,
`\hskip\labelsep` after the label box) — a description label's, the
kernel's theorem head (latex.ltx `\@begintheorem`, `\item[\hskip\labelsep
…]`) and amsthm's proof head (`\item[\hskip\labelsep\itshape …]`).
amsthm's theorem head closes with `\thm@headsep`, `5pt plus 1pt minus 1pt`
(amsthm.sty `\@thm`): the same length at a 10 pt body, 0.5 pt over at 11 pt
and 1 pt at 12 pt, its ±1 pt rubber not carried — the IR has no
fixed-length inline glue, and the en space (U+2002, `\enspace`, a kern of
half the em) stands for both. -/
def labelSep : String := "\u2002"

/-- `\@addpunct{.}` (amsthm.sty): a period after a head, unless the head
already ends in one of the punctuation marks it tests for. -/
private def addPunct (head : Array Inline) : Array Inline :=
  let t := (Ir.plainText head).trimAscii.toString
  if [".", "?", "!", ":", ";", ","].any (t.endsWith ·) then #[] else #[.text "."]

/-- The head a theorem-like environment opens with, the separator
included. The kernel's (latex.ltx `\@begintheorem`, `\@opargbegintheorem`):
name, number and `(note)`, bold. amsthm's (amsthm.sty `\thmhead@plain`,
`\@begintheorem`): name and number in the style's head font — bold, italic
under `remark` — the number `\@upn` upright, the note parenthesised in the
note font (`\fontseries\mddefault\upshape`), then the head punctuation `.`
in the head font. -/
def thmHead (style : ThmStyle) (name : Array Inline) (num : Option String)
    (note : Option (Array Inline)) : Array Inline :=
  match style with
  | .kernel =>
    let numRun : Array Inline := match num with
      | some n => #[.text (" " ++ n)]
      | none => #[]
    let noted : Array Inline := match note with
      | some nt => #[.text " ("] ++ nt ++ #[.text ")"]
      | none => #[]
    #[.styled .bold (name ++ numRun ++ noted), .text labelSep]
  | _ =>
    let font : Style := if style == .remark then .italic else .bold
    let numRun : Array Inline := match num with
      | some n => #[.text " ", .styled .upright #[.text n]]
      | none => #[]
    let noteRun : Array Inline := match note with
      | some nt => #[.text " ", .styled .medium #[.styled .upright
          (#[.text "("] ++ nt ++ #[.text ")"])]]
      | none => #[]
    #[.styled font (name ++ numRun)] ++ noteRun ++
      #[.styled font #[.text "."], .text labelSep]

/-- A theorem-like scope's state at its `\begin`: the head its first
paragraph opens with, the space its trivlist opens (`Ir.ThmSpace`), whether
a QED closes it (amsthm's `proof`) and the `\qedsymbol` its own body
redefines, and the label target and block declarations to restore at its
`\end` — `\refstepcounter` and the body font are local to the environment's
group. -/
structure ThmOpen where
  head : Array Inline
  space : Ir.ThmSpace
  qed : Bool
  qedDef : Option (Array Raw)
  /-- The enclosing proof's `qedPlaced`, restored at the `\end`. -/
  outerPlaced : Bool
  target : Option Ir.RefBinding
  decls : List Ir.Decl

/-- The `\qedsymbol` a proof's own body redefines — the manual's way to
change or omit one proof's mark (amsthdoc §5: "just before
`\end{proof}`") — read off the body's top level, where Compat spells the
redefinition `\define \qedsymbol() {…}`: the body of the last one. -/
private def bodyQedDef? (body : Array Raw) : Option (Array Raw) := Id.run do
  let mut found : Option (Array Raw) := none
  for i in [0:body.size] do
    if body[i]? matches some (.ctrl "define" _) then
      let j := skipSpaces body (i + 1)
      if body[j]? matches some (.ctrl "qedsymbol" _) then
        match (body.extract (j + 1) body.size).find? (· matches .group _ _) with
        | some (.group g _) => found := some g
        | _ => pure ()
  return found

/-- Step a theorem counter and render its number (ltthm.dtx `\newtheorem`:
`\the<counter>` is `\arabic`, after `\the<within>.` for a `[within]`
counter, which restarts whenever that heading counter moves — read here as
the heading numbers it last stepped under, the appendix mark included). -/
private def stepThmCounter (c : String) : EM String := do
  let st ← get
  let within := (st.ctr.thm.counters.find? (·.1 == c)).bind (·.2)
  let (s1, s2, s3) := st.ctr.secNums
  let mark := if st.ctr.inAppendix then "A" else ""
  let levels := match within with
    | some 1 => s!"{s1}"
    | some 2 => s!"{s1}.{s2}"
    | some _ => s!"{s1}.{s2}.{s3}"
    | none => ""
  let snap := mark ++ levels
  let v := match st.ctr.thm.nums.find? (·.1 == c) with
    | some (_, s, v) => if s == snap then v + 1 else 1
    | none => 1
  modify fun st => { st with ctr := { st.ctr with thm := { st.ctr.thm with
    nums := (st.ctr.thm.nums.filter (·.1 != c)).push (c, snap, v) } } }
  return match within with
    | some lvl => s!"{renderSecLevel st.ctr.secFmts st.ctr.secNums st.ctr.inAppendix secFmtFuel lvl}.{v}"
    | none => toString v

/-- Open a theorem-like scope: read the optional `[note]`, step the counter
and make its number the label target, push the style's body font
(`\itshape` for the kernel's and `plain`), and build the head. Returns the
index past the note, where the body starts. -/
private def thmOpen (ctx : Ctx) (n : String) (body : Array Raw) (pos : Pos) :
    EM (ThmOpen × Nat) := do
  let (note, k) ← match scanBracketArg body 0 pos with
    | .took k =>
      let j := skipSpaces body 0
      pure (some (← elabInlines ctx (body.extract (j + 1) (k - 1))), k)
    | .unclosed bpos =>
      warnUnclosed ctx s!"'\\begin\{{n}}'" bpos
      pure (none, 0)
    | .content => pure (none, 0)
  let st ← get
  let (head, italic, qed, space) ← match thmOf? st.ctr.thm n with
    | some d =>
      let num ← match d.counter with
        | some c => pure (some (← stepThmCounter c))
        | none => pure none
      if let some nm := num then
        modify fun st => { st with refTarget := some { kind := none, num := nm } }
      pure (thmHead d.style d.heading num note, d.style == .plain || d.style == .kernel, false,
        d.style.space)
    | none =>
      -- amsthm's proof: `\itshape #1\@addpunct{.}` over `\proofname`,
      -- `\labelsep`, the body `\normalfont` and a QED at its end.
      let name ← match note with
        | some nt => pure nt
        | none => definedOr ctx "proofname" pos (pure #[.text ctx.locale.proof])
      pure (#[.styled .italic (name ++ addPunct name), .text labelSep], false, true, .proof)
  if italic then
    modify fun s => { s with blockDecls := st.blockDecls ++ [.style .italic] }
  -- A proof pushes its QED (amsthm.sty `\pushQED{\qed}`): a `\qedhere` in
  -- it may set the mark.
  if qed then
    modify fun s => { s with ctr := { s.ctr with thm := { s.ctr.thm with
      proofs := s.ctr.thm.proofs + 1, qedPlaced := false } } }
  return ({ head := Ir.wrapDecls st.blockDecls head, space, qed,
            qedDef := if qed then bodyQedDef? body else none,
            outerPlaced := st.ctr.thm.qedPlaced, target := st.refTarget,
            decls := st.blockDecls }, k)

/-- Close a theorem-like scope: restore what `thmOpen` changed, open the
first paragraph with the head — or stand it alone when the body opens with
anything else — end a proof with its QED (amsthm.sty `\qed`:
`\hbox{}\nobreak\hfill\quad\hbox{\qedsymbol}` on the last line, a line of its
own after a display or list, where the empty box keeps the fill that a line's
start would otherwise drop), and set the whole as the trivlist it is
(ltthm.dtx and amsthm.sty both open `\trivlist`), in the role that names
the space its spelling opens (`Ir.thmSpaceRole`), under the environment's
name. A `\qedhere` moves the mark (amsthm.sty `\setQED@elt` empties the
stack): its text-mode run gets the mark here, and the end sets none. -/
private def thmClose (ctx : Ctx) (n : String) (o : ThmOpen) (inner : Array Block)
    (pos : Pos) : EM (Array Block) := do
  modify fun st => { st with refTarget := o.target, blockDecls := o.decls }
  let inner : Array Block := match inner[0]? with
    | some (Block.para c) => inner.modify 0 fun _ => .para (o.head ++ c)
    | _ => #[Block.para o.head] ++ inner
  let inner ← if o.qed then do
      let mark ← match o.qedDef with
        | some b => elabInlines ctx b
        | none => qedMark ctx pos
      let shown := Ir.wrapDecls o.decls mark
      let here := Ir.foldBlocks (fun a _ => a) (fun a x => a || x == .label qedHereKey) false inner
      let placed := here || (← get).ctr.thm.qedPlaced
      modify fun st => { st with ctr := { st.ctr with thm := { st.ctr.thm with
        proofs := st.ctr.thm.proofs - 1, qedPlaced := o.outerPlaced } } }
      let set : Inline := match shown with
        | #[x] => x
        | xs => .role "qedsymbol" xs
      let inner := if here then
          Ir.mapBlocks (fun x => if x == .label qedHereKey then set else x) inner
        else inner
      -- `\renewcommand{\qedsymbol}{}` is the manual's way to omit it.
      if placed || mark.isEmpty then pure inner else
      let q : Array Inline := #[.strut {}, .fill, .text "\u2003"] ++ shown
      pure (match inner.back? with
        | some (.para c) => inner.pop.push (.para (c ++ q))
        | _ => inner.push (.para q))
    else pure inner
  return #[.role (Ir.thmSpaceRole o.space) #[.role n inner]]

/-- The labels a description list's `\item`s carry, one per item in the
order `itemSplitGo` splits them: the `[...]` run after each top-level
`\item`, past an overlay spec, `none` where the item carries none. -/
private def descLabelRaws (body : Array Raw) : Array (Option (Array Raw)) := Id.run do
  let mut out := #[]
  for i in [0:body.size] do
    if body[i]? matches some (.ctrl "item" _) then
      let mut j := i + 1
      let mut label : Option (Array Raw) := none
      for _ in [0:body.size] do
        match body[j]? with
        | some .space => j := j + 1
        | some (.sym '[' _) =>
          label := (closeBracketFrom body (j + 1)).map (body.extract (j + 1) ·)
          break
        | some r => if (specWord? r).isSome then j := j + 1 else break
        | none => break
      out := out.push label
  return out

/-- A description list's items with their labels run in (latex.ltx
`\descriptionlabel`: `\hspace\labelsep\normalfont\bfseries #1`, the
`\hspace` taken back by the label box's `\hskip-\labelsep`): each label in
the description label role with `\labelsep` after it, first in the item's
first paragraph, or a paragraph of its own when the item opens with another
block. An item with no label keeps the separator, as LaTeX's empty label box
still leaves `\labelsep` before the text. -/
private def descItems (ctx : Ctx) (body : Array Raw) (items : Array (Array Block)) :
    EM (Array (Array Block)) := do
  let labels := descLabelRaws body
  let mut out := #[]
  for (item, i) in items.zipIdx do
    let label ← match labels[i]?.join with
      | some raws => elabInlines ctx raws
      | none => pure #[]
    let head : Array Inline :=
      #[.role Ir.descLabelRole #[.styled .normal #[.styled .bold label], .text labelSep]]
    out := out.push (match item[0]? with
      | some (Block.para c) => item.modify 0 fun _ => .para (head ++ c)
      | _ => #[Block.para head] ++ item)
  return out

/-- A raw run with its edge spaces and paragraph ends dropped, and a
paragraph end inside it read as a space: a `\bibitem`'s text. -/
private def entryRaws (raws : Array Raw) : Array Raw :=
  let rs := raws.map fun r => if r matches .par _ then Raw.space else r
  let a := (rs.findIdx? (· != Raw.space)).getD rs.size
  let b := rs.size - ((rs.reverse.findIdx? (· != Raw.space)).getD rs.size)
  rs.extract a b

/-- `thebibliography` (classes.dtx): an unnumbered References section, then
each `\bibitem[label]{key}` entry in source order — its key, its label as
written, and its text. The widest-label argument names the label column's
width, which the layout measures from the labels themselves; `\newblock`'s
.11 em between an entry's blocks is not set, the source's space standing. -/
private def ownBibList (ctx : Ctx) (body : Array Raw) : EM (Array Block) := do
  let j := skipSpaces body 0
  let start := if body[j]? matches some (.group _ _) then j + 1 else 0
  let mut items : Array Ir.BibItem := #[]
  let mut cur : Option (String × Option String × Array Raw) := none
  let mut i := start
  for _ in [0:body.size + 1] do
    if h : i < body.size then
      match body[i] with
      | .ctrl "bibitem" bpos =>
        if let some (k, l, raws) := cur then
          items := items.push { key := k, marker := l, content := ← elabInlines ctx (entryRaws raws) }
        let k0 := skipSpaces body (i + 1)
        let (label, k1) : Option String × Nat := match body[k0]? with
          | some (.sym '[' _) => match closeBracketFrom body (k0 + 1) with
            | some c => (some (rawSrc (body.extract (k0 + 1) c)).trimAscii.toString,
                skipSpaces body (c + 1))
            | none => (none, k0)
          | _ => (none, k0)
        match body[k1]? with
        | some (.group kb _) =>
          cur := some ((rawSrc kb).trimAscii.toString, label, #[])
          i := k1 + 1
        | _ =>
          diag ctx .E0304 "missing argument 'key' for '\\bibitem'" bpos
          cur := none
          i := k1
      | .ctrl "newblock" npos =>
        warnOnce ctx "ctrl:nothing:newblock" .N0100
          "'\\newblock' → nothing: the .11 em it adds between an entry's blocks is not set; the source's space stands" npos
        i := i + 1
      | r =>
        cur := cur.map fun (k, l, rs) => (k, l, rs.push r)
        i := i + 1
    else break
  if let some (k, l, raws) := cur then
    items := items.push { key := k, marker := l, content := ← elabInlines ctx (entryRaws raws) }
  return #[.section 1 true none #[.text ctx.locale.references], .bibliography "" none items]

seal thmOf? thmEnv thmOpen thmClose descItems ownBibList
seal enterAppendicesIf leaveAppendices wrapScopedEnv
seal secFmtDefine? secFmtOfBody applySecFmt applyCounter counterCtrl counterArm
seal theCounterLevel? String.toInt? String.toNat?
seal Ir.padTableRows Ir.setAltBlocks Ir.plainText Ir.overlayRange
seal declBlockOf isDeclBlock enterBlockDecl leaveBlockDecl declScopeWrap
seal bodyIsBlock bodyIsBlockList bodyIsBlockOne overlayTakesBlocks
seal DiagCode.ofString? Diag.of renderedBuiltins structuralNames
seal declCtrl runningCtrl titleCtrls overlayCtrls blockEnvs reservedEnv
seal displayMathEnvs alignEnvs isMathEnv sectionLevel specWord?
seal lookupUser lookupUserEnv isArgument isCenteringRaw isParRaw splitAtPars
seal isColumnStray
seal Ir.markInParagraph Ir.flushedText

-- ===== Pseudocode environments: algorithm2e and algorithmicx ============
--
-- Both surfaces parse onto the one `Ir.Block.algorithm` value: lines of
-- rich text with depth from nesting, keywords generated from the locale
-- table at the backends. algorithm2e's grammar is grouped
-- (`\For{cond}{body}`, `\;` the line terminator — algorithm2e.sty's own
-- macro definitions and the manual's block forms); algorithmicx's is flat
-- (`\For{cond}` … `\EndFor` — algorithmicx manual §2). No recursion into
-- the block walk, so the whole family lives outside the knot, as
-- `tabularArm` does.

/-- One parsed pseudocode line, still raw: elaboration to `Ir.AlgLine`
happens per segment, after the structural walk. -/
private structure AlgSeg where
  depth : Nat
  kind : Ir.AlgKind
  content : Array Raw
  comment : Option (Array Raw)

/-- The structural walk's work items: a source raw, or a virtual marker a
block form's expansion leaves behind — `close` ends a nested body
(repeat's carries its until-condition), `mid` is `\eIf`'s else at the
opener's level, `dedent` closes a `\uIf`-style block that prints no
end. -/
private inductive AlgTok where
  | raw (r : Raw)
  | close (o : Ir.AlgOpen) (cond : Array Raw)
  | mid (o : Ir.AlgOpen)
  | dedent

/-- algorithm2e's `{cond}{body}` block openers, each with its opener kind
and whether it prints an end line (`\SetKwFor`/`\SetKwIF` defaults; the
`u` forms are the if-chain links that print none). -/
private def algA2eBlocks : List (String × Ir.AlgOpen × Bool) :=
  [("For", (.forLoop, true)), ("ForEach", (.forEach, true)),
   ("ForAll", (.forEach, true)), ("While", (.whileLoop, true)),
   ("If", (.ifThen, true)), ("uIf", (.ifThen, false)),
   ("ElseIf", (.elseIf, true)), ("uElseIf", (.elseIf, false))]

/-- algorithm2e's io-line commands (`\SetKwInput` defaults). -/
private def algA2eIo : List (String × Ir.AlgIo) :=
  [("KwIn", .input), ("KwOut", .output), ("KwData", .data),
   ("KwResult", .result)]

/-- algorithm2e display settings the engine does not model, each with the
group count it consumes: named and ignored (N0102), never silent — the
engine keeps its own display (vertical block lines included, until the
layout grows a vertical-rule op). -/
private def algA2eSettings : List (String × Nat) :=
  [("SetAlgoLined", 0), ("SetAlgoNoLine", 0), ("SetAlgoVlined", 0),
   ("SetLine", 0), ("SetNoline", 0), ("SetVline", 0),
   ("SetAlgoNoEnd", 0), ("SetAlgoShortEnd", 0), ("SetAlgoLongEnd", 0),
   ("SetInd", 2), ("SetVlineSkip", 1), ("SetAlgoSkip", 1),
   ("SetAlgoInsideSkip", 1), ("RestyleAlgo", 1), ("SetAlCapSkip", 1),
   ("SetAlCapHSkip", 1), ("NoCaptionOfAlgo", 0), ("SetAlgorithmName", 3),
   ("IncMargin", 1), ("DecMargin", 1), ("SetKwSty", 1), ("SetFuncSty", 1),
   ("SetArgSty", 1), ("SetCommentSty", 1), ("SetDataSty", 1),
   ("SetProcNameSty", 1), ("SetProcArgSty", 1), ("SetTitleSty", 2),
   ("SetAlFnt", 1), ("SetAlCapFnt", 1), ("SetAlCapNameFnt", 1),
   ("BlankLine", 0), ("Indp", 0), ("Indm", 0), ("SetSideCommentLeft", 0),
   ("SetSideCommentRight", 0), ("LinesNumberedHidden", 0),
   ("SetNlSty", 3), ("SetAlgoNlRelativeSize", 1)]

/-- algorithm2e constructs outside the modeled subset, each with its
group count: W0383 names the construct and the groups' contents splice
back into the stream, so the text is kept as plain lines, never
dropped. -/
private def algA2eRefused : List (String × Nat) :=
  [("Begin", 1), ("lIf", 2), ("lElseIf", 2), ("lElse", 1), ("lFor", 2),
   ("lForEach", 2), ("lForAll", 2), ("lWhile", 2), ("lRepeat", 2),
   ("Switch", 3), ("Case", 2), ("uCase", 2), ("lCase", 2), ("Other", 1),
   ("lOther", 1), ("ForPar", 2), ("KwHData", 1), ("nlset", 1), ("nl", 0),
   ("ShowLn", 0), ("ShowLnLabel", 1)]

/-- algorithmicx's flat block openers, one `{cond}` group each. -/
private def algAcxBlocks : List (String × Ir.AlgOpen) :=
  [("For", .forLoop), ("ForAll", .forEach), ("While", .whileLoop),
   ("If", .ifThen)]

/-- algorithmicx's end commands, each naming the opener it closes (the
kind only selects the generated word: every non-repeat block ends on
`end`). -/
private def algAcxEnds : List (String × Ir.AlgOpen) :=
  [("EndFor", .forLoop), ("EndWhile", .whileLoop), ("EndIf", .ifThen),
   ("EndFunction", .function), ("EndProcedure", .procedure)]

/-- algorithmicx constructs outside the modeled subset: W0383 names each;
none carries a content group, so nothing needs keeping. -/
private def algAcxRefused : List String := ["Loop", "EndLoop"]

/-- Rewrite document-defined algorithm keywords inside content raws, so a
`\KwTo` in a `\For` condition or a `\SetKwFunction` name in a statement
reaches `elabInlines` as the styled text algorithm2e prints: a keyword
bold (`\KwSty`'s default), a function name in small caps with its `(args)`
(`\FuncSty`), a data name in sans (`\DataSty`). An io keyword met inline
renders as its bold label. Anything else passes through; groups are
rewritten inside. -/
private def algSubstList (kws : Array (String × AlgKwDef)) (out : Array Raw) :
    List Raw → Array Raw
  | [] => out
  | .group body p :: rest =>
    algSubstList kws (out.push (.group (algSubstList kws #[] body.toList) p)) rest
  | .ctrl n p :: rest =>
    match ((kws.find? (·.1 == n)).map (·.2) : Option AlgKwDef) with
    | some (.word w) =>
      -- the space TeX ate after the control word returns beside the word
      algSubstList kws
        (((out.push (.ctrl "textbf" p)).push (.group w p)).push .space) rest
    | some (.io label) =>
      algSubstList kws
        ((out.push (.ctrl "textbf" p)).push (.group #[.word (label ++ ":") p] p)) rest
    | some (.data name) =>
      algSubstList kws
        ((out.push (.ctrl "textsf" p)).push (.group name p)) rest
    | some (.func name) =>
      let out := (out.push (.ctrl "textsc" p)).push (.group name p)
      match rest with
      | .group args gp :: rest2 =>
        let out := out.push (.word "(" gp)
        let out := algSubstList kws out args.toList
        algSubstList kws (out.push (.word ")" gp)) rest2
      | other => algSubstList kws out other
    | none => algSubstList kws (out.push (.ctrl n p)) rest
  | r :: rest => algSubstList kws (out.push r) rest
termination_by l => rawWeightList l
decreasing_by all_goals first
  | (simp_all [rawWeightList, rawWeight]; omega)
  | (simp only [rawWeightList]; have := rawWeight_pos r; omega)
  | simp_all [rawWeightList, rawWeight]

/-- Flush the accumulated line, skipping an empty statement (a stray `\;`,
whitespace between structure commands); a non-statement kind always
emits — `\Return\;` is a real line. -/
private def algFlush (segs : Array AlgSeg) (depth : Nat) (kind : Ir.AlgKind)
    (cur : Array Raw) (comment : Option (Array Raw)) : Array AlgSeg :=
  if (kind matches Ir.AlgKind.statement) && cur.all isSpaceOrPar
      && comment.isNone then segs
  else segs.push { depth := depth
                   kind := kind
                   content := trimRawEdges cur
                   comment := comment }

/-- Pop the next `{...}` group off the walk's stack, skipping spaces. -/
private def algPopGroup (stack : Array AlgTok) :
    Option (Array Raw × Pos) × Array AlgTok := Id.run do
  let mut stack := stack
  for _ in [0:stack.size + 1] do
    match stack.back? with
    | some (.raw .space) => stack := stack.pop
    | some (.raw (.par _)) => stack := stack.pop
    | some (.raw (.group g gp)) => return (some (g, gp), stack.pop)
    | _ => return (none, stack)
  return (none, stack)

/-- The structural walk: one dialect flag, one bounded pass over a work
stack — a block form's body group is expanded onto the stack behind its
virtual closer, so nesting costs no recursion and the weight bound makes
the loop total. Returns the elaborated lines with the `\LinesNumbered`
and `\DontPrintSemicolon` flags met on the way. -/
private def algorithmLines (ctx : Ctx) (acx : Bool) (body : Array Raw)
    (pos : Pos) : EM (Array Ir.AlgLine × Bool × Bool) := do
  let mut kws : Array (String × AlgKwDef) := (← get).alg.kws
  -- The one built-in inline keyword (`\SetKw{KwTo}{to}`, the sty's own
  -- default); the io and block keywords are line kinds, not inline text.
  kws := kws.push ("KwTo", .word #[.word "to" pos])
  let mut stack : Array AlgTok := body.reverse.map AlgTok.raw
  let mut segs : Array AlgSeg := #[]
  let mut depth : Nat := 0
  let mut cur : Array Raw := #[]
  let mut curKind : Ir.AlgKind := .statement
  let mut curComment : Option (Array Raw) := none
  let mut numbered := (← get).alg.numbered
  let mut semis := (← get).alg.semis
  for _ in [0:2 * rawWeightList body.toList + body.size + 2] do
    match stack.back? with
    | none => break
    | some tok =>
      stack := stack.pop
      match tok with
      | .mid o =>
        segs := algFlush segs depth curKind cur curComment
        cur := #[]; curKind := .statement; curComment := none
        segs := segs.push { depth := depth - 1
                            kind := .opener o
                            content := #[]
                            comment := none }
      | .close o cond =>
        segs := algFlush segs depth curKind cur curComment
        cur := #[]; curKind := .statement; curComment := none
        depth := depth - 1
        segs := segs.push { depth := depth
                            kind := .closer o
                            content := trimRawEdges cond
                            comment := none }
      | .dedent =>
        segs := algFlush segs depth curKind cur curComment
        cur := #[]; curKind := .statement; curComment := none
        depth := depth - 1
      | .raw (.ctrl ";" _) =>
        segs := algFlush segs depth curKind cur curComment
        cur := #[]; curKind := .statement; curComment := none
      | .raw (.par _) =>
        -- a paragraph break between lines is whitespace, as in a table
        pure ()
      | .raw (.ctrl name p) =>
        if name == "SetKw" || name == "SetKwInOut" || name == "SetKwInput"
            || name == "SetKwFunction" || name == "SetKwData" then
          let (g1, st1) := algPopGroup stack
          let (g2, st2) := algPopGroup st1
          stack := st2
          match g1, g2 with
          | some (nm, _), some (val, _) =>
            let key := (Parse.rawSrc nm).trimAscii.toString
            if name == "SetKw" then kws := kws.push (key, .word val)
            else if name == "SetKwFunction" then kws := kws.push (key, .func val)
            else if name == "SetKwData" then kws := kws.push (key, .data val)
            else kws := kws.push (key, .io (Ir.plainText (← elabInlines ctx val)))
          | _, _ =>
            diag ctx .E0304 s!"'\\{name}' needs its \{name}\{text} groups" p
        else if let some (o, hasEnd) :=
            (if acx then none else algA2eBlocks.lookup name) then
          let (g1, st1) := algPopGroup stack
          let (g2, st2) := algPopGroup st1
          stack := st2
          match g1, g2 with
          | some (cond, _), some (b, _) =>
            segs := algFlush segs depth curKind cur curComment
            cur := #[]; curKind := .statement; curComment := none
            segs := segs.push { depth := depth
                                kind := .opener o
                                content := trimRawEdges cond
                                comment := none }
            depth := depth + 1
            stack := stack.push (if hasEnd then .close o #[] else .dedent)
            stack := stack ++ b.reverse.map AlgTok.raw
          | _, _ =>
            diag ctx .E0304 s!"'\\{name}' needs its \{condition}\{body} groups" p
        else if !acx && name == "eIf" then
          let (g1, st1) := algPopGroup stack
          let (g2, st2) := algPopGroup st1
          let (g3, st3) := algPopGroup st2
          stack := st3
          match g1, g2, g3 with
          | some (cond, _), some (tb, _), some (eb, _) =>
            segs := algFlush segs depth curKind cur curComment
            cur := #[]; curKind := .statement; curComment := none
            segs := segs.push { depth := depth
                                kind := .opener .ifThen
                                content := trimRawEdges cond
                                comment := none }
            depth := depth + 1
            stack := stack.push (.close .elseBranch #[])
            stack := stack ++ eb.reverse.map AlgTok.raw
            stack := stack.push (.mid .elseBranch)
            stack := stack ++ tb.reverse.map AlgTok.raw
          | _, _, _ =>
            diag ctx .E0304 "'\\eIf' needs its {condition}{then}{else} groups" p
        else if !acx && (name == "Else" || name == "uElse") then
          let (g1, st1) := algPopGroup stack
          stack := st1
          match g1 with
          | some (b, _) =>
            segs := algFlush segs depth curKind cur curComment
            cur := #[]; curKind := .statement; curComment := none
            segs := segs.push { depth := depth
                                kind := .opener .elseBranch
                                content := #[]
                                comment := none }
            depth := depth + 1
            stack := stack.push
              (if name == "Else" then .close .elseBranch #[] else .dedent)
            stack := stack ++ b.reverse.map AlgTok.raw
          | none =>
            diag ctx .E0304 s!"'\\{name}' needs its \{body} group" p
        else if !acx && name == "Repeat" then
          let (g1, st1) := algPopGroup stack
          let (g2, st2) := algPopGroup st1
          stack := st2
          match g1, g2 with
          | some (cond, _), some (b, _) =>
            segs := algFlush segs depth curKind cur curComment
            cur := #[]; curKind := .statement; curComment := none
            segs := segs.push { depth := depth
                                kind := .opener .repeatLoop
                                content := #[]
                                comment := none }
            depth := depth + 1
            stack := stack.push (.close .repeatLoop cond)
            stack := stack ++ b.reverse.map AlgTok.raw
          | _, _ =>
            diag ctx .E0304 "'\\Repeat' needs its {condition}{body} groups" p
        else if let some k :=
            (if acx then none else algA2eIo.lookup name) then
          let (g1, st1) := algPopGroup stack
          stack := st1
          match g1 with
          | some (g, _) =>
            segs := algFlush segs depth curKind cur curComment
            cur := #[]; curKind := .statement; curComment := none
            segs := segs.push { depth := depth
                                kind := .io k
                                content := trimRawEdges g
                                comment := none }
          | none =>
            diag ctx .E0304 s!"'\\{name}' needs its \{text} group" p
        else if name == "Return" || name == "KwRet" then
          segs := algFlush segs depth curKind cur curComment
          cur := #[]; curComment := none
          curKind := .ret
        else if !acx && (name == "tcc" || name == "tcp") then
          if let some (.raw (.sym '*' _)) := stack.back? then
            stack := stack.pop
          if let some (.raw (.sym '[' _)) := stack.back? then
            for _ in [0:stack.size + 1] do
              match stack.back? with
              | some (.raw (.sym ']' _)) => stack := stack.pop; break
              | some _ => stack := stack.pop
              | none => break
          let (g1, st1) := algPopGroup stack
          stack := st1
          match g1 with
          | some (c, _) =>
            if cur.all isSpaceOrPar && curComment.isNone
                && (curKind matches Ir.AlgKind.statement) then
              segs := segs.push { depth := depth
                                  kind := .statement
                                  content := #[]
                                  comment := some c }
              cur := #[]
            else
              curComment := some ((curComment.getD #[]) ++ c)
          | none =>
            diag ctx .E0304 s!"'\\{name}' needs its \{comment} group" p
        else if !acx && name == "LinesNumbered" then
          numbered := true
        else if !acx && name == "DontPrintSemicolon" then
          semis := false
        else if !acx && name == "PrintSemicolon" then
          semis := true
        else if let some k :=
            (if acx then none else algA2eSettings.lookup name) then
          warnOnce ctx ("alg:set:" ++ name) .N0102
            s!"'\\{name}' is not modelled; the algorithm keeps the \
engine's own display" p
          for _ in [0:k] do
            let (_, st1) := algPopGroup stack
            stack := st1
        else if let some k :=
            (if acx then none else algA2eRefused.lookup name) then
          warnOnce ctx ("alg:refused:" ++ name) .W0383
            s!"'\\{name}' is an algorithm construct outside the modeled \
subset; its content is kept as plain lines" p
          let mut gs : Array (Array Raw) := #[]
          for _ in [0:k] do
            match algPopGroup stack with
            | (some (g, _), st1) =>
              stack := st1
              gs := gs.push g
            | (none, st1) => stack := st1
          for i in [0:gs.size] do
            if let some g := gs[gs.size - 1 - i]? then
              stack := stack ++ g.reverse.map AlgTok.raw
        else if acx && (name == "State" || name == "Statex") then
          segs := algFlush segs depth curKind cur curComment
          cur := #[]; curKind := .statement; curComment := none
        else if let some o :=
            (if acx then algAcxBlocks.lookup name else none) then
          let (g1, st1) := algPopGroup stack
          stack := st1
          segs := algFlush segs depth curKind cur curComment
          cur := #[]; curKind := .statement; curComment := none
          segs := segs.push { depth := depth
                              kind := .opener o
                              content := trimRawEdges ((g1.map (·.1)).getD #[])
                              comment := none }
          depth := depth + 1
        else if acx && name == "ElsIf" then
          let (g1, st1) := algPopGroup stack
          stack := st1
          segs := algFlush segs depth curKind cur curComment
          cur := #[]; curKind := .statement; curComment := none
          segs := segs.push { depth := depth - 1
                              kind := .opener .elseIf
                              content := trimRawEdges ((g1.map (·.1)).getD #[])
                              comment := none }
        else if acx && name == "Else" then
          segs := algFlush segs depth curKind cur curComment
          cur := #[]; curKind := .statement; curComment := none
          segs := segs.push { depth := depth - 1
                              kind := .opener .elseBranch
                              content := #[]
                              comment := none }
        else if let some o :=
            (if acx then algAcxEnds.lookup name else none) then
          segs := algFlush segs depth curKind cur curComment
          cur := #[]; curKind := .statement; curComment := none
          depth := depth - 1
          segs := segs.push { depth := depth
                              kind := .closer o
                              content := #[]
                              comment := none }
        else if acx && name == "Repeat" then
          segs := algFlush segs depth curKind cur curComment
          cur := #[]; curKind := .statement; curComment := none
          segs := segs.push { depth := depth
                              kind := .opener .repeatLoop
                              content := #[]
                              comment := none }
          depth := depth + 1
        else if acx && name == "Until" then
          let (g1, st1) := algPopGroup stack
          stack := st1
          segs := algFlush segs depth curKind cur curComment
          cur := #[]; curKind := .statement; curComment := none
          depth := depth - 1
          segs := segs.push { depth := depth
                              kind := .closer .repeatLoop
                              content := trimRawEdges ((g1.map (·.1)).getD #[])
                              comment := none }
        else if acx && (name == "Function" || name == "Procedure") then
          let (g1, st1) := algPopGroup stack
          let (g2, st2) := algPopGroup st1
          stack := st2
          segs := algFlush segs depth curKind cur curComment
          cur := #[]; curKind := .statement; curComment := none
          let o : Ir.AlgOpen :=
            if name == "Function" then .function else .procedure
          let nm := (g1.map (·.1)).getD #[]
          let content := match g2 with
            | some (args, gp) =>
              ((#[Raw.ctrl "textsc" p, .group nm p, .word "(" gp]
                : Array Raw) ++ args).push (.word ")" gp)
            | none => #[Raw.ctrl "textsc" p, .group nm p]
          segs := segs.push { depth := depth
                              kind := .opener o
                              content := content
                              comment := none }
          depth := depth + 1
        else if acx && name == "Require" then
          segs := algFlush segs depth curKind cur curComment
          cur := #[]; curComment := none
          curKind := .io .input
        else if acx && name == "Ensure" then
          segs := algFlush segs depth curKind cur curComment
          cur := #[]; curComment := none
          curKind := .io .output
        else if acx && name == "Comment" then
          let (g1, st1) := algPopGroup stack
          stack := st1
          match g1 with
          | some (c, _) => curComment := some ((curComment.getD #[]) ++ c)
          | none => diag ctx .E0304 "'\\Comment' needs its {text} group" p
        else if acx && name == "Call" then
          let (g1, st1) := algPopGroup stack
          let (g2, st2) := algPopGroup st1
          stack := st2
          let nm := (g1.map (·.1)).getD #[]
          cur := (cur.push (Raw.ctrl "textsc" p)).push (.group nm p)
          if let some (args, gp) := g2 then
            cur := ((cur.push (.word "(" gp)) ++ args).push (.word ")" gp)
        else if acx && algAcxRefused.contains name then
          warnOnce ctx ("alg:refused:" ++ name) .W0383
            s!"'\\{name}' is an algorithm construct outside the modeled \
subset; its content is kept as plain lines" p
        else
          -- an unknown command is line content: `elabInlines` judges it
          -- (a document-defined keyword substitutes at elaboration below)
          cur := cur.push (Raw.ctrl name p)
      | .raw r =>
        cur := cur.push r
  segs := algFlush segs depth curKind cur curComment
  let mut lines : Array Ir.AlgLine := #[]
  for seg in segs do
    let content ← elabInlines ctx (algSubstList kws #[] seg.content.toList)
    let comment ← match seg.comment with
      | some c => some <$> elabInlines ctx (algSubstList kws #[] c.toList)
      | none => pure none
    lines := lines.push { depth := seg.depth
                          kind := seg.kind
                          content := content
                          comment := comment }
  return (lines, numbered, semis)

/-- The bare `{algorithmic}` arm (algorithmicx/algpseudocode): `[n]`
numbers the lines, the body parses in the flat dialect, and the node
stands alone — uncaptioned, unnumbered, exactly where written. Inside an
`{algorithm}` float the wrapper's arm takes it instead. -/
private def algorithmicArm (ctx : Ctx) (body : Array Raw) (pos : Pos)
    (blocks : Array Block) : EM (Array Block) := do
  let mut k := 0
  let mut numbered := false
  match scanBracketArg body 0 pos with
  | .took k' =>
    numbered := true
    let inner := (Parse.rawSrc (body.extract 1 (k' - 1))).trimAscii.toString
    unless inner == "1" do
      warnOnce ctx "algorithmic:step" .N0102
        s!"'[{inner}]' line-number stepping is not modelled; every line \
is numbered" pos
    k := k'
  | .unclosed bpos => warnUnclosed ctx "'\\begin{algorithmic}'" bpos
  | .content => pure ()
  let (lines, n2, semis) ←
    algorithmLines ctx true (body.extract k body.size) pos
  return blocks.push (.algorithm (numbered || n2) semis lines)

/-- The `{algorithm}`/`{algorithm2e}` arm: a float of the algorithm kind.
`[placement]` is noted and ignored (floats stand where written);
`\caption` fills the float's caption — set above the lines, algorithm2e's
own default position — and `numberFloats` assigns the number afterwards.
A nested `{algorithmic}` body parses in the flat dialect; otherwise the
body is algorithm2e's own grouped grammar. -/
private def algorithmArm (ctx : Ctx) (n : String) (body : Array Raw)
    (pos : Pos) (blocks : Array Block) : EM (Array Block) := do
  let mut k := 0
  for _ in [0:body.size] do
    match scanBracketArg body k pos with
    | .took k' =>
      warnOnce ctx ("float:placement:" ++ n) .N0102
        s!"'\{{n}}' [placement] is ignored: a single-pass engine has \
nowhere for a float to float" pos
      k := k'
    | .unclosed bpos =>
      warnUnclosed ctx s!"'\\begin\{{n}}'" bpos
      break
    | .content => break
  let mut caption : Array Inline := #[]
  let mut anchors : Array Inline := #[]
  let mut rest : Array Raw := #[]
  let mut acxBody : Option (Array Raw × Pos) := none
  let mut j := k
  for _ in [k:body.size] do
    if h : j < body.size then
      match body[j] with
      | .ctrl "label" lpos =>
        -- The float's own anchor (`\caption{…}\label{alg:…}`): it rides
        -- with the caption, never as a numbered line of pseudocode.
        let j2 := skipSpaces body (j + 1)
        match body[j2]? with
        | some (.group g _) =>
          anchors := anchors ++ (← elabInlines ctx #[.ctrl "label" lpos, .group g lpos])
          j := j2 + 1
        | _ =>
          rest := rest.push body[j]
          j := j + 1
      | .ctrl "caption" cpos =>
        let (⟨j2, _⟩, _, _) ← skipOptArg ctx "caption" body (j + 1) cpos
        let j3 := skipSpaces body j2
        match body[j3]? with
        | some (.group t _) =>
          unless caption.isEmpty do
            diag ctx .W0311
              s!"this '\\caption' replaces the {n}'s earlier caption"
              (some cpos)
              (help := "the last one wins; remove the other '\\caption'")
          caption ← elabInlines ctx t
          j := j3 + 1
        | _ =>
          diag ctx .E0304 "'\\caption' needs a {text} group" cpos
          j := j3
      | .env "algorithmic" abody apos =>
        acxBody := some (abody, apos)
        j := j + 1
      | r =>
        rest := rest.push r
        j := j + 1
    else break
  let (lines, numbered, semis) ← match acxBody with
    | some (abody, apos) =>
      let mut m := 0
      let mut numbered := false
      match scanBracketArg abody 0 apos with
      | .took m' =>
        numbered := true
        let inner := (Parse.rawSrc (abody.extract 1 (m' - 1))).trimAscii.toString
        unless inner == "1" do
          warnOnce ctx "algorithmic:step" .N0102
            s!"'[{inner}]' line-number stepping is not modelled; every \
line is numbered" apos
        m := m'
      | .unclosed bpos => warnUnclosed ctx "'\\begin{algorithmic}'" bpos
      | .content => pure ()
      let (lines, n2, semis) ←
        algorithmLines ctx true (abody.extract m abody.size) apos
      pure (lines, numbered || n2, semis)
    | none => algorithmLines ctx false rest pos
  -- Anchors bind to the float's number wherever they can: inside the
  -- caption when there is one, on the first line otherwise.
  let mut lines := lines
  if !anchors.isEmpty then
    if !caption.isEmpty then
      caption := anchors ++ caption
    else if h : 0 < lines.size then
      lines := lines.set 0 { lines[0] with content := anchors ++ lines[0].content }
    else
      lines := #[{ depth := 0
                   kind := .statement
                   content := anchors
                   comment := none }]
  let blk : Block := .algorithm numbered semis lines
  return blocks.push (.float .algorithm none true #[blk] caption)


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

/-- `\begin{frame}[options]`, read. `fragile` and `fragile=true` are
consumed silently over `fragileNoopChecks`: Beamer uses those spellings to
select its external reader, while this lexer captures the supported raw forms
before the parser collects environments. `fragile=false` is not in that class:
Beamer's environment path differs, so it remains a registered unsupported
option. Other unmodelled options are ignored with a note (plain and friends say
how beamer should cope, not what to say), except `standout`, which says what the
frame IS, `allowframebreaks`, which declares that content taller than one page
continues (beamer user guide §8.1; the layout's spill account reads it), and
`t`/`c`/`b`, which say how the frame distributes its leftover vertical space
(`c` is beamer's default). Outside the elaboration knot on purpose: its loop
state is what pushed the knot's compile over the heartbeat wall. -/
structure FrameOpts where
  standout : Bool := false
  breakable : Bool := false
  valign : VAlign := .center
  /-- The index past the last bracket group read. -/
  next : Nat := 0

private def frameOpts (ctx : Ctx) (body : Array Raw) (pos : Pos) : EM FrameOpts := do
  let mut o : FrameOpts := {}
  for _ in [0:body.size] do
    let j0 := skipSpaces body o.next
    match scanBracketArg body o.next pos with
    | .took k' =>
      let inner := rawSrc (body.extract (j0 + 1) (k' - 1))
      for opt in (inner.splitOn ",").map (·.trimAscii.toString) do
        match opt with
        -- premise: fragileNoopChecks — over Beamer-accepted external-reader
        -- inputs, diagnostics and both artifacts agree for exactly these spellings.
        | "fragile" | "fragile=true" => pure ()
        | "standout" => o := { o with standout := true }
        | "allowframebreaks" => o := { o with breakable := true }
        | "t" => o := { o with valign := .top }
        | "c" => o := { o with valign := .center }
        | "b" => o := { o with valign := .bottom }
        | other =>
          -- plain and friends say how beamer should cope, not what to
          -- say: registered, never silent.
          unless other.isEmpty do
            warnOnce ctx ("frame:opt:" ++ other) .N0102
              s!"frame option '{other}' is not modelled; ignored" pos
      o := { o with next := k' }
    | .unclosed bpos =>
      warnUnclosed ctx "'\\begin{frame}'" bpos
      break
    | .content => break
  return o

/-- A box's optional arguments from the start of `body`: `[pos]`
(`boxPosOf`), then `[height]` and `[inner-pos]`, which size and fill a box
the engine sets at its content's height, named once per box kind. The
position and the index past the brackets. Outside the knot, as `tikzArm`
is, so the environment arms stay inside the elaboration budget. -/
private def boxOptsArm (ctx : Ctx) (body : Array Raw) (pos : Pos) (what : String) :
    EM (Ir.BoxPos × Nat) := do
  let mut k := 0
  let mut boxPos : Ir.BoxPos := .top
  for arg in [0:3] do
    match scanBracketArg body k pos with
    | .took k' =>
      match (if arg == 0 then boxPosOf (bracketSrc body k k') else none) with
      | some p => boxPos := p
      | none =>
        warnOnce ctx ("box:" ++ what ++ ":options") .N0102
          s!"'\{{what}}' [height] and [inner-pos] options are ignored: the box is as tall as its content" pos
      k := k'
    | .unclosed bpos =>
      warnUnclosed ctx s!"'\\begin\{{what}}'" bpos
      break
    | .content => break
  return (boxPos, k)

/-- beamer's `\begin{columns}[...]`: `t`/`c`/`b`/`T` is the point each column
stands on the row's baseline by unless a `{column}` declares its own
(`Ir.BoxPos`, carried to the columns by `Compat.columnsRowPos`); any other
option is named. The index past the brackets. Outside the knot. -/
private def columnsOptsArm (ctx : Ctx) (body : Array Raw) (pos : Pos) : EM Nat := do
  let mut k := 0
  for _ in [0:body.size] do
    match scanBracketArg body k pos with
    | .took k' =>
      for o in (bracketSrc body k k').splitOn "," do
        let o := o.trimAscii.toString
        if (boxPosOf o).isNone && !o.isEmpty then
            warnOnce ctx ("columns:option:" ++ o) .N0102
              s!"'columns' option '{o}' is not modelled; ignored" pos
      k := k'
    | .unclosed bpos =>
      warnUnclosed ctx "'\\begin{columns}'" bpos
      break
    | .content => break
  return k

/-- beamer's `\begin{column}[pos]{width}`: the point it stands on the row's
baseline by, and where its width group may stand. A row's own `[pos]`
reaches a column that declares none through the raws
(`Compat.columnsRowPos`), so this reads the column alone. -/
private def columnPosOf (cbody : Array Raw) (cpos : Pos) : Ir.BoxPos × Nat :=
  match scanBracketArg cbody 0 cpos with
  | .took k' => ((boxPosOf (bracketSrc cbody 0 k')).getD .top, skipSpaces cbody k')
  | _ => (.top, skipSpaces cbody 0)

/-- The flow-state declarations a block list reads between blocks: each
changes the state from here forward and places nothing (the `\appendix`
scope model). The language switch, block form; appendixnumberbeamer's
restart (`Compat.frameRestartMark`), which records the index the next block
takes, where the frame count starts over as its `\appendix` sets
`framenumber` to 0; and `\appendix` itself, not a heading but a declaration
affecting every heading after it — the counter restarts and level-1 numbers
letter. Outside the elaboration knot on purpose, as `FrameOpts` is: the knot
asks once and recurses once, and its compile budget is spent. -/
private def flowDecl? (ctx : Ctx) (n : String) (next : Nat) : Option (ESt → ESt) :=
  if n.startsWith "@lang:" then some (flowLangUpdate ctx n)
  else if n == Compat.frameRestartMark then
    some fun st => { st with frameRestart := st.frameRestart <|> some next }
  else if n == "appendix" then
    some fun st => { st with ctr := { st.ctr with inAppendix := true, secNums := (0, 0, 0) } }
  else none

/-- The page-model marks a control word stands for between blocks: the
declared boundary `\pagebreak` names, `\vspace*`'s anchor
(`Compat.vspaceAnchorMark`, which no document spells) and
`\nointerlineskip`. Outside the elaboration knot, as `flowDecl?` is: one
arm inside reads the three. -/
private def pageMark? (n : String) : Option Block :=
  if n == "pagebreak" then some .pagebreak
  else if n == Compat.vspaceAnchorMark then some (.role Ir.pageAnchorRole #[])
  else if n == "nointerlineskip" then some (.role Ir.noInterlineRole #[])
  else none

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
  set saved.freshReport
  let ⟨checkCtx, hm⟩ : MCtx ctx ← pure ⟨{ ctx with
    args := cmd.params.map fun p => (p.name, some #[Inline.text "x"])
    atUse := true },
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
    -- A refused size command may still declare its step (`\@setfontsize`):
    -- stashed for the preamble's-end read-out, the title-body shape.
    if sizeCtrlNames.contains cmd.name && cmd.name != "normalsize" then
      modify fun st => { st with refusedSizeBodies :=
        st.refusedSizeBodies.push (cmd.name, cmd.body, cmd.span) }
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
    (cols : Array (BoxWidth × Array Block)) (rest : Array Raw)
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
            pure (innerBlocks ++ rb, (#[] : Array (BoxWidth × Array Block)))
          else pure (innerBlocks, cols)
        -- The minipage shape: `[pos]` is the point the box stands on its
        -- row's baseline by (`Ir.BoxPos`); `[height]` and `[inner-pos]` are
        -- noted, since the box takes its content's height. The `{width}`
        -- group is a fraction of the measure, exactly as a column's.
        let (subPos, m0) ← boxOptsArm ctx sbody spos sn
        let mut m := m0
        m := skipSpaces sbody m
        let mut width : Ir.BoxWidth := .share
        if let some (.group wRaws _) := sbody[m]? then
          m := m + 1
          let src := rawSrc wRaws
          let read := columnWidth ctx src
          width := read.getD .share
          if read.isNone then
            warnOnce ctx ("env:subfigure-width:" ++ sn ++ ":" ++ src) .W0314
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
          (cols.push ({ width with pos := subPos }, #[.float .sub none sCapAbove sInner sCaption]))
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
    (cols : Array (BoxWidth × Array Block)) (strayRaws : Array Raw)
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
        if strayRaws.any isColumnStray then do
          let blocks := if cols.isEmpty then blocks
            else blocks.push (.columns cols)
          have hs0 : sliceWeight strayRaws 0
              = rawWeightList strayRaws.toList := sliceWeight_zero _
          have hs1 : slicePars strayRaws 0
              = nestedParsList strayRaws.toList := slicePars_zero _
          let sb ← elabBlocksGo ctx strayRaws 0 #[] #[] (← get).flowGen
          pure ((#[] : Array (BoxWidth × Array Block)), blocks ++ sb)
        else pure (cols, blocks)
      -- beamer's `\begin{column}[pos]{width}`: its own point on the row's
      -- baseline, else the row's.
      let (colPos, m) := columnPosOf cbody cpos
      let mut width : Ir.BoxWidth := .share
      let mut m2 := m
      if let some (.group wRaws _) := cbody[m]? then
        m2 := m + 1
        let src := rawSrc wRaws
        let read := columnWidth ctx src
        width := read.getD .share
        if read.isNone then
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
      columnsGo ctx body (j + 1) (cols.push ({ width with pos := colPos }, cinner)) #[]
        blocks
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
    if strayRaws.any isColumnStray then
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
  else if n == "titlepage" then
    -- article.cls defines titlepage as an isolated page with the empty page
    -- style. Its body supplies any vertical glue, so the page-opening path
    -- declares the top distribution and otherwise elaborates it unchanged.
    let inner ← elabBlocksGo ctx body 0 #[] #[] (← get).flowGen
    blocks := blocks.push (.frame #[] false .top false inner)
  else if n == "tabular" || n == "tabular*" || n == "tabularx" then
    blocks ← tabularArm ctx n body pos blocks
  else if n == "thebibliography" then
    blocks := blocks ++ (← ownBibList ctx body)
  else if n == "frame" then
    -- \begin{frame}[options]{title}: the options are `frameOpts`'; the
    -- title group counts only when it follows directly — a paragraph
    -- break before a group makes it content, which is where LaTeX's
    -- own argument scanning stops looking too.
    let opts ← frameOpts ctx body pos
    let standout := opts.standout
    let breakable := opts.breakable
    let valign := opts.valign
    let mut k := skipSpaces body opts.next
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
    -- **A page model nests no page.** `\titlepage` inside an author's own
    -- `\begin{frame}` is beamer's documented idiom and what every real deck
    -- writes, and the title arm opens a frame of its own for the golden
    -- split — so the body walk produced `frame > frame`. The PDF flattened
    -- that (one page, correctly placed); the HTML backend gives each frame a
    -- `section.slide` with its own vertical fills, so the title matter was
    -- pushed a full slide-height down and off the viewport. The divergence
    -- was in neither backend: an `Ir.Block.frame` must not contain one, and
    -- the only producer of a titleless inner frame is the title arm, whose
    -- `.golden` distribution is the one to keep — as in beamer, where the
    -- title-page template's glue sits inside the frame the author opened.
    blocks := blocks.push (flattenFrame title standout valign breakable inner)
  else if n == "itemize" || n == "enumerate" || n == "description" then
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
    let ⟨(items, steps, itemPauses), hsplit⟩ ← itemSplitGo ctx lbody pos
      (n == "description") 0
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
    let elabItems ← if n == "description" then descItems ctx lbody elabItems
      else pure elabItems
    blocks := blocks.push (.list (n == "enumerate") elabItems)
  else if n == "center" || (Ir.raggedSideOf? n).isSome then
    let inner ← elabBlocksGo ctx body 0 #[] #[] (← get).flowGen
    -- The environment is a trivlist and opens `\topsep` around its scope;
    -- the `\centering`/`\raggedright` declarations open the same scope and
    -- no space, so the environment's rides in the engine's trivlist role.
    blocks := blocks.push (.role Ir.trivlistRole #[match Ir.raggedSideOf? n with
      | some side => .ragged side inner
      | none => .center inner])
  else if n == "minipage" then
    -- A minipage is one column of declared width: the column model
    -- reused whole, never a parallel box model. LaTeX's signature
    -- is [pos][height][inner-pos]{width} (classes.dtx §minipage):
    -- `[pos]` is the point the box stands on its row's baseline by
    -- (`Ir.BoxPos`), carried; `[height]` and `[inner-pos]` size and fill
    -- a box the engine sets at its content's height, so they are noted.
    -- An absolute width is the same loss a column has (W0314).
    let (boxPos, k) ← boxOptsArm ctx body pos "minipage"
    let m := skipSpaces body k
    let mut width : Ir.BoxWidth := .share
    let mut m2 := m
    if let some (.group wRaws _) := body[m]? then
      m2 := m + 1
      let src := rawSrc wRaws
      let read := columnWidth ctx src
      width := read.getD .share
      if read.isNone then
        warnOnce ctx "env:minipage-width" .W0314
          s!"minipage width '{src}' does not read as a length or a fraction of \
the text width; the box takes the whole measure" pos
          (help := "write a length like {60pt} or a factor like {0.5\\textwidth}")
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
      (.columns #[({ width with pos := boxPos }, ← elabBlocksGo ctx (body.extract m2 body.size) 0
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
  else if thmEnv (← get).ctr.thm n then
    -- A theorem-like environment (ltthm.dtx, amsthm.sty): the head, the
    -- counter, the label target and the body font are the scope's own,
    -- opened and closed outside the knot; the body recurses here.
    let (o, k) ← thmOpen ctx n body pos
    have hxw : rawWeightList (body.extract k body.size).toList
        ≤ rawWeightList body.toList := extract_weight_le ..
    have hxp : nestedParsList (body.extract k body.size).toList
        ≤ nestedParsList body.toList := extract_nested_le ..
    have hx0 : sliceWeight (body.extract k body.size) 0
        = rawWeightList (body.extract k body.size).toList := sliceWeight_zero _
    have hx1 : slicePars (body.extract k body.size) 0
        = nestedParsList (body.extract k body.size).toList := slicePars_zero _
    let inner ← elabBlocksGo ctx (body.extract k body.size) 0 #[] #[] (← get).flowGen
    blocks := blocks ++ (← thmClose ctx n o inner pos)
  else if n == "quote" || n == "quotation" || n == "verse" || n == "abstract"
      || n == "appendices" then
    -- Three same-shaped block-sequence wrappers, one branch and one
    -- recursion site (the knot compiles as one LCNF unit; a branch per
    -- wrapper is what its budget cannot afford): the node each ships is
    -- `wrapScopedEnv`'s, and `{appendices}`'s meaning is the numbering
    -- scope — appendix.sty's `\appendix` scoped to the body, counters
    -- restored at `\end` (see `enterAppendicesIf`).
    let saved ← enterAppendicesIf (n == "appendices")
    let inner ← elabBlocksGo ctx body 0 #[] #[] (← get).flowGen
    leaveAppendices saved
    blocks := wrapScopedEnv n blocks inner
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
        warnOnce ctx ("float:placement:" ++ n) .N0102
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
  else if n == "algorithm" || n == "algorithm*" || n == "algorithm2e" then
    blocks ← algorithmArm ctx n body pos blocks
  else if n == "algorithmic" then
    blocks ← algorithmicArm ctx body pos blocks
  else if n == "columns" then
    -- beamer's `[t]`/`[c]`/`[b]`/`[T]` is the point each column stands on
    -- the row's baseline by, unless a `{column}` declares its own
    -- (`Ir.BoxPos`); an undeclared row stands its columns top-aligned
    -- where beamer centres them. A column's width is its first group, a
    -- fraction of the text width; content standing outside any column
    -- keeps its place as ordinary blocks — never dropped.
    let k ← columnsOptsArm ctx body pos
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
  else if ["href", "link", "hyperlink", "hypertarget"].contains n then
    let j := skipSpaces raws (i + 1)
    have hjge := skipSpaces_ge raws (i + 1)
    let j2 := skipSpaces raws (j + 1)
    have hj2ge := skipSpaces_ge raws (j + 1)
    match hj : raws[j]?, hj2 : raws[j2]? with
    | some (.group targetRaw _), some (.group body _) =>
      have hj2lt := getElem?_lt hj2
      have hbw : rawWeightList body.toList + 1 ≤ sliceWeight raws j2 := by
        have := elem_weight_le hj2 (Nat.le_refl j2)
        simp only [rawWeight] at this
        omega
      have hbp : nestedParsList body.toList ≤ slicePars raws j2 := by
        have := elem_pars_le hj2 (Nat.le_refl j2)
        simp only [nestedPars] at this
        exact Nat.le_trans (nestedParsList_le body.toList) this
      have hb2 : sliceWeight raws j2 ≤ sliceWeight raws i :=
        sliceWeight_le raws (by omega)
      have hb3 : slicePars raws j2 ≤ slicePars raws i :=
        slicePars_le raws (by omega)
      have hb0 : sliceWeight body 0 = rawWeightList body.toList := sliceWeight_zero _
      have hb1 : slicePars body 0 = nestedParsList body.toList := slicePars_zero _
      let inner ← elabBlocksGo ctx body 0 #[] #[] (← get).flowGen
      let target := argText ctx targetRaw
      let wrapped :=
        if n == "hypertarget" then #[Block.para #[.label target]] ++ inner
        else
          let anchor := Ir.labelAnchor target
          let url := if n == "hyperlink" then "#".append anchor else target
          Ir.linkBlocks url inner
      return (blocks ++ wrapped, ⟨j2 + 1, by omega⟩)
    | _, _ =>
      diag ctx .E0304 s!"'\\{n}' needs a \{target}\{content}" pos
      return (blocks, ⟨i + 1, by omega⟩)
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
        match Ir.overlayRange w with
        | some p => pure ⟨(some p, jg), h2⟩
        | none => do
          warnOverlaySpec ctx w pos
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
          blocks := blocks.push
            (if Ir.stepPending s last 1 then .alt s last ib ia else .alt s last ia ib)
          return (blocks, ⟨j3 + 1, by omega⟩)
        | none =>
          -- One reading at block level too: an unnumberable spec keeps the
          -- active alternative on every step, never a second copy beside
          -- it. W0105 accounts for the group that is not inked; it is the
          -- one already fired for the spec when there was one to read.
          warnAltSpec ctx pos
          blocks := blocks ++ (← elabBlocksGo ctx ga 0 #[] #[] (← get).flowGen)
          return (blocks, ⟨j3 + 1, by omega⟩)
      | _, _ =>
        diag ctx .E0304 "'\\alt' needs <spec>{content}{content}" pos
          (help := "'\\alt<2>{on step 2}{on the others}' takes a spec and TWO \
braced groups: the second is what every other step shows, so give it even \
when it is empty — '{}'")
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
      warnOnce ctx ("section:short:" ++ n) .N0103
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
      else if (body.any isCenteringRaw || bodyIsBlock body) && !isArgument cur then
        -- A scope group carrying a `\centering` declaration, or holding
        -- block content — a list, a table, a heading, a display — is a
        -- block scope: a group scopes declarations and nothing else
        -- (TeXbook ch. 5), so the blocks inside stay blocks and a
        -- declaration reaches exactly to the group's edge. An argument
        -- group is the command's, as in the par splice above; its own
        -- block sequence, so the declaration stops at the closing brace.
        let blocks ← flushPara ctx' blocks cur
        let inner ← elabBlocksGo ctx' body 0 #[] #[] (← get).flowGen
        elabBlocksGo ctx' raws (i + 1) (blocks ++ inner) #[] gen'
      else
        elabBlocksGo ctx' raws (i + 1) blocks (cur.push raws[i]) gen'
    | .par _ =>
      let blocks ← flushPara ctx' blocks cur
      elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
    | .verb env s vpos =>
      if env == "verb" then
        elabBlocksGo ctx' raws (i + 1) blocks (cur.push raws[i]) gen'
      else
      let blocks ← flushPara ctx' blocks cur
      let b ← listingBlock ctx' env s vpos
      elabBlocksGo ctx' raws (i + 1) (blocks.push b) #[] gen'
    | .math display body mpos =>
      if display then
        -- A display formula is amsmath's `equation*` (amsmath.sty:
        -- `\DeclareRobustCommand{\[}{\begin{equation*}}`), so it takes that
        -- environment's one arm: unnumbered, a label binding to the flow's
        -- last number, and a `\tag` standing in the number's place.
        let blocks ← flushPara ctx' blocks cur
        let blocks ← displayMathArm ctx' false body mpos blocks
        elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
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
      let thmS := (← get).ctr.thm
      let isB : Bool :=
        if (Parse.inputEnvFile? n).isSome then bodyIsBlock body
        else
          blockEnvs.contains n || isMathEnv n
            || n == "tabular" || n == "tabular*"
            || n == "algorithm" || n == "algorithm*" || n == "algorithm2e"
            || n == "algorithmic"
            || reservedEnv.contains n
            || thmEnv thmS n
            || (match lookupUserEnv ctx' n with
                | some (_, env) =>
                  bodyIsBlock env.beginBody || bodyIsBlock env.endBody
                | none => false)
            || bodyIsBlock body
      if isB then
        pictureInSentence ctx' n cur raws i epos
        let k := blocks.size
        let flushed ← flushPara ctx' blocks cur
        let inPar := Ir.flushedText k flushed
        let blocks ← elabEnvArm ctx' n body epos flushed
        -- A list or quote opened inside an open paragraph (no blank line
        -- before it) rides in the in-paragraph role: `\@trivlist` finds
        -- horizontal mode there and adds no `\partopsep`.
        elabBlocksGo ctx' raws (i + 1) (Ir.markInParagraph inPar flushed.size blocks) #[] gen'
      else
        elabBlocksGo ctx' raws (i + 1) blocks (cur.push raws[i]) gen'
    | .ctrl n cpos =>
      -- A page-ground command in horizontal mode changes shipout state,
      -- not paragraph structure. Consume it without flushing `cur`, and
      -- elaborate the whole open paragraph under the last state that will
      -- paint its page.
      if !cur.isEmpty &&
          (n.startsWith Compat.pageColorMarkPrefix || n == Compat.pageColorResetMark) then
        let pal? ← if n.startsWith Compat.pageColorMarkPrefix then
            pageGroundDecl ctx' n cpos
          else
            pure (some (ctx'.palette.restore ctx'.basePalette "bg"))
        match pal? with
        | some pal => modify fun st =>
          { st with flowPalette := some pal, flowGen := st.flowGen + 1 }
        | none => pure ()
        let ⟨palCtx, hm⟩ : MCtx ctx' ←
          pure ⟨{ ctx' with palette := pal?.getD ctx'.palette }, rfl, rfl, rfl, rfl⟩
        have ht1 : sliceWeight raws (i + 1) < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        have ht2 : slicePars raws (i + 1) ≤ slicePars raws i :=
          slicePars_le raws (by omega)
        return ← elabBlocksGo palCtx raws (i + 1)
          (match pal? with
            | some pal => blocks.push (.setPalette pal)
            | none => blocks) cur ((← get).flowGen)
      let isB : Bool :=
        n == "par" || n == "block" || n == "centering" || n == "pause"
          || (Ir.raggedSideOf? n).isSome
          || n == "framefoot" || n == "pagebreak" || n == "appendix"
          || n == Compat.frameRestartMark || n == Compat.vspaceAnchorMark
          -- `\prevdepth` is vertical mode's: TeX refuses it mid-paragraph.
          || (n == "nointerlineskip" && cur.isEmpty)
          || n == "bibliography" || n == "bibliographystyle" || n == "@natbib"
          || (n == "note" && cur.isEmpty)
          -- A declaration met between blocks scopes the rest of the group,
          -- as `\centering` does (the arm below); mid-paragraph it keeps
          -- the inline reading.
          || isDeclBlock ctx' n raws i cur
          -- `\color{n}`'s block form: a flow ink declaration (the arm
          -- below). Mid-paragraph the marker keeps the inline reading —
          -- splitting the paragraph there would move text.
          || (cur.isEmpty && n.startsWith "@ink:")
          || (cur.isEmpty && n.startsWith Compat.pageColorMarkPrefix)
          || (cur.isEmpty && n == Compat.pageColorResetMark)
          || (cur.isEmpty && n.startsWith "@lang:")
          || (["href", "link", "hyperlink", "hypertarget"].contains n &&
            contentWrapperTakesBlocks raws i)
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
      macroPictureInSentence ctx' n cur raws i cpos
      let blocks ← flushPara ctx' blocks cur
      if n == "par" then
        elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else if n == "centering" || (Ir.raggedSideOf? n).isSome
          || isDeclBlock ctx' n raws i cur then
        -- The declaration form of \begin{center} / \begin{flushleft}
        -- (ltmiscen.dtx: flushleft is a trivlist under \raggedright, and
        -- \raggedright is the same declaration bare): the rest of this
        -- scope centres, or sets ragged left. Text flushed just above
        -- stays unaligned — LaTeX would re-align the whole broken
        -- paragraph; this engine aligns from the declaration on. The
        -- style and colour declarations met between blocks take the same
        -- rest-of-scope reading, pushed onto the scope's leaves
        -- (`Ir.styleBlocks`, `Ir.decl_between_blocks_covers`), so a table
        -- or list standing next receives them and no empty styled
        -- paragraph is set in the declaration's place. One arm for the
        -- family: the elabBlocks termination burden is per recursive
        -- call, and the wrapper (`declScopeWrap`) and the state
        -- (`enterBlockDecl`) are the only differences.
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
        let saved ← enterBlockDecl ctx' n raws i cur cpos
        let inner ← elabBlocksGo ctx' (raws.extract (i + 1) raws.size) 0
          #[] #[] (← get).flowGen
        leaveBlockDecl saved
        let blocks := blocks ++ declScopeWrap n inner
        have hend : sliceWeight raws raws.size = 0 :=
          sliceWeight_end raws (Nat.le_refl _)
        have hendp : slicePars raws raws.size = 0 :=
          slicePars_end raws (Nat.le_refl _)
        elabBlocksGo ctx' raws raws.size blocks #[] gen'
      else if let some f := flowDecl? ctx' n blocks.size then
        modify f
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
      else if n.startsWith Compat.pageColorMarkPrefix then
        let pal? ← pageGroundDecl ctx' n cpos
        let ⟨palCtx, hm⟩ : MCtx ctx' ←
          pure ⟨{ ctx' with palette := pal?.getD ctx'.palette }, rfl, rfl, rfl, rfl⟩
        match pal? with
        | some pal => modify fun st =>
          { st with flowPalette := some pal, flowGen := st.flowGen + 1 }
        | none => pure ()
        have ht1 : sliceWeight raws (i + 1) < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        have ht2 : slicePars raws (i + 1) ≤ slicePars raws i :=
          slicePars_le raws (by omega)
        elabBlocksGo palCtx raws (i + 1)
          (match pal? with
            | some pal => blocks.push (.setPalette pal)
            | none => blocks) #[] ((← get).flowGen)
      else if n == Compat.pageColorResetMark then
        -- A reset is an epoch, not a textual colour: restore the opening
        -- document/class ground and preserve every other body declaration.
        let pal := ctx'.palette.restore ctx'.basePalette "bg"
        modify fun st => { st with flowPalette := some pal
                                   flowGen := st.flowGen + 1 }
        let ⟨palCtx, hm⟩ : MCtx ctx' ←
          pure ⟨{ ctx' with palette := pal }, rfl, rfl, rfl, rfl⟩
        have ht1 : sliceWeight raws (i + 1) < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        have ht2 : slicePars raws (i + 1) ≤ slicePars raws i :=
          slicePars_le raws (by omega)
        elabBlocksGo palCtx raws (i + 1) (blocks.push (.setPalette pal)) #[]
          ((← get).flowGen)
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
            let (decorative, skipBlock) ← parsePaletteOpts ctx' (rawSrc opt) cpos
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
      else if n == "bibliographystyle" || n == "@natbib" then
        -- The declared style rides the state to the `\bibliography`
        -- marker; resolution reads it from the block (W0353 there names
        -- an unknown one). natbib's marker carries its declarations, one
        -- word each (`Compat.natbibLoad`), to the document.
        let ⟨j, hjge⟩ : { x : Nat // i + 1 ≤ x } ←
          pure ⟨skipSpaces raws (i + 1), skipSpaces_ge raws (i + 1)⟩
        match raws[j]? with
        | some (.group body _) =>
          modify fun st => if n == "@natbib" then
              { st with natbib := some ((st.natbib.getD #[]) ++ body.filterMap fun r =>
                  match r with
                  | .word w _ => some w
                  | _ => none) }
            else { st with bibStyle := some (rawSrc body).trimAscii.toString }
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
          recordBibSpan ctx' src cpos
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
      else if let some mark := pageMark? n then
        -- A page-model mark: the declared boundary (adjacent boundaries
        -- never make a blank page — the page builder closes only pages that
        -- hold something), `\vspace*`'s anchor, `\nointerlineskip`.
        elabBlocksGo ctx' raws (i + 1) (blocks.push mark) #[] gen'
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
            (blocks.push (.spaced (Ir.Sourced.bare before) inner)) #[] gen'
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
unseal elabMathInline elabMathEnv applyPalette parsePaletteOpts applyTokens parseColSpec
unseal titleBlocks Picture.elabPicture MathParse.parseMath
unseal Decl.parseBlock Decl.parseLength Decl.parseGlue skipOptArg takeTitleDecl
unseal sectionNumber columnWidth cmidRange trimRawEdges
unseal recordLabel refuseRedef dropEnvArgs skipReservedArgs takeDefine
unseal secFmtDefine? secFmtOfBody applySecFmt applyCounter counterCtrl counterArm
unseal theCounterLevel? String.toInt? String.toNat?
unseal Ir.padTableRows Ir.setAltBlocks Ir.plainText Ir.overlayRange
unseal declBlockOf isDeclBlock enterBlockDecl leaveBlockDecl declScopeWrap
unseal bodyIsBlock bodyIsBlockList bodyIsBlockOne overlayTakesBlocks
unseal DiagCode.ofString? Diag.of renderedBuiltins structuralNames
unseal declCtrl runningCtrl titleCtrls overlayCtrls blockEnvs reservedEnv
unseal displayMathEnvs alignEnvs isMathEnv sectionLevel specWord?
unseal lookupUser lookupUserEnv isArgument isCenteringRaw isParRaw splitAtPars
unseal isColumnStray
unseal Ir.markInParagraph Ir.flushedText
unseal scanBracketArg Parse.inputEnvFile?
unseal enterAppendicesIf leaveAppendices wrapScopedEnv
unseal thmOf? thmEnv thmOpen thmClose descItems ownBibList

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
    (pos : Pos) (tokens : Array (String × SymGlue) := #[]) : PageSpec × Array PEvent := Id.run do
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
    -- `size` names a paper (`a4`) or a slides stage by its ratio
    -- (`16:9`, or beamer's bare digits, which arrive as an int) — one
    -- vocabulary; the ratio spellings are `Ir.slidesStages`'s rows.
    | "size", .ident name =>
      match (pageSizes.lookup name.toLower).orElse
          (fun _ => Ir.slidesStageNamed name) with
      | some (w, h) => spec := { spec with width := w, height := h }
      | none =>
        evs := say evs .E0324 s!"unknown page size '{name}'"
          (help := s!"known sizes: {String.intercalate ", "
            (pageSizes.map (·.1) ++ (Ir.slidesStages.map (·.1)).toList)}")
    | "size", .int n =>
      match Ir.slidesStageNamed (toString n) with
      | some (w, h) => spec := { spec with width := w, height := h }
      | none =>
        evs := say evs .E0324 s!"unknown page size '{n}'"
          (help := s!"known sizes: {String.intercalate ", "
            (pageSizes.map (·.1) ++ (Ir.slidesStages.map (·.1)).toList)}")
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
    -- Printer's cut marks, a declared feature of the page: `cut` draws
    -- the eight derived hairlines (`Layout.cutMarks`), `none` is the
    -- default — a shop that wants only the declared boxes gets only
    -- boxes. The marks need a bleed to stand in: they occupy the strip
    -- the cutter discards, `mark-gap` short of the trim.
    | "marks", .ident v =>
      match v with
      | "cut" => spec := { spec with marks := true }
      | "none" | "off" => spec := { spec with marks := false }
      | _ =>
        evs := say evs .E0323 s!"'marks' in '\\page' expects 'cut' or 'none', got '{v}'"
    | "mark-gap", v =>
      if let some d := asDim v then spec := { spec with markGap := d }
      else evs := evs.push (.say (Decl.wrongType ctx.file "page" "mark-gap" "a dimension" v pos))
    | "mark-thickness", v =>
      if let some d := asDim v then spec := { spec with markThickness := d }
      else
        evs := evs.push
          (.say (Decl.wrongType ctx.file "page" "mark-thickness" "a dimension" v pos))
    -- A rule drawn on every page, as a shipout picture draws it
    -- (`Ir.DrawnRule`): `"x; y; w; h; colour"`, the lower-left corner from
    -- the page's top-left with y up, as the kernel's picture reads it. The
    -- box is stored y down from the medium's top-left corner.
    | "rule", .str s =>
      match s.splitOn ";" |>.map (·.trimAscii.toString) with
      | [x, y, w, h, c] =>
        match [x, y, w, h].map fun p => (Decl.parseValue p tokens).bind asDim with
        | [some x, some y, some w, some h] =>
          spec := { spec with drawn := spec.drawn.push ⟨x, -(y + h), w, h, c⟩ }
        | _ => evs := say evs .E0323 s!"'rule' in '\\page' expects four dimensions, got '{s}'"
      | _ =>
        let msg := s!"'rule' in '\\page' expects \"x; y; width; height; colour\", got '{s}'"
        evs := say evs .E0323 msg
    -- The page's trim is the one its drawn cut marks cut (`Ir.PageSpec.trimMarked`).
    | "trim", .ident v =>
      match v with
      | "marks" => spec := { spec with trimMarked := true }
      | _ => evs := say evs .E0323 s!"'trim' in '\\page' expects 'marks', got '{v}'"
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
    -- Margin line numbers: a declared page feature (the obligation-table
    -- rule), lineno's \linenumbers natively. `modulo` beside it prints
    -- only multiples while counting every line, lineno's
    -- \modulolinenumbers[n].
    | "linenumbers", .ident v =>
      match v with
      | "on" | "true" => spec := { spec with linenumbers := some true }
      | "off" | "false" => spec := { spec with linenumbers := some false }
      | _ =>
        evs := say evs .E0323 s!"'linenumbers' in '\\page' expects on or off, got '{v}'"
    | "modulo", .int n =>
      if n ≥ 1 then spec := { spec with lineModulo := some n.toNat }
      else evs := say evs .E0323 "'modulo' in '\\page' expects a count of at least 1"
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
    -- The page's bottom: `\flushbottom` sets a page the page builder broke
    -- flush with the text area's floor, `\raggedbottom` keeps its glue.
    | "bottom", .ident v =>
      match v with
      | "flush" => spec := { spec with flushBottom := some true }
      | "ragged" => spec := { spec with flushBottom := some false }
      | _ =>
        evs := say evs .E0323 s!"'bottom' in '\\page' expects flush or ragged, got '{v}'"
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
          else if key == "marks" then "'cut' or 'none'"
          else if key == "modulo" then "a count of at least 1"
          else if key == "bottom" then "'flush' or 'ragged'"
          else if key == "hyphenate" || key == "justify" || key == "protrusion"
            || key == "expansion" || key == "numbers"
            || key == "linenumbers" then "on or off"
          else "a dimension"
        evs := evs.push (.say (Decl.wrongType ctx.file "page" key expected v pos))
      else
        -- The help names the native surface; `headsep`/`footskip` stay
        -- accepted as the LaTeX spellings of `furnituregap` (read through
        -- the baseline-to-ink correction), `textwidth`/`textheight`
        -- as geometry's spellings of the block size the native
        -- width/height + margin surface already covers, and the
        -- `mark-gap`/`mark-thickness` riders are learned from `marks`,
        -- the key that owns them — accepted, not advertised beside it.
        -- `modulo` only qualifies `linenumbers` (named beside it in the
        -- lineno translation notes), so it too is accepted without a
        -- listing of its own; `bottom` is `\flushbottom`'s and
        -- `\raggedbottom`'s, which name it in their translation notes.
        evs := evs.push (.say (Decl.unknownKey ctx.file "page" key
          (pageKeys.filter
            (!["headsep", "footskip", "textwidth", "textheight",
               "mark-gap", "mark-thickness", "modulo", "rule", "trim", "bottom"].contains ·)) pos))
    -- Every failing arm above records a diagnostic, so a clean count means
    -- the entry applied: record it, and warn if it overwrote (W0343). A
    -- `rule` adds a drawing rather than setting a value, so a second one
    -- overwrites nothing.
    if evs.size == before && e.key != "rule" then
      evs := evs.push (.scalar "page" e.key (renderValue e.value) pos)
  return (spec, evs)

private def fontSlot? (name : String) : Option Nat :=
  match name with
  | "body" | "rm" => some 0
  | "sans" | "sf" => some 1
  | "mono" | "tt" => some 2
  | _ => none

/-- `body.bold`-style keys: `(slot, weight, italic)`. The four LaTeX-shaped
spellings name the standard corners of the axis; a series code
(`body.l`, `sans.sb.italic`) names any other weight — the native surface
fontspec's `FontFace={series}{shape}{font}` rewrites into. -/
private def fontVariantKey? (key : String) : Option (Nat × Nat × Bool) :=
  let seriesKey (s : String) (italic : Bool) : Option (Nat × Bool) :=
    match Ir.Weight.parseSeries s with
    -- A width half names an axis the engine does not have; a key that
    -- asks for one is unknown rather than quietly weight-only.
    | some (w, "") => some (w.css, italic)
    | _ => none
  match key.splitOn "." with
  | [slotName, variant] => do
    let slot ← fontSlot? slotName
    match variant with
    | "upright" => some (slot, 400, false)
    | "bold" => some (slot, 700, false)
    | "italic" => some (slot, 400, true)
    | "bolditalic" => some (slot, 700, true)
    | s => (seriesKey s false).map fun (w, i) => (slot, w, i)
  | [slotName, series, "italic"] => do
    let slot ← fontSlot? slotName
    (seriesKey series true).map fun (w, i) => (slot, w, i)
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
            (fontKeys ++ ["<slot>.upright/.bold/.italic/.bolditalic",
              "<slot>.<series>[.italic] (series ul/el/l/sl/m/sb/b/eb/ub)"]) pos))
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
  ["font", "before", "after", "rule", "rule-position", "rule-thickness", "marker", "indent", "gap",
   "align", "separator", "rule-above", "rule-above-skip", "rule-above-gap",
   "rule-below", "rule-below-gap", "rule-below-skip", "author-font",
   "author-strut", "body-size", "hover", "focus", "motion", "slot"]

/-- The keys of one `slot = {...}` group in `\style{titlepage}`. A
slot owns its box; repeated `part` entries own independently styled data.
The legacy part keys remain accepted and translate to one or more parts. -/
def titleSlotKeys : List String :=
  ["part", "set", "content", "font", "align", "width", "size", "anchor", "at",
   "xshift", "yshift", "inner-sep"]

/-- The keys of one independently styled part in a title slot. -/
def titlePartKeys : List String :=
  ["set", "content", "font", "align", "size", "leading", "new-line", "before"]

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
list levels: itemize2..4, enumerate2..4")
    return styles
  let mut st : ElementStyle := (styles.find? element).getD {}
  -- The two value readers, over any source text: an entry's own value, or
  -- one sub-entry of a `slot = {...}` group, read through the same door.
  let inlineOf (src : String) : EM (Option (Array Inline)) := do
    let inner := if src.startsWith "{" && src.endsWith "}" && src.length ≥ 2
      then (src.drop 1).dropEnd 1 |>.toString else src
    let (toks, _) := Lex.lex ctx.file inner
    let (raws, _) := Parse.parse ctx.file toks
    -- Value text re-enters through the same door as the document, idiom
    -- translation included, or a \color inside a font spec would leak.
    -- Seeded with the document's warn-once keys (one set, `Compat.rewrite`
    -- carries why) but not merged back: this site discards the notes the
    -- rewrite produced, so a key it fired may stand for a diagnostic the
    -- document never received, and recording it would silence the later
    -- visible one.
    let (raws, ds, _) := Compat.rewrite ctx.file raws (warned := (← get).warnedUnknown)
    modify fun st => { st with diags := st.diags ++ ds.filter (·.severity != .note) }
    return some (← elabInlines ctx raws)
  let lengthOf (key src : String) : EM (Option SymGlue) := do
    -- The engine's own page lengths read here as in any length the
    -- document writes (`0.6\paperwidth`, a template node's measure): the
    -- expression grammar spells tokens bare, so the backslash is dropped,
    -- as `imageLenOf` drops it.
    let expr := fun (_ : Unit) =>
      match Decl.parseLengthExpr (ctx.tokens.entries ++ ctx.engineTokens)
          (String.join (src.splitOn "\\")) with
      | .ok g => some g
      | .error _ => none
    match Decl.parseValue src ctx.tokens.entries with
    | some (.glue g) => return some g
    | some (.dim d) => return some { width := Dim.Length.ofSp d }
    | _ =>
      if let some g := expr () then return some g
      diag ctx .E0321 s!"cannot read length for '{key}' in '\\style': {src.quote}" pos
        (help := "lengths look like 10pt, 1.5ex, or a token name")
      return none
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | none =>
      diag ctx .E0320 s!"invalid entry in '\\style': {entry.quote}" pos
        (help := "entries look like: key = value")
    | some (key, valueSrc) =>
      -- premise: titleHeadingChecks — no site reads these keys on the title page: both artifacts ship the same page with and without each
      if element == "titlepage" && Ir.titleUnreadKeys.contains key then
        warnOnce ctx ("style:titlepage:" ++ key) .W0104
          s!"'{key}' has no meaning on the title page; the title is set without it" pos
          (help := "draw rules around the title with rule-above, rule-below or separator")
      let asInline : EM (Option (Array Inline)) := inlineOf valueSrc
      let asLength : EM (Option SymGlue) := lengthOf key valueSrc
      -- Every colour-valued style key uses the same typed source resolver
      -- as palette declarations and inline colour commands.
      let asColor : EM (Option (Ir.Color × Option String)) := do
        match ← readColor ctx ctx.palette none valueSrc pos with
        | .resolved c token => return some (c, token)
        | .rejected => return none
        | .missing =>
          diag ctx .E0326 s!"'{valueSrc}' is not in the palette" pos
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
      | "body-size" =>
        let v := valueSrc.trimAscii.toString
        let v := if v.startsWith "\\" then (v.drop 1).toString else v
        if sizeCtrlNames.contains v then st := { st with bodySize := some v }
        else
          diag ctx .E0323 s!"'body-size' in '\\style' expects a size name, got '{v}'" pos
            (help := "sizes: tiny, scriptsize, footnotesize, small, normalsize, large, Large")
      | "rule" =>
        if let some v ← asColor then st := { st with rule := some v }
      | "rule-thickness" => st := { st with ruleThickness := ← asLength }
      | "rule-position" =>
        match valueSrc.trimAscii.toString with
        | "baseline" => st := { st with rulePosition := some .baseline }
        | "xheight" => st := { st with rulePosition := some .xHeight }
        | v =>
          diag ctx .E0323 s!"'rule-position' in '\\style' expects baseline or xheight, got '{v}'" pos
      | "separator" =>
        -- `none` is a declaration too: a title page whose own template draws
        -- no rule (a theme's `title page` replaces the lineage's separator
        -- along with the rest of the page).
        if valueSrc.trimAscii.toString == "none" then st := { st with separator := none }
        else if let some v ← asColor then st := { st with separator := some v }
      | "slot" =>
        if element != "titlepage" then
          diag ctx .E0323 s!"'slot' in '\\style' belongs to the title page, not '{element}'" pos
            (help := "write \\style{titlepage}{ slot = { set = title, anchor = west, at = west } }")
        else
          let unbrace (src : String) : String :=
            if src.startsWith "{" && src.endsWith "}" && src.length ≥ 2
            then (src.drop 1).dropEnd 1 |>.toString else src
          let partOf (src : String) : EM (Option Ir.TitlePart) := do
            let mut p : Ir.TitlePart := { datum := none }
            let mut ok := true
            let mut hasDatum := false
            let mut hasContent := false
            for sub in Decl.splitEntries (unbrace src) do
              match Decl.splitEntry sub with
              | none =>
                ok := false
                diag ctx .E0320 s!"invalid entry in a title part: {sub.quote}" pos
                  (help := "entries look like: key = value")
              | some (k, v) =>
                let vt := v.trimAscii.toString
                match k with
                | "set" =>
                  match Ir.TitleDatum.ofName? vt with
                  | some d =>
                    p := { p with datum := some d }
                    hasDatum := true
                  | none =>
                    ok := false
                    diag ctx .E0323 s!"'set' in a title part expects title, subtitle, author, \
institute, or date, got '{vt}'" pos
                | "content" =>
                  p := { p with content := (← inlineOf v).getD #[] }
                  hasContent := true
                | "font" => p := { p with font := ← inlineOf v }
                | "align" =>
                  if vt == "left" || vt == "center" || vt == "right" then
                    p := { p with align := some vt }
                  else
                    ok := false
                    diag ctx .E0323
                      s!"'align' in a title part expects left, center, or right, got '{vt}'" pos
                | "size" => p := { p with size := ← lengthOf "size" v }
                | "leading" => p := { p with leading := ← lengthOf "leading" v }
                | "new-line" =>
                  if vt == "true" then p := { p with newLine := true }
                  else if vt == "false" then p := { p with newLine := false }
                  else
                    ok := false
                    diag ctx .E0323
                      s!"'new-line' in a title part expects true or false, got '{vt}'" pos
                | "before" => p := { p with before := ← lengthOf "before" v }
                | _ =>
                  modify fun st' => { st' with
                    diags := st'.diags.push
                      (Decl.unknownKey ctx.file "title part" k titlePartKeys pos) }
            if hasDatum && hasContent then
              ok := false
              diag ctx .E0323 "a title part cannot declare both 'set' and 'content'" pos
            return if ok then some p else none
          let inner := unbrace valueSrc
          let mut parts : Array Ir.TitlePart := #[]
          let mut legacyData : Array (Bool × Ir.TitleDatum) := #[]
          let mut legacyContent : Array Inline := #[]
          let mut legacyFont : Option (Array Inline) := none
          let mut legacyAlign : Option String := none
          let mut legacySize : Option SymGlue := none
          let mut legacySeen := false
          let mut width : Option SymGlue := none
          let mut anchor : Option Ir.BoxPoint := none
          let mut pagePoint : Option Ir.BoxPoint := none
          let mut xshift : Option SymGlue := none
          let mut yshift : Option SymGlue := none
          let mut innerSep : Option SymGlue := none
          let mut ok := true
          for sub in Decl.splitEntries inner do
            match Decl.splitEntry sub with
            | none =>
              ok := false
              diag ctx .E0320 s!"invalid entry in a title slot: {sub.quote}" pos
                (help := "entries look like: key = value")
            | some (k, v) =>
              let vt := v.trimAscii.toString
              let point (what : String) : EM (Option Ir.BoxPoint) := do
                match Ir.BoxPoint.ofName? vt with
                | some p => return some p
                | none =>
                  diag ctx .E0323 s!"'{what}' in a title slot expects a compass point \
such as north west, got '{vt}'" pos
                  return none
              match k with
              | "part" =>
                match ← partOf v with
                | some p => parts := parts.push p
                | none => ok := false
              | "set" =>
                legacySeen := true
                let pieces := (vt.splitOn "\\\\").map fun p =>
                  (p.splitOn " ").filter (!·.isEmpty)
                let names : List (Bool × String) := (pieces.zipIdx.map fun (ws, k) =>
                  ws.zipIdx.map fun (w, j) => (k > 0 && j == 0, w)).flatten
                match names.mapM fun (own, w) => (Ir.TitleDatum.ofName? w).map (own, ·) with
                | some ds@(_ :: _) => legacyData := ds.toArray
                | _ =>
                  ok := false
                  diag ctx .E0323 s!"'set' in a title slot expects title, subtitle, author, \
institute, or date, got '{vt}'" pos
              | "content" =>
                legacySeen := true
                legacyContent := (← inlineOf v).getD #[]
              | "font" =>
                legacySeen := true
                legacyFont := ← inlineOf v
              | "align" =>
                legacySeen := true
                if vt == "left" || vt == "center" || vt == "right" then
                  legacyAlign := some vt
                else
                  ok := false
                  diag ctx .E0323
                    s!"'align' in a title slot expects left, center, or right, got '{vt}'" pos
              | "width" => width := ← lengthOf "width" v
              | "size" =>
                legacySeen := true
                legacySize := ← lengthOf "size" v
              | "anchor" => anchor := (← point "anchor") <|> anchor
              | "at" => pagePoint := (← point "at") <|> pagePoint
              | "xshift" => xshift := ← lengthOf "xshift" v
              | "yshift" => yshift := ← lengthOf "yshift" v
              | "inner-sep" => innerSep := ← lengthOf "inner-sep" v
              | _ =>
                modify fun st' => { st' with
                  diags := st'.diags.push (Decl.unknownKey ctx.file "slot" k titleSlotKeys pos) }
          if legacySeen && !parts.isEmpty then
            ok := false
            diag ctx .E0323 "a title slot cannot mix 'part' entries with legacy part keys" pos
          let legacyParts : Array Ir.TitlePart :=
            if legacyData.isEmpty then
              if legacySeen then
                #[{ datum := none, content := legacyContent, font := legacyFont,
                    align := legacyAlign, size := legacySize }]
              else #[]
            else legacyData.map fun (newLine, datum) =>
              { datum := some datum, font := legacyFont, align := legacyAlign,
                size := legacySize, newLine := newLine }
          let place : Option Ir.TitlePlace :=
            if anchor.isNone && pagePoint.isNone then none
            else some { anchor := anchor.getD .center, pagePoint := pagePoint.getD .center
                        xshift := xshift, yshift := yshift, innerSep := innerSep }
          if ok then
            let slot := Ir.TitleSlot.ofNodeParts
              (if parts.isEmpty then legacyParts else parts) width place
            st := { st with slots := st.slots.push slot }
      | "align" =>
        match valueSrc.trimAscii.toString with
        | "left" => st := { st with align := some "left" }
        | "center" => st := { st with align := some "center" }
        | "right" => st := { st with align := some "right" }
        | v =>
          diag ctx .E0323 s!"'align' in '\\style' expects left, center, or right, got '{v}'" pos
      | "hover" =>
        if let some v ← asColor then st := { st with hover := some v }
      | "focus" =>
        if let some v ← asColor then st := { st with focus := some v }
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

/-- The two bare comma lists `\output` takes; an entry without `=`
continues whichever was last opened. -/
private inductive OutputList where
  | formats
  | profiles

/-- `\output{...}`: what to build, so a document needs no CLI options.
`formats` and `profiles` take bare comma lists (`formats = pdf, html`,
`profiles = pdf/a-4, pdf/ua-2`), so entries are walked by hand: an entry
without `=` continues the open list. -/
private def applyOutput (ctx : Ctx) (o0 : OutputSpec) (src : String) (pos : Pos) :
    OutputSpec × Array PEvent := Id.run do
  let mut o := o0
  let mut evs : Array PEvent := #[]
  let mut inList : Option OutputList := none
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
  -- A profile name is checked against the registered table, the `formats`
  -- pattern: an unknown name is refused naming the registered ones and
  -- never enters the set.
  let addProfile (o : OutputSpec) (evs : Array PEvent) (p : String) :
      OutputSpec × Array PEvent :=
    if PdfContract.Profile.names.contains p then
      (o.addProfile p, evs)
    else
      (o, say evs .E0321 s!"'{p}' is not a conformance profile"
        (help := s!"profiles: {String.intercalate ", " PdfContract.Profile.names}"))
  let addListed (o : OutputSpec) (evs : Array PEvent) (l : OutputList) (v : String) :
      OutputSpec × Array PEvent :=
    match l with
    | .formats => addFormat o evs v
    | .profiles => addProfile o evs v
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | some ("formats", v) =>
      inList := some .formats
      let (o', evs') := addFormat o evs v
      o := o'
      evs := evs'
    | some ("profiles", v) =>
      inList := some .profiles
      let (o', evs') := addProfile o evs v
      o := o'
      evs := evs'
    | some ("css", v) =>
      inList := none
      if ["own", "bulma", "none"].contains v then
        o := { o with css := some v }
        evs := evs.push (.scalar "output" "css" v pos)
      else
        evs := say evs .E0321 s!"'{v}' is not a stylesheet mode"
          (help := "css: own, bulma, none")
    | some ("stylesheet", v) =>
      inList := none
      -- A path is a string; the quotes other declarations require are
      -- accepted but not demanded, as `formats` entries are bare too.
      let v := if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then
          String.ofList (v.toList.drop 1).dropLast
        else v
      o := { o with stylesheet := some v }
      evs := evs.push (.scalar "output" "stylesheet" v pos)
    | some ("md", v) =>
      inList := none
      let v := if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then
          String.ofList (v.toList.drop 1).dropLast
        else v
      o := { o with md := some v }
      evs := evs.push (.scalar "output" "md" v pos)
    -- The contract keys: each a closed enumeration, last wins, and each
    -- an apply site the commutation oracle sees through its event.
    | some ("alternatives", v) =>
      inList := none
      let pol : Option AltPolicy := match v with
        | "judged" => some .judged
        | "required" => some .required
        | _ => none
      match pol with
      | some p =>
        o := { o with contract := { o.contract with alternatives := p } }
        evs := evs.push (.scalar "output" "alternatives" v pos)
      | none =>
        evs := say evs .E0321 s!"'{v}' is not an alternatives policy"
          (help := "alternatives: judged, required")
    | some ("color", v) =>
      inList := none
      let intent : Option ColorIntent := match v with
        | "device" => some .device
        | "srgb" => some .srgb
        | _ => none
      match intent with
      | some c =>
        o := { o with contract := { o.contract with color := c } }
        evs := evs.push (.scalar "output" "color" v pos)
      | none =>
        evs := say evs .E0321 s!"'{v}' is not a colour intent"
          (help := "color: device, srgb")
    | some ("fonts", v) =>
      inList := none
      let pol : Option FontPolicy := match v with
        | "embedded" => some .embedded
        | "none" => some .none
        | _ => none
      match pol with
      | some p =>
        o := { o with contract := { o.contract with fonts := some p } }
        evs := evs.push (.scalar "output" "fonts" v pos)
      | none =>
        evs := say evs .E0321 s!"'{v}' is not a font policy"
          (help := "fonts: embedded, none")
    | some (key, _) =>
      inList := none
      evs := evs.push (.say (Decl.unknownKey ctx.file "output" key
        (["formats", "profiles", "css", "stylesheet", "md"] ++ OutputContract.facts) pos))
    | none =>
      match inList with
      | some l =>
        let (o', evs') := addListed o evs l entry
        o := o'
        evs := evs'
      | none =>
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
    | "version", .str s =>
      if s == "1.7" || s == "2.0" then m := { m with pdfVersion := some s }
      else
        evs := evs.push (.say (diagOf ctx .E0323
          s!"'version' in '\\pdfmeta' expects \"1.7\" or \"2.0\", got '{s}'" (some pos) none))
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
  | ["accessibility", "=", "AA"] =>
    (some { kind := .accessibilityAA, span := some ⟨ctx.file, pos⟩
            help := some ("each failing fact is also a warning above, " ++
              "naming its pair and its fix; a deliberate exception is " ++
              "declared where the warning says, never defaulted") }, #[])
  | ["text.xheight", ">=", v] =>
    match Decl.parseValue v with
    | some (.dim d) => (some { kind := .minXHeight d, span := some ⟨ctx.file, pos⟩ }, #[])
    | _ => fail s!"'{v}' is not a dimension (like 1.4mm)"
  | ["pages", op, n] =>
    match cmpOp op, n.toInt? with
    | some o, some v => (some { kind := .pages o v, span := some ⟨ctx.file, pos⟩ }, #[])
    | none, _ => fail s!"'{op}' is not a comparison (== != <= < >= >)"
    | _, none => fail s!"'{n}' is not a whole number"
  | _ => fail "supported forms: pages <op> N, fonts.all_embedded, text.in_area, text.xheight >= <len>, accessibility = AA"

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
  | pictures (src : Option String) (pos : Pos)
  | defineCmd (decl : Array Raw) (pos : Pos)
  | defineEnv (name : Option (String × Pos)) (sig : String)
      (beginB : Option (Array Raw)) (endB : Option (Array Raw)) (pos : Pos)
  | fileMark (f : String)
  | running (name : String) (opts : Option (Array Raw))
      (body : Option (Array Raw)) (pos : Pos)
  | logo (body : Option (Array Raw)) (pos : Pos)
  /-- `\logoleft`/`\logoright` (the gemini poster lineage's commands):
  one piece of inline content each, the headline band's corner slots. -/
  | logoSlot (left : Bool) (body : Option (Array Raw)) (pos : Pos)
  | palette (opts : Option (Array Raw)) (body : Option String) (pos : Pos)
  /-- A preamble page-ground selection, resolved where it stands. `none`
  is `\nopagecolor`; a concrete source is `\pagecolor`. -/
  | pageGround (source : Option String) (pos : Pos)
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
  | captionsetup (scope : Option String) (unclosed : Option Pos) (body : Option String) (pos : Pos)
  /-- url.sty's `\urlstyle`: the family `\url`/`\nolinkurl` set in. Legal in
  the preamble, where url.sty documents it, and in the body, where the inline
  arm reads it. -/
  | urlstyle (v : Option String) (pos : Pos)
  /-- A declaration written in the preamble proper that is in force where
  the body begins: Compat's `\color` marker, which LaTeX's
  `\begin{document}` keeps (measured against lualatex). It is the body's
  first declaration, the reading a `\begin{document}` hook body gets. -/
  | bodyStart (marker : String) (pos : Pos)
  | titleDecl (name : String) (unclosed : Option Pos) (recovered : Bool)
      (body : Option (Array Raw)) (pos : Pos)
  | reserved (name : String) (code : DiagCode) (unclosed : Option Pos) (pos : Pos)
  | unknownCmd (name : String) (unclosed : Option Pos) (pos : Pos)
  /-- `\SetKw` and family in the preamble: a document-global algorithm
  keyword (algorithm2e §10.3), carried whole so the io label's accents
  still elaborate. -/
  | algKw (name : String) (args : Option (Array Raw × Array Raw)) (pos : Pos)
  /-- `\DontPrintSemicolon`/`\LinesNumbered` in the preamble: the
  document-wide display default every algorithm starts from. -/
  | algFlag (name : String) (pos : Pos)
  /-- An algorithm2e display setting outside the model, met in the
  preamble: named and ignored, its groups consumed with it. -/
  | algSetting (name : String) (pos : Pos)
  /-- `\newtheorem{env}[shared]{heading}[within]` (latex.ltx, ltthm.dtx),
  amsthm's starred form unnumbered: the environment, the counter it
  shares, its heading, and the heading counter that resets its own. -/
  | newtheorem (star : Bool) (env : String) (shared : Option String)
      (heading : Option (Array Raw)) (within : Option String) (pos : Pos)
  /-- amsthm's `\theoremstyle{s}`: the style the `\newtheorem`s after it
  take. -/
  | theoremstyle (name : Option String) (pos : Pos)
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
  /-- A `\pagecolor` already resolved in preamble order. It overlays the
  eventual class/document palette without becoming that reset target. -/
  pageGround : Option Color := none
  tokens : Tokens := {}
  /-- Caption positions `\captionsetup` declared (`Doc.captionPos`). -/
  captionPos : Array (String × Ir.CaptionPos) := #[]
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

/-- An optional `[...]` run at `j`: its contents and the index past it —
`closeBracketFrom` doing the collection the preamble scanners below used
to hand-roll. An unclosed run reaches the end of the preamble. -/
private def takeOptRun (preamble : Array Raw) (j : Nat) :
    Option (Array Raw) × Nat :=
  if preamble[j]? matches some (.sym '[' _) then
    match closeBracketFrom preamble (j + 1) with
    | some c => (some (preamble.extract (j + 1) c), c + 1)
    | none => (some (preamble.extract (j + 1) preamble.size), preamble.size)
  else (none, j)

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
        let (optRun, j1) := takeOptRun preamble (skipSpaces preamble i)
        let options : Option String := optRun.map rawSrc
        let j := skipSpaces preamble j1
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
          -- environ's spelling (`\NewEnviron`, which Compat gives the
          -- native head and marks): one code body with `\BODY` at its top
          -- level is the begin code before it — the mark closing it, the
          -- body's edges trimmed — and the end code after it; a code with
          -- none is all end code, its body discarded at each use. The final
          -- code joins the end, environ's `\ignorespacesafterend` where
          -- none follows. Unmarked, the head is the kernel's, and a `\BODY`
          -- in it the document's own macro.
          let isMark (r : Raw) : Bool := match r with
            | .ctrl n _ => n == Compat.environBodyMark
            | _ => false
          let environ := sigRaws.any isMark
          sigRaws := sigRaws.filter (!isMark ·)
          match beginRaws, environ with
          | some code, true =>
            let fb := skipSpaces preamble k
            let (final, kf) : Option (Array Raw) × Nat := match preamble[fb]? with
              | some (.sym '[' _) =>
                match closeBracketFrom preamble (fb + 1) with
                | some c => (some (preamble.extract (fb + 1) c), c + 1)
                | none => (none, k)
              | _ => (none, k)
            let (bb, ee) := match Compat.bodySlot? code with
              | some (bb, ee) => (bb.push (.ctrl Compat.environBodyMark pos), ee)
              | none => (#[], code)
            i := kf
            out := out.push (.defineEnv (some (envName, npos)) (rawSrc sigRaws)
              (some bb) (some (ee ++ final.getD #[.ctrl "ignorespacesafterend" pos])) pos)
          | _, _ =>
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
        else if name.startsWith "@series:" || name.startsWith "@lang:" then
          -- premise: compatMarkerChecks — the Doc is the one without it, `\enquote` included
          -- Compat's markers for `\fontseries` and `\selectlanguage`, met in
          -- the preamble proper. LaTeX's `\begin{document}` selects the
          -- normal font and babel's main language (measured against
          -- lualatex), so neither reaches text there. Compat discards both
          -- there itself, with a `ctrl:nothing:` note and no marker, so this
          -- arm drops only what a note already names as nothing. Never an
          -- unknown command: the marker is Compat's own spelling, and a
          -- warning quoting it named nothing the document wrote.
          pure ()
        else if name.startsWith Compat.pageColorMarkPrefix then
          out := out.push (.pageGround
            (some (name.drop Compat.pageColorMarkPrefix.length).toString) pos)
        else if name == Compat.pageColorResetMark then
          out := out.push (.pageGround none pos)
        else if name.startsWith "@ink:" then
          -- An ink declaration survives `document`; page-ground markers
          -- are applied above in preamble order instead.
          out := out.push (.bodyStart name pos)
        else if runningCtrl.contains name then
          let (opts, k) := takeOptRun preamble (skipSpaces preamble i)
          let j := skipSpaces preamble k
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
        else if name == "logoleft" || name == "logoright" then
          let j := skipSpaces preamble i
          match preamble[j]? with
          | some (.group body _) =>
            i := j + 1
            out := out.push (.logoSlot (name == "logoleft") (some body) pos)
          | _ =>
            out := out.push (.logoSlot (name == "logoleft") none pos)
        else if name == "palette" then
          let (opts, k) := takeOptRun preamble (skipSpaces preamble i)
          let j := skipSpaces preamble k
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
        else if name == "tikzexternalize" then
          -- TikZ's own externalization spelling (pgf manual §53): the
          -- LaTeX-shaped door to the boundary, with the pinned default
          -- tool. Its optional configuration is the external library's
          -- own business and is consumed with it.
          let (_, k) := takeOptRun preamble (skipSpaces preamble i)
          i := k
          out := out.push (.pictures (some "tool = lualatex") pos)
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
          | "pictures" => out := out.push (.pictures src pos)
          | _ => out := out.push (.pdfmeta src pos)
        else if name == "urlstyle" then
          let j := skipSpaces preamble i
          match preamble[j]? with
          | some (.group gbody _) =>
            i := j + 1
            out := out.push (.urlstyle (some ((rawSrc gbody).trimAscii.toString)) pos)
          | _ =>
            out := out.push (.urlstyle none pos)
        else if name == "captionsetup" then
          let mut j := i
          let mut unclosed : Option Pos := none
          let mut scope : Option String := none
          match scanBracketArg preamble j pos with
          | .took j' =>
            let b := skipSpaces preamble j
            scope := some (rawSrc (preamble.extract (b + 1) (j' - 1))).trimAscii.toString
            j := j'
          | .unclosed bpos => unclosed := some bpos
          | .content => pure ()
          j := skipSpaces preamble j
          match preamble[j]? with
          | some (.group gbody _) =>
            i := j + 1
            out := out.push (.captionsetup scope unclosed (some (rawSrc gbody)) pos)
          | _ =>
            out := out.push (.captionsetup scope unclosed none pos)
        else if name == "SetKw" || name == "SetKwInOut" || name == "SetKwInput"
            || name == "SetKwFunction" || name == "SetKwData" then
          let j := skipSpaces preamble i
          let j2 := skipSpaces preamble (j + 1)
          match preamble[j]?, preamble[j2]? with
          | some (.group nm _), some (.group val _) =>
            i := j2 + 1
            out := out.push (.algKw name (some (nm, val)) pos)
          | _, _ =>
            out := out.push (.algKw name none pos)
        else if name == "DontPrintSemicolon" || name == "PrintSemicolon"
            || name == "LinesNumbered" then
          out := out.push (.algFlag name pos)
        else if let some k := algA2eSettings.lookup name then
          let mut j := i
          for _ in [0:k] do
            let j2 := skipSpaces preamble j
            if let some (.group _ _) := preamble[j2]? then
              j := j2 + 1
          i := j
          out := out.push (.algSetting name pos)
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
        else if name == "newtheorem" then
          -- \newtheorem{env}[shared]{heading}[within]; amsthm's `*` form.
          let j0 := skipSpaces preamble i
          let (star, j0) := match preamble[j0]? with
            | some (.word "*" _) => (true, skipSpaces preamble (j0 + 1))
            | _ => (false, j0)
          match preamble[j0]? with
          | some (.group envRaws _) =>
            let env := (rawSrc envRaws).trimAscii.toString
            let (shared, j1) := takeOptRun preamble (skipSpaces preamble (j0 + 1))
            let j2 := skipSpaces preamble j1
            match preamble[j2]? with
            | some (.group hRaws _) =>
              let (within, j3) := takeOptRun preamble (skipSpaces preamble (j2 + 1))
              i := j3
              out := out.push (.newtheorem star env
                (shared.map fun r => (rawSrc r).trimAscii.toString) (some hRaws)
                (within.map fun r => (rawSrc r).trimAscii.toString) pos)
            | _ =>
              i := j2
              out := out.push (.newtheorem star env none none none pos)
          | _ =>
            i := j0
            out := out.push (.newtheorem star "" none none none pos)
        else if name == "theoremstyle" then
          let j := skipSpaces preamble i
          match preamble[j]? with
          | some (.group g _) =>
            i := j + 1
            out := out.push (.theoremstyle (some (rawSrc g).trimAscii.toString) pos)
          | _ =>
            out := out.push (.theoremstyle none pos)
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
prints in the build summary. A *retired* code is not an unknown one: it
answers through `DiagCode.retired` with a note (N0105) naming what reports
its loss now, because a document that names it was written against an
engine that had it — and it accepts nothing, because a successor that folds
the retired fragment into a wider diagnostic would otherwise be a blanket
the document never wrote. -/
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
      match DiagCode.retired.lookup code with
      | some (some succ) =>
        evs := evs.push (.say (diagOf ctx .N0105
          s!"'\\allow' names the retired code '{code}'; its loss is a clause of '{succ}' \
now, so this accepts nothing"
          (some pos) (help := s!"\\allow\{{succ}} accepts every '{succ}', this loss among them")
          (subject := some ("allow:" ++ code))))
      | some none =>
        evs := evs.push (.say (diagOf ctx .N0105
          s!"'\\allow' names the retired code '{code}'; the loss it named cannot occur"
          (some pos) (subject := some ("allow:" ++ code))))
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
  let pe := applyPage s.ctx s.page pb.1 pos s.tokens.entries
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
        -- the W0303 gains W0361's clause naming what survived. The body's
        -- size is always declared: a begin body that switches none leaves
        -- the body at the size in force, never at the built-in's `\small`.
        -- The refusal names what the built-in keeps: its heading text
        -- where the definition writes another, and its heading and margins
        -- where nothing of the definition's heading was read.
        let heading := if envName == "abstract" then
            beginB.bind fun b => envStyleInterpret (envStyleScanList {} b.toList)
          else none
        let est := if envName == "abstract" then
            beginB.map fun b =>
              let body := { ({} : Ir.ElementStyle) with
                bodySize := some ((envBodySizeList none b.toList).getD "normalsize") }
              Theme.styleMerge body (heading.getD {})
          else none
        let word := s.info.locale.abstract
        let written := String.intercalate " "
          ((beginB.map fun b => envHeadWords #[] false 0 b.toList).getD #[]).toList
        let replaced := if written.isEmpty || written == word then ""
          else s!"; its heading reads '{word}', not '{written}'"
        modify fun st => { st with diags := st.diags.push (Diag.of .W0303
          (match est, heading with
           | some _, some _ =>
             s!"'\{{envName}}' is built in; this definition's heading and body size style it, \
the built-in's margins, body font and vertical skips stand{replaced}"
           | some _, none =>
             s!"'\{{envName}}' is built in; of this definition only its body size is read, \
the built-in's heading and margins stand{replaced}"
           | none, _ =>
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
            userEnvs := s.ctx.userEnvs.push (envOfHalves envName params b e s.ctx.limit)
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
        logos := { st.logos with main := if content.isEmpty then none else some content } }
      return s
    | none =>
      diag s.ctx .E0304 "'\\logo' needs one group of inline content" pos
      return s
  | .logoSlot left body pos =>
    -- The gemini lineage's `\logoleft`/`\logoright`: one piece of inline
    -- content — normally an image — for the headline band's corner slot.
    -- The band itself is class furniture (`ClassRecord.headline`); a
    -- declaration a class cannot draw is dropped by name at assembly.
    let cmd := if left then "logoleft" else "logoright"
    match body with
    | some b =>
      -- The logo's image sizes read the same token environment a
      -- `\\setlength` reads (`0.2\\paperheight` names the page the class
      -- and the declarations so far have fixed).
      let ctx := { s.ctx with
        engineTokens := engineLengthTokens s.docClass s.classOptions s.page }
      let content ← elabInlines ctx b
      let v := if content.isEmpty then none else some content
      modify fun st =>
        { st with logos := if left then { st.logos with left := v } else { st.logos with right := v } }
      return s
    | none =>
      diag s.ctx .E0304 s!"'\\{cmd}' needs one group of inline content" pos
      return s
  | .palette opts body pos =>
    -- `\palette[decorative]{...}`: options read by the one door
    -- (`parsePaletteOpts`), the body arm's too.
    let (decorative, skipBlock) ← match opts with
      | some opt => parsePaletteOpts s.ctx (rawSrc opt) pos
      | none => pure (false, false)
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
      -- A style's lengths read the token environment a `\setlength` reads
      -- (`0.6\paperwidth` names the page the class has fixed so far), as
      -- the logo arm's sizes do.
      let ctx := { s.ctx with
        engineTokens := engineLengthTokens s.docClass s.classOptions s.page }
      let styles ← applyStyle ctx s.styles elem body pos
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
          (refused := some tname)
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
  | .pictures body pos =>
    match body with
    | some src =>
      -- The boundary door: which pinned tool draws pictures outside the
      -- rendered subset, or `tool = none`, the declared refusal. The
      -- boundary is open by default, so the block pins or refuses; a
      -- pinned value is drawn from `picTools`, never an arbitrary binary
      -- (the driver executes it).
      let mut s := s
      for e in Decl.splitEntries src do
        match Decl.splitEntry e with
        | some ("tool", v) =>
          let v := v.trimAscii.toString
          if v == "none" then
            s := { s with ctx := { s.ctx with pic := { s.ctx.pic with tool := none } } }
          else if picTools.contains v then
            s := { s with ctx := { s.ctx with pic := { s.ctx.pic with tool := some v } } }
          else
            diag s.ctx .E0321
              s!"cannot read a boundary tool for 'tool' in 'pictures': '{v}'" pos
              (help := "the engine runs only the tools it pins: lualatex; \
tool = none refuses the boundary")
        | some (key, _) =>
          let d := Decl.unknownKey s.ctx.file "pictures" key ["tool"] pos
          modify fun st => { st with diags := st.diags.push d }
        | none => pure ()
      return s
    | none =>
      diag s.ctx .E0304 "'\\pictures' needs a {...} block" pos
      return s
  | .pdfmeta (some src) pos => stepDone s.ctx (stepPdfmeta s src pos)
  | .pdfmeta none pos => stepDone s.ctx (stepMissing s "pdfmeta" "a {...} block" pos)
  | .urlstyle v pos =>
    -- url.sty's face selector, honoured rather than refused: the four
    -- values it defines map onto the engine's three families and the
    -- running face. Refusing it was wrong twice — it told a reader who
    -- asked for the running face that URLs are set mono, and the slot
    -- census then counted such a URL as mono the document had lost. The
    -- family itself is read before the fold (`elabDoc`, `urlFamily0`), so
    -- this arm only reports: a write here would give a `\url` in a title
    -- part the selector's position rather than the preamble's value.
    match v with
    | some val =>
      match urlStyleFamily? val with
      | some _ => return s
      | none =>
        warnOnce s.ctx ("ctrl:urlstyle:" ++ val) .W0104
          s!"'\\urlstyle\{{val}}' names no URL face; skipped" pos
          (help := "url.sty defines tt, rm, sf and same")
        return s
    | none =>
      diag s.ctx .E0304 "'\\urlstyle' needs a {tt|rm|sf|same} group" (some pos)
      return s
  | .pageGround source pos =>
    match source with
    | none => return { s with pageGround := none }
    | some source =>
      match ← readColor s.ctx s.palette none source pos with
      | .resolved c _ => return { s with pageGround := some c }
      | .missing =>
        warnPageColorMiss s.ctx source pos
        return s
      | .rejected => return s
  | .bodyStart _ _ =>
    -- Read off the scanned declarations by `elabDoc`, which opens the body
    -- with it; the fold has nothing to apply.
    return s
  | .captionsetup scope unclosed body pos =>
    -- The caption package's option interface (caption manual §2–4).
    -- `skip` and `aboveskip` set `\abovecaptionskip`, `belowskip` sets
    -- `\belowcaptionskip` (caption3.sty's option declarations): the
    -- `captionsep` and `belowcaptionskip` tokens, the two skips
    -- `Ir.captionSides` places. `position`/`tableposition`/`figureposition`
    -- declare the side captions are placed for (§2.2: the option does not
    -- move a caption, it tells the package which way its skips face), the
    -- document's `Doc.captionPos`. `margin` is the caption's own both-side
    -- margin (§2.4), the `captionmargin` token. A `[float type]` scope (§4)
    -- declares the kind's own token or position (`tablecaptionsep`),
    -- which only that kind reads; a type the engine has no float for
    -- names its keys unhonoured rather than reach every kind. A length
    -- reads as the document's other lengths do — a literal, or an
    -- expression over the declared tokens — and a skip set to its own
    -- register (`skip=\abovecaptionskip`) is the gap set to itself, which
    -- the package evaluates where the caption is set: a no-op. Every
    -- other key, and an honoured key whose value no reading carries (a
    -- {left,right} pair, an unknown position), is named and ignored
    -- (W0354), one warning per key.
    if let some bpos := unclosed then
      warnUnclosed s.ctx "'\\captionsetup'" bpos
    let kind? : Option (Option Ir.FloatKind) := scope.map Ir.FloatKind.ofCaptionType?
    match body with
    | some src =>
      let mut s := s
      for entry in src.splitOn "," do
        let parts := entry.splitOn "="
        let key := (parts.headD "").trimAscii.toString
        if key.isEmpty then continue
        let value := (String.intercalate "=" (parts.drop 1)).trimAscii.toString
        let honouredToken ← do
          -- Each honoured length key is one token, the styling door both
          -- backends read, beside the register it sets.
          let tokenOf := [("skip", ("captionsep", "abovecaptionskip")),
            ("aboveskip", ("captionsep", "abovecaptionskip")),
            ("belowskip", ("belowcaptionskip", "belowcaptionskip")),
            ("margin", ("captionmargin", ""))]
          match tokenOf.lookup key, kind? with
          | some _, some none => pure false
          | some (tok, reg), _ =>
            let tok := match kind? with
              | some (some k) => k.captionScope ++ tok
              | _ => tok
            -- premise: captionScopeChecks — a skip set to the caption skip
            -- itself ships the page the document ships without it
            if !reg.isEmpty && value == s!"\\{reg}" then pure true
            else
              let glue := (Decl.parseGlue value).orElse fun _ =>
                match Decl.parseLengthExpr (s.ctx.tokens.entries ++ s.ctx.engineTokens)
                    (String.join (value.splitOn "\\")) with
                | .ok g => some g
                | .error _ => none
              match glue with
              | some g =>
                let tokens := s.tokens.declare tok g
                s := { s with tokens := tokens, ctx := { s.ctx with tokens := tokens } }
                noteDeclared s.ctx "tokens" tok
                pure true
              | none => pure false
          | none, _ => pure false
        -- caption3.sty: `tableposition`/`figureposition` are
        -- `\captionsetup*[table|figure]{position=…}`, whatever scope the
        -- key is written under.
        let posScope : Option String := match key, kind? with
          | "tableposition", _ => some "table"
          | "figureposition", _ => some "figure"
          | "position", some (some k) => some k.captionScope
          | "position", none => some ""
          | _, _ => none
        let mut honouredPos := false
        if let some sc := posScope then
          if let some p := Ir.CaptionPos.ofKey? value then
            s := { s with captionPos := (s.captionPos.filter (·.1 != sc)).push (sc, p) }
            honouredPos := true
        unless honouredToken || honouredPos do
          let head := match scope with
            | some sc => s!"'\\captionsetup[{sc}]'"
            | none => "'\\captionsetup'"
          warnOnce s.ctx ("captionsetup:" ++ key) .W0354
            s!"{head} key '{key}' is not honoured; the caption keeps \
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
      storeTitlePart name (← elabInlines s.ctx b)
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
  | .algKw name args pos =>
    match args with
    | some (nm, val) =>
      let key := (Parse.rawSrc nm).trimAscii.toString
      let kd : AlgKwDef ←
        if name == "SetKw" then pure (.word val)
        else if name == "SetKwFunction" then pure (.func val)
        else if name == "SetKwData" then pure (.data val)
        else pure (.io (Ir.plainText (← elabInlines s.ctx val)))
      modify fun st => { st with alg := { st.alg with kws := st.alg.kws.push (key, kd) } }
      return s
    | none =>
      diag s.ctx .E0304 s!"'\\{name}' needs two groups: the name, then its text" pos
      return s
  | .algFlag name _ =>
    modify fun st =>
      if name == "DontPrintSemicolon" then { st with alg := { st.alg with semis := false } }
      else if name == "PrintSemicolon" then { st with alg := { st.alg with semis := true } }
      else { st with alg := { st.alg with numbered := true } }
    return s
  | .algSetting name pos =>
    warnOnce s.ctx ("alg:set:" ++ name) .N0102
      s!"'\\{name}' is not modelled; the algorithm keeps the engine's own display" pos
    return s
  | .newtheorem star env shared heading within pos =>
    match heading with
    | some h =>
      if env.isEmpty then
        warnOnce s.ctx "newtheorem:" .E0304 "'\\newtheorem' needs {name}{heading}" pos
        return s
      let thms := (← get).ctr.thm
      let name ← elabInlines s.ctx h
      -- A shared counter must exist (ltthm.dtx: "No counter defined" is an
      -- error there); unknown, the environment numbers on its own.
      let sharedOk := shared.any fun c => thms.counters.any (·.1 == c)
      if let some c := shared then
        unless sharedOk do
          warnOnce s.ctx ("newtheorem:" ++ env) .W0110
            s!"'\\newtheorem\{{env}}' shares counter '{c}', which no \\newtheorem \
declared; '{env}' numbers on its own" pos
            (help := "declare the environment that owns the counter first")
      let withinLvl ← match within, sharedOk with
        | some w, false =>
          match sectionLevel w with
          | some l => pure (some l)
          | none =>
            warnOnce s.ctx ("newtheorem:" ++ env ++ ":within") .W0110
              s!"'\\newtheorem\{{env}}' numbers within '{w}', a counter the engine \
does not keep; the number stands alone" pos
            pure none
        | _, _ => pure none
      let counter := if star then none else if sharedOk then shared else some env
      let counters := if !star && !sharedOk then thms.counters.push (env, withinLvl)
        else thms.counters
      let thms := { thms with
        defs := thms.defs.push ⟨env, name, counter, thms.style⟩, counters }
      modify fun st => { st with ctr := { st.ctr with thm := thms } }
      return s
    | none =>
      warnOnce s.ctx ("newtheorem:" ++ env) .E0304
        "'\\newtheorem' needs {name}{heading}" pos
      return s
  | .theoremstyle name pos =>
    let style := match name with
      | some "plain" => some ThmStyle.plain
      | some "definition" => some .definition
      | some "remark" => some .remark
      | _ => none
    match style with
    | some st =>
      modify fun e => { e with ctr := { e.ctr with thm := { e.ctr.thm with style := st } } }
      return s
    | none =>
      -- amsthm.sty's `\theoremstyle`: an undefined `th@<name>` warns and
      -- sets `\thm@style{plain}`, whatever style stood before.
      warnOnce s.ctx ("theoremstyle:" ++ name.getD "") .W0110
        s!"'\\theoremstyle' names '{name.getD ""}', not one of plain, definition, \
remark; plain applies, as amsthm sets it" pos
      modify fun e => { e with ctr := { e.ctr with thm := { e.ctr.thm with style := .plain } } }
      return s
  | .unknownCmd name unclosed pos =>
    -- A tikz-family set line is not unknown: the engine reads `\tikzset`
    -- itself (`Compat.nativeSetCtrls`), and while the boundary is open the
    -- rest ride into every wrapped standalone (`Compat.boundaryDecls`
    -- collected them), where the real TikZ reads them. A declared refusal
    -- (`tool = none`) makes only the ones the engine does not read unknown
    -- again.
    if Compat.nativeSetCtrls.contains name ||
        (s.ctx.pic.tool.isSome && Compat.boundaryCtrls.contains name) then
      return s
    -- Unknown preamble commands are configuration, not content: their
    -- arguments are skipped with them, never elaborated as stray text.
    warnOnce s.ctx ("ctrl:" ++ name) .W0301
      s!"unknown command '\\{name}' in the preamble; skipped" pos
      (help := unknownCmdHelp name false)
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

/-- Rule (b)'s remainder for the size ladder: a refused size-command
redefinition whose body opens with `\@setfontsize\X<size><leading>`
(fntguide §"\@setfontsize") still *declares* `\X` — the size read as a
per-mille step of the body in force, exactly as a class's `\normalsize`
already declares the body size itself (the Compat size idiom). Read at
the preamble's end in document order, as one declaration: the whole read
ladder through `Ir.setStepsAll`'s ordered door, or — only when the venue's
own ladder disorders — step by step through `Ir.setStep`, the offenders
named (`Ir.size_ladder_monotone`, `Ir.size_ladder_monotone_all`). A landed
step drops its W0361 and notes what it became (N0100); a step that would
disorder the named sizes keeps the built-in, its W0361 gaining the clause
saying why; a body whose head is not the idiom keeps plain rule (b). The
declared leading is not read:
the engine's leading is one page-level factor (`Ir.leadingFor`), already
the venue's own through `\normalsize`'s read-out, and no per-step leading
exists to declare. A redefinition that later won extracts nothing. -/
private def applyRefusedSizeLadder (s : PreState) : EM PreState := do
  let stash := (← get).refusedSizeBodies
  if stash.isEmpty then return s
  modify fun st => { st with refusedSizeBodies := #[] }
  -- Each stashed body's readable step, in document order — later wins.
  let mut steps : Array (String × Nat × Span) := #[]
  for (name, body, span) in stash do
    if (lookupUser s.ctx name).isSome then continue
    let b := skipSpaces body 0
    unless body[b]? matches some (.ctrl "@setfontsize" _) do continue
    let (fsArgs, _) := Compat.takeGroups body (b + 1) 3
    if fsArgs.size < 3 then continue
    let some a1 := fsArgs[1]? | continue
    let some sz := Compat.ptMacroArg a1 | continue
    let bodySp := s.page.fontSize
    if sz == 0 || bodySp ≤ 0 then continue
    -- `sz` is milli-points, so `Dim.pt sz` is a thousand times the size in
    -- sp: dividing by the body straight off gives the per-mille step.
    let factor : Nat := ((Dim.pt (Int.ofNat sz) + bodySp / 2) / bodySp).toNat
    steps := (steps.filter (·.1 != name)).push (name, factor, span)
  if steps.isEmpty then return s
  let land (name : String) (factor : Nat) (span : Span) : EM Unit :=
    modify fun st => { st with
      diags := (st.diags.filter fun d =>
        !(d.code == DiagCode.W0361.code
          && (d.message.splitOn s!"'\\{name}'").length > 1)).push
        (Diag.of .N0100
          s!"the refused '\\{name}' → the size ladder step \
{Compat.milliStr factor} of the body"
          (some span)) }
  let refuse (name : String) (factor : Nat) : EM Unit :=
    modify fun st => { st with
      diags := st.diags.map fun d =>
        if d.code == DiagCode.W0361.code
            && (d.message.splitOn s!"'\\{name}'").length > 1 then
          { d with message := d.message ++ s!"; its size \
({Compat.milliStr factor} of the body) would put the named sizes out of \
order, so it is not read" }
        else d }
  -- The venue's steps are one declaration: judged whole first, and only a
  -- ladder that disorders whole is salvaged step by step, the offenders
  -- named — both doors ordered by construction (`Ir.size_ladder_monotone`,
  -- `Ir.size_ladder_monotone_all`).
  match Ir.setStepsAll s.page.scale (steps.toList.map fun q => (q.1, q.2.1)) with
  | some ladder =>
    for (name, factor, span) in steps do
      land name factor span
    return { s with page := { s.page with sizes := some ladder } }
  | none =>
    let mut ladder := s.page.scale
    let mut moved := false
    for (name, factor, span) in steps do
      match Ir.setStep ladder name factor with
      | some l' =>
        ladder := l'
        moved := true
        land name factor span
      | none =>
        refuse name factor
    if moved then
      return { s with page := { s.page with sizes := some ladder } }
    else
      return s

/-- The LaTeX2e definer family the boundary standalone reads back as one
`\renewcommand`: each declares one command with an arity and an optional
default, so one re-emission serves them all (usrguide, "Defining
commands"). -/
def latexDefiners : List String :=
  ["newcommand", "renewcommand", "providecommand", "DeclareRobustCommand"]

/-- xparse's family. `\DeclareDocumentCommand` defines irrespective of
whether the name already exists (usrguide3, "Creating document commands"),
so the re-emission needs no guard of its own. -/
def xparseDefiners : List String :=
  ["NewDocumentCommand", "RenewDocumentCommand", "DeclareDocumentCommand",
   "ProvideDocumentCommand"]

/-- TeX's own definers, already total: each binds whatever the name held
(TeXbook ch. 20), so they ride in their own spelling. -/
def texDefiners : List String := ["def", "gdef", "edef", "xdef"]

/-- A definer's name argument: `\newcommand{\x}` and `\newcommand\x` both
spell it — the braced form is what LaTeX documents, the bare one what TeX
accepts and many classes write. -/
private def definerName? (raws : Array Raw) (i : Nat) : Option String :=
  match raws[i]? with
  | some (.ctrl n _) => some n
  | some (.group b _) =>
    b.findSome? fun (r : Raw) =>
      match r with
      | .ctrl n _ => some n
      | _ => none
  | _ => none

/-- One LaTeX2e definer, from the element after its head: the name, the
arity and the optional default as written, and the body. The re-emission
guards with `\providecommand` first, so the declaration cannot fail on a
name the standalone's own packages already own, and then states the
document's definition — a document that defined a name defined it for its
pictures too. -/
private def latexDefiner? (raws : Array Raw) (i : Nat) :
    Option ((String × String) × Nat) := do
  let i := skipStar raws i
  let name ← definerName? raws i
  let (arity, j) := takeOptRun raws (skipSpaces raws (i + 1))
  let (dflt, j) := takeOptRun raws (skipSpaces raws j)
  let j := skipSpaces raws j
  match raws[j]? with
  | some (.group body _) =>
    let spec := (match arity with | some a => s!"[{rawSrc a}]" | none => "") ++
      (match dflt with | some d => s!"[{rawSrc d}]" | none => "")
    let line := s!"\\providecommand\{\\{name}}\{}\
\\renewcommand\{\\{name}}{spec}\{{rawSrc body}}"
    some ((name, line), j + 1)
  | _ => none

/-- One xparse definer: its argument specification rides as written. -/
private def xparseDefiner? (raws : Array Raw) (i : Nat) :
    Option ((String × String) × Nat) := do
  let i := skipStar raws i
  let name ← definerName? raws i
  let j := skipSpaces raws (i + 1)
  let k := skipSpaces raws (j + 1)
  match raws[j]?, raws[k]? with
  | some (.group sig _), some (.group body _) =>
    some ((name,
      s!"\\DeclareDocumentCommand\{\\{name}}\{{rawSrc sig}}\{{rawSrc body}}"), k + 1)
  | _, _ => none

/-- One TeX definer: the parameter text between the name and the body rides
verbatim. The scan for the body group is bounded — a parameter text is a
short run of `#k` tokens and delimiters, so a head with no body group of its
own never reaches forward into the document for one. -/
private def texDefiner? (head : String) (raws : Array Raw) (i : Nat) :
    Option ((String × String) × Nat) := Id.run do
  match raws[i]? with
  | some (.ctrl name _) =>
    let lim := min raws.size (i + 17)
    let mut k := i + 1
    let mut found := false
    for _ in [i + 1:lim] do
      if raws[k]? matches some (.group _ _) then
        found := true
        break
      k := k + 1
    if !found then return none
    match raws[k]? with
    | some (.group body _) =>
      let params := rawSrc (raws.extract (i + 1) k)
      return some ((name, s!"\\{head}\\{name}{params}\{{rawSrc body}}"), k + 1)
    | _ => return none
  | _ => return none

/-- The native `\define \name(sig) {body}`, so the LaTeX spelling and the
native one carry the same definition to the boundary — a document that
writes `\define` itself is not a document whose pictures lose their macros.
The signature's parameter count becomes LaTeX's arity and a leading
optional parameter its empty default: the native form carries no default
value to spell back, which is why the definer family is read as written
rather than through a `UserCmd`. -/
private def nativeDefiner? (raws : Array Raw) (i : Nat) :
    Option ((String × String) × Nat) := Id.run do
  match raws[i]? with
  | some (.ctrl name _) =>
    let lim := min raws.size (i + 33)
    let mut k := i + 1
    let mut found := false
    for _ in [i + 1:lim] do
      if raws[k]? matches some (.group _ _) then
        found := true
        break
      k := k + 1
    if !found then return none
    match raws[k]? with
    | some (.group body _) =>
      let sig := rawSrc (raws.extract (i + 1) k)
      let entries := (sig.splitOn ",").filter fun e => e.toList.any Char.isAlpha
      let spec :=
        if entries.isEmpty then ""
        else if ((entries.headD "").splitOn "?").length > 1 then s!"[{entries.length}][]"
        else s!"[{entries.length}]"
      let line := s!"\\providecommand\{\\{name}}\{}\
\\renewcommand\{\\{name}}{spec}\{{rawSrc body}}"
      return some ((name, line), k + 1)
    | _ => return none
  | _ => return none

mutual

-- conserves: none — the walk collects the document's macro definitions for
-- the boundary standalone and drops everything else by design, so no
-- census equality can hold. What the collection must satisfy is stated
-- where it pays: `Ir.macroDecls_covers` over the request it feeds.
private def macroScanLevel (raws : Array Raw) (out : Array (String × String)) :
    List Raw → Nat → Nat → Array (String × String)
  | [], _, _ => out
  | _ :: rest, i, skip + 1 => macroScanLevel raws out rest (i + 1) skip
  | .ctrl name _ :: rest, i, 0 =>
    let read? : Option ((String × String) × Nat) :=
      if latexDefiners.contains name then latexDefiner? raws (i + 1)
      else if xparseDefiners.contains name then xparseDefiner? raws (i + 1)
      else if texDefiners.contains name then texDefiner? name raws (i + 1)
      else if name == "define" then nativeDefiner? raws (i + 1)
      else none
    match read? with
    | some (entry, k) =>
      -- LaTeX's provide keeps an existing definition, so a provide of a
      -- name this document already bound declares nothing.
      let provide := name == "providecommand" || name == "ProvideDocumentCommand"
      let kept := if provide && out.any (fun q => q.1 == entry.1) then out
        else out.push entry
      macroScanLevel raws kept rest (i + 1) (k - (i + 1))
    | none => macroScanLevel raws out rest (i + 1) 0
  | r :: rest, i, 0 => macroScanLevel raws (macroScanRaw out r) rest (i + 1) 0

/-- Descend into a group or an environment, structurally on `Raw` —
`boundaryRaw`'s shape. A picture's own body is that standalone's already,
so a definition written inside one is not hoisted out of it. -/
private def macroScanRaw (out : Array (String × String)) : Raw → Array (String × String)
  | .group body _ => macroScanLevel body out body.toList 0 0
  | .env n body _ =>
    if Compat.pictureEnvs.contains n then out
    else macroScanLevel body out body.toList 0 0
  | .math _ body _ => macroScanLevel body out body.toList 0 0
  | .word _ _ => out
  | .space => out
  | .par _ => out
  | .ctrl _ _ => out
  | .sym _ _ => out
  | .verb _ _ _ => out

end

/-- The document's own macro definitions for the boundary and the picture
walk, one entry per name, in the document order of each name's last word —
LaTeX's last definition is what a use at the end of the document means, and
the standalone reads one definition per name rather than a replay.

**A name the document defines with different texts is left out.** A
picture reads a macro where the picture stands, and one table for the whole
document cannot say which of several definitions is in force at a given
picture: read that way, a label drew the last definition at every site.
The conditional pass puts the site's own value into a picture for every
parameterless macro it can read there; what is left here is the rest, so a
name whose definitions all agree is the same at every site, and one whose
definitions differ is not expanded at all — the walk names it where it
stands, and a boundary standalone that needs it fails in the tool, in the
tool's words — rather than drawn with a definition that may not be its.

Read over the *unrewritten* tree, as the boundary preamble's collector is
(`Compat.boundaryScan`): the native `\define` a rewrite produces cannot
spell an optional argument's default back, so the declaration the
standalone reads is captured as the document wrote it rather than
reconstructed from a `UserCmd`. -/
def macroScan (raws : Array Raw) : Array (String × String) := Id.run do
  let all := macroScanLevel raws #[] raws.toList 0 0
  let mut last : Std.HashMap String Nat := {}
  let mut text : Std.HashMap String String := {}
  let mut differ : Std.HashSet String := {}
  for i in [0:all.size] do
    if let some (n, l) := all[i]? then
      last := last.insert n i
      match text[n]? with
      | some l0 => if l0 != l then differ := differ.insert n
      | none => text := text.insert n l
  let mut out : Array (String × String) := #[]
  for i in [0:all.size] do
    if let some (n, l) := all[i]? then
      if last[n]? == some i && !differ.contains n then out := out.push (n, l)
  return out

/-- The pictures the engine drew *itself*: the `.picture` nodes the body walk
produced, at any depth. Those nodes have exactly two sources — the shapes the
rendered subset evaluated, and the placeholder that marks a picture the
subset refused whole — so a positive count says the engine, not the boundary
tool, put the diagram on the page. The gate on the `\tikzset` key diagnostic
reads it, and `pictureKeys_named` states over it. -/
def enginePictures (blocks : Array Block) : Nat :=
  Ir.foldBlocks (fun n b => match b with | .picture _ => n + 1 | _ => n)
    (fun n _ => n) 0 blocks

/-- Elaborate the whole document: split preamble and body around the
`document` environment, process declarations, then the body. -/
def elabDoc (file : String) (raws : Array Raw) (picPre : String := "")
    (picSets : Array (Pos × Array Raw) := #[])
    (picMacros : Array (String × String) := #[])
    (picMetric : Ir.Pic.LabelMetric := fun _ _ => {})
    (picWithdrawn : Array String := #[]) :
    EM (Doc × Ir.RefTable) := do
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
  let decls := scanDecls file preamble
  -- The boundary door is read before the fold: a `\tikzset` above the
  -- `\pictures` line is already the boundary's to keep (or W0301's, above
  -- a refusal), so the door is read off the scanned declarations first,
  -- order-free. Open by default; a `\pictures` block pins a tool or
  -- refuses (`tool = none`). The apply arm still owns every diagnostic
  -- for the block's contents.
  let picTool0 : Option String :=
    (decls.findSome? fun d =>
      match d with
      | .pictures (some src) _ =>
        (Decl.splitEntries src).findSome? fun e =>
          match Decl.splitEntry e with
          | some ("tool", v) =>
            let v := v.trimAscii.toString
            if v == "none" then some none
            else if picTools.contains v then some (some v) else none
          | _ => none
      | _ => none).getD (some "lualatex")
  -- url.sty's selector is read off the scanned declarations too, for the
  -- reason the boundary door is: order. A `\url` inside `\author`, a
  -- running head or a logo elaborates where it is declared, while LaTeX
  -- typesets it at `\maketitle` or on the page — after every preamble
  -- selector has run. So the family the preamble's content reads is the
  -- last defined value the preamble names, wherever it stands (T1, the
  -- commutation `scripts/compose-fuzz.lean` checks over this head); the
  -- apply arm keeps every diagnostic and writes nothing, and the body
  -- starts from the same value.
  let urlFamily0 : Option Ir.Style := decls.foldl (fun fam d =>
      match d with
      | .urlstyle (some v) _ => (urlStyleFamily? v).getD fam
      | _ => fam) (← get).urlFamily
  modify fun st => { st with urlFamily := urlFamily0 }
  let s ← decls.foldlM applyDecl
    { ctx := { file := file
               pic := { tool := picTool0, preamble := picPre, metric := picMetric
                        withdrawn := picWithdrawn, macros := picMacros
                        sets := picSets.map (·.2) } } }
  -- What a `\tikzset` left unread is named at the line that wrote it, and
  -- the gate is *who drew the picture* — read below, off the elaborated
  -- body, once the drawings are facts rather than a configuration.
  -- What a refused `\maketitle` redefinition still declares, applied once
  -- the fold has bound everything its body names.
  let s ← applyRefusedTitleStyle s
  -- What refused size redefinitions still declare: the document's ladder.
  let s ← applyRefusedSizeLadder s
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
  let basePalette := themedDs.palette
  let palette := match s.pageGround with
    | some c => basePalette.declare "bg" c
    | none => basePalette
  let tokens := themedDs.tokens
  let styles := themedDs.styles
  let chrome := themedDs.chrome
  ctx := { ctx with palette := palette, basePalette := basePalette, tokens := tokens, styles := styles
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
  -- text block. `classPageDefaults` is the one resolving site — the same
  -- door `engineLengthTokens` reads, so the preamble's token environment
  -- and the shipped page are one value (`engine_tokens_agree`). `twocolumn`
  -- and `draft` ask for a page model and a proofing mode the engine does
  -- not have: each is refused by name (W0356) — the silent drop was the
  -- defect class here, an a4paper request quietly shipping on letter.
  let classOpts := (classOptions.splitOn ",").map (·.trimAscii.toString)
  page := classPageDefaults record classOpts page
  for o in classOpts do
    if o == "twocolumn" then
      diag ctx .W0356
        "class option 'twocolumn' asks for a two-column page; the text is set in one column"
        none
    else if o == "draft" then
      diag ctx .W0356
        "class option 'draft' asks for a proofing mode the engine does not have; the document is rendered in full"
        none
  if record.model == .flow && !sawPage then
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
                    face := record.model == .face
                    numberHeadings := record.numberHeadings, styles := styles
                    page := page
                    engineTokens := engineLengthTokensOfPage page }
  -- Numbering is a property of the finished document, not of any one
  -- elaboration site: `Ir.numberFloats` fills every captioned float's
  -- number in document order (`numberFloats_exact` is the fact `\ref`
  -- will resolve against), once, before any backend reads the body.
  -- The preamble's own declarations that are in force where the body
  -- begins open it, in the order they were written (`PDecl.bodyStart`).
  let opening : Array Raw := decls.filterMap fun d =>
    match d with
    | .bodyStart m p => some (.ctrl m p)
    | _ => none
  let blocks := Ir.numberFloats (← elabBlocks ctx (opening ++ body))
  -- **Whatever drew a picture, the keys that drawing did not read are
  -- named.** A `\tikzset` entry outside the rendered subset has exactly one
  -- other reader: the real TikZ, and only for a picture that went to the
  -- boundary (`tikzArm` routes there what the subset draws nothing of, or
  -- draws with a loss it names). So the loss is real as soon as the engine
  -- drew one picture itself — whatever `\pictures{ tool = ... }` nominally
  -- says, and
  -- a mixed document is the case that matters, since one boundary picture
  -- buys no silence for the twelve beside it. The gate the refusal used to
  -- carry claimed the boundary read them whenever a tool was configured;
  -- native drawing made that premise false and the keys were dropped in
  -- silence, an arrow-tip default among them.
  -- Read here rather than in the preamble fold because *who drew it* is a
  -- fact of the elaborated body — the `.picture` nodes this walk produced —
  -- never of a configuration, and never of how layout will resolve them.
  if enginePictures blocks > 0 then
    let mut styles : List (String × Array Picture.Tok) := []
    for (pos, keys) in picSets do
      let toks := Picture.ofRaws keys
      for key in Picture.unreadKeys styles toks do
        warnOnce ctx ("picture:set:" ++ key) .W0334
          s!"picture key {key} is outside the rendered picture subset; \
the key is dropped" pos
          (help := "the rendered subset reads 'name/.style={...}' definitions")
      styles := (Picture.readStyleList styles toks).1
  -- The label table, complete: the float rows are read off the numbered IR
  -- just produced (`Ir.floatLabelRows`), so a label under a captioned
  -- float binds to the number the node carries — one numbering,
  -- `Ir.refs_agree_with_numbering` the statement. References resolve
  -- against it once the document is assembled below; W0380 is judged here
  -- from the recorded sites, because a kindless binding is a fact of the
  -- table, not of the resolved node.
  let stRefs ← get
  let table := if stRefs.labels.isEmpty then stRefs.labels
    else Ir.withFloatRows stRefs.labels (Ir.floatLabelRows blocks)
  let mut warnedRefs : Array String := #[]
  for (key, form, rpos) in stRefs.refSites do
    unless warnedRefs.contains key do
      if let some (_, some b) := table.find? (·.1 == key) then
        -- The binding is numbered but kindless (a bare \refstepcounter):
        -- a form that must name what the label names has no name to use,
        -- so the plain number stands (refText), named here.
        if b.kind.isNone && refFormNeedsKind form then
          warnedRefs := warnedRefs.push key
          diag ctx .W0380
            s!"'{key}' names a bare counter step, not a heading, equation, or float; the plain number is set"
            (some rpos)
            (help := "reference it with \\ref, or move the \\label after the numbered thing it should name")
  -- A citation with no bibliography anywhere: `Bib.apply` never runs
  -- (`Ir.bibRefs` stays empty — nothing requests a file), the
  -- missing-file diagnostic has no file to miss, and the mark ships '?'
  -- unexplained. The loss is W0351's (a citation names no bibliography
  -- entry); the message and help name this cause. One diagnostic per
  -- distinct key, at its first `\cite`.
  if (Ir.bibRefsBlocks blocks).isEmpty && (Ir.ownBibItemsBlocks blocks).isEmpty then
    for (key, span) in stRefs.spans.cites do
      modify fun st => { st with diags := st.diags.push (Diag.of .W0351
        s!"citation '{key}' has no bibliography to resolve against; it shows as '?'"
        (some span)
        (help := "the document declares no bibliography; \\bibliography{file} \
names the .bib file")
        (subject := some key)) }
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
  let mut logo := (← get).logos.main
  if !record.runningFurniture && logo.isSome then
    diag ctx .W0317
      "a card carries no logo; the declaration is dropped" none
    logo := none
  -- The headline band: a headline class (`ClassRecord.headline`) reads
  -- the `\title` family as furniture, the gemini lineage's headline rule.
  -- The corner slots ride only with the band: under a class with no band
  -- they are dropped by name (the card-logo rule), and under a headline
  -- class with no declared `\title` there is no band for them to stand
  -- in, so that is said too rather than dropped silently.
  let stH ← get
  let nonEmpty (v : Option (Array Inline)) : Option (Array Inline) :=
    v.bind fun xs => if xs.isEmpty then none else some xs
  let headline : Option Ir.Headline := if record.headline then
      (nonEmpty stH.title).map fun t =>
        { title := t
          author := (nonEmpty stH.author).getD #[]
          institute := (nonEmpty stH.institute).getD #[] }
    else none
  let mut logoLeft := stH.logos.left
  let mut logoRight := stH.logos.right
  if logoLeft.isSome || logoRight.isSome then
    if !record.headline then
      diag ctx .W0317
        s!"the {docClass.name} class draws no headline band; the corner logo declaration is dropped"
        none
      logoLeft := none
      logoRight := none
    else if headline.isNone then
      diag ctx .W0309
        "a corner logo is declared but no '\\title' is; the headline band and its logos do not draw"
        none (help := "declare \\title{...} (and \\author, \\institute) in the preamble")
      logoLeft := none
      logoRight := none
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
          | .frame _ _ _ _ _ => n + 1
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
  -- A declared conformance profile is a set element that implies exactly
  -- one assertion, `pdf.profile = <name>`, judged on the census of the
  -- built bytes (the class-implied shape); and it folds its
  -- backend-neutral demands into the output contract — where the document
  -- declared a contract key itself, the declaration wins, whatever order
  -- the two were written in (read here, after every `\output`, so the
  -- fold commutes with the declarations).
  let seen := (← get).seenScalars
  let declaredKey (k : String) : Bool :=
    seen.any fun e => e.1 == "output" && e.2.1 == k
  for name in output.profiles do
    asserts := asserts.push {
      kind := .pdfProfile name
      help := some s!"declared by \\output\{ profiles = {name} }; the rules named are the file's, judged on its bytes" }
    let imp := PdfContract.Profile.implies name
    output := { output with contract := {
      alternatives := if declaredKey "alternatives" || imp.alternatives == ({} : OutputContract).alternatives
        then output.contract.alternatives else imp.alternatives
      color := if declaredKey "color" || imp.color == ({} : OutputContract).color
        then output.contract.color else imp.color
      fonts := if declaredKey "fonts" || imp.fonts.isNone
        then output.contract.fonts else imp.fonts } }
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
  let doc : Doc := {
    docClass := docClass
    classOptions := classOptions
    page := page
    fonts := fonts
    palette := palette
    tokens := tokens
    captionPos := s.captionPos
    head := head
    foot := foot
    logo := logo
    headline := headline
    logoLeft := logoLeft
    logoRight := logoRight
    headFrom := headFrom
    footFrom := footFrom
    chrome := chrome
    chromeDeclared := chromeDeclared
    styles := styles
    info := info
    output := output
    asserts := asserts
    allow := allow
    natbib := (← get).natbib
    pictureTool := ctx.pic.tool
    pictureSrcs := (← get).pictures
    picturePreamble := ctx.pic.preamble
    -- Request material, so a document that states no request carries none:
    -- a `\newcommand` is otherwise a change to every document's `Doc`, and
    -- the definer family's whole point is that it moves no ink by itself.
    pictureMacros := if (← get).pictures.isEmpty then #[] else ctx.pic.macros
    salvage := (← get).salvage
    frameRestart := (← get).frameRestart
    body := blocks
  }
  -- Cross-references resolve here, once, against the whole document's
  -- labels — every region a backend reads (`Ir.mapDoc`), so a `\ref` in a
  -- running head resolves as one in the body does, and `Ir.resolveRefs` is
  -- a pure pass over the IR: no backend re-scans for labels and a forward
  -- reference costs nothing. What stays `??` is named by `Ir.refDiags`,
  -- read off the resolved census (`runRaws`, and the driver after the
  -- bibliography resolves), never from the sites: a reference cannot be
  -- judged where it stands, because its label may follow it.
  let doc := if stRefs.refSites.isEmpty then doc
    else Ir.mapDoc (Ir.resolveRefInlines ctx.locale table) (Ir.resolveRefs ctx.locale table) doc
  return (doc, table)

/-- Where the requests a document states were declared — reporting metadata
the driver reads to place its missing-file diagnostics. Delivered beside
the `Doc`, never in it: two spellings of one document elaborate to one
`Doc` (the compat conservation oracle holds them equal), while their
marker positions differ. -/
structure ReqSpans where
  /-- Each `\bibliography` marker's span, keyed by its named source: the
  line E0503 names when the driver finds no file. -/
  bib : Array (String × Span) := #[]
  /-- Each image source's first span — file images and boundary pictures
  alike: where the driver's per-picture W0376 and E0382 point. -/
  images : Array (String × Span) := #[]
  /-- The boundary pictures the rendered subset draws in part, by picture
  id: a request here that no tool draws is withdrawn, and the picture is
  drawn natively instead (`Cli.Boundary.withdraw`, and `runRaws` for a
  caller that fulfils nothing). -/
  fallbacks : Array String := #[]
  /-- Each reference key's first site: where W0349 points. -/
  refs : Array (String × Span) := #[]
  /-- The label table resolution spent, for W0349's cause (`Ir.refDiags`). -/
  labels : Ir.RefTable := #[]
  deriving Repr, BEq, Inhabited

/-- The source both of a document's elaborations read: the compat rewrite
applied, the boundary and macro scans taken, the warn-once key set the
rewrite already spent. Held as a value because a metric-carrying pass and
the pass that discovers the metric must read the *same* rewritten tree —
rewriting twice would make the two passes' documents functions of two
sources, and nothing would state they agree. -/
structure Prepared where
  raws : Array Raw
  picPre : String
  picSets : Array (Pos × Array Raw)
  picMacros : Array (String × String)
  warned : Array String
  compatDiags : Array Diag

/-- The name a definer's head binds, when its next item (past spaces and a
`*`) is a one-word group. -/
private def definedEnvName : List Raw → Option String
  | .space :: rest => definedEnvName rest
  | .sym '*' _ :: rest => definedEnvName rest
  | .group #[.word n _] _ :: _ => some n
  | _ => none

mutual

/-- **Only a definer judges its bodies.** The parse keeps an environment or
math opened in one of an environment definer's bodies and closed in the
other as two halves (`Parse.splitOpen`, `Parse.splitClose`), because LaTeX
balances them where the environment is used. A refused definition — a
built-in name, W0303's — ignores its bodies, so its halves raise nothing
and ship nothing; every other definition's halves settle to the tree a
plain parse builds, the open half closed at its body's brace and the close
half dropped, with that parse's diagnostics. A package file's splice drops them, as it drops its
parse's (`Cli.Input.expandLocalSty`). `skip` counts the groups a refused
definition still holds at this level: its name and its two bodies. -/
-- conserves: none — settling rebuilds the parse's recovery tree by design.
private def settleList (file : String) (skip : Nat) (out : Array Raw)
    (ds : Array Diag) : List Raw → Array Raw × Array Diag
  | [] => (out, ds)
  | .ctrl d p :: rest =>
    -- premise: refusedEnvChecks — a built-in's definition is ignored whole
    -- (W0303), so its halves owe no diagnostic
    let refused := Parse.envDefiners.contains d &&
      (definedEnvName rest).any builtinEnvNames.contains
    settleList file (if refused then 3 else skip) (out.push (.ctrl d p)) ds rest
  | .group body p :: rest =>
    if skip > 0 then settleList file (skip - 1) (out.push (.group body p)) ds rest
    else
      let (rs, ds) := settleOne file ds (.group body p)
      settleList file 0 (out ++ rs) ds rest
  | r :: rest =>
    let (rs, ds) := settleOne file ds r
    settleList file skip (out ++ rs) ds rest

/-- One raw of `settleList`'s walk: a half settles, anything else descends. -/
private def settleOne (file : String) (ds : Array Diag) : Raw → Array Raw × Array Diag
  | .group body p =>
    let (body', ds) := settleList file 0 #[] ds body.toList
    (#[.group body' p], ds)
  | .env n body p =>
    let quiet := Compat.packageFile file
    match Parse.splitOpen? n, Parse.splitClose? n with
    | some e, _ =>
      let (body', ds) := settleList file 0 #[] ds body.toList
      let (rs, d) := Parse.settleOpenHalf file e body' p
      (rs, if quiet then ds else ds.push d)
    | none, some e =>
      (#[], if quiet then ds else ds.push (Parse.closeHalfDiag file e p))
    | none, none =>
      let (body', ds) :=
        settleList ((Parse.inputEnvFile? n).getD file) 0 #[] ds body.toList
      (#[.env n body' p], ds)
  | .math dm body p =>
    let (body', ds) := settleList file 0 #[] ds body.toList
    (#[.math dm body' p], ds)
  | .word w p => (#[.word w p], ds)
  | .space => (#[.space], ds)
  | .par p => (#[.par p], ds)
  | .ctrl c p => (#[.ctrl c p], ds)
  | .sym c p => (#[.sym c p], ds)
  | .verb e s p => (#[.verb e s p], ds)

end

/-- Settle every definer body's halves in a parsed tree (`settleList`). -/
def settleSplits (file : String) (raws : Array Raw) : Array Raw × Array Diag :=
  settleList file 0 #[] #[] raws.toList

/-- Rewrite and scan, once. LaTeX idioms become native declarations here,
which is why a `\fonts` a document never wrote — `\setmainfont`, a class
option, a beamer font theme — is nonetheless a declaration the preamble
carries by the time anything reads it. -/
def prepare (file : String) (raws : Array Raw) : Prepared :=
  let (raws, splitDiags) := settleSplits file raws
  let picScan := Compat.boundaryScan raws
  let picMacros := macroScan raws
  let (raws, compatDiags, warned) :=
    Compat.rewrite file raws (provideKeeps := renderedBuiltins ++ structuralNames)
  let (raws, textDiags, warned) := Compat.rewriteText file raws warned
  { raws := raws, picPre := picScan.pre, picSets := picScan.sets
    picMacros := picMacros, warned := warned
    compatDiags := splitDiags ++ compatDiags ++ textDiags }

/-- What a source's own pictures could ask a face for. `draws` is whether an
environment the native subset draws stands anywhere in the rewritten tree;
`math` is whether any of those bodies sets a formula, which decides whether
a face resolved before elaboration needs a math slot. -/
structure PicWants where
  draws : Bool := false
  math : Bool := false

mutual

/-- One level of the picture-possibility walk; the list drives the recursion. -/
-- conserves: none — the walk answers two Bools about the tree, not a tree,
-- so no census equality can hold. What it must satisfy is stated where it
-- pays: a false `draws` means no node is ever measured, so no face is
-- needed to elaborate (`Cli.FontFix`'s fallback covers a false positive in
-- either field, which is why only the negative answer must be exact).
private def picWantsLevel (inPic : Bool) (acc : PicWants) : List Raw → PicWants
  | [] => acc
  | r :: rest => picWantsLevel inPic (picWantsRaw inPic acc r) rest

/-- Descend into a group or an environment, structurally on `Raw`. -/
private def picWantsRaw (inPic : Bool) (acc : PicWants) : Raw → PicWants
  | .env n body _ =>
    let drawn := Compat.pictureEnvs.contains n
    picWantsLevel (inPic || drawn)
      (if drawn then { acc with draws := true } else acc) body.toList
  | .group body _ => picWantsLevel inPic acc body.toList
  | .math _ body _ =>
    picWantsLevel inPic (if inPic then { acc with math := true } else acc) body.toList
  | .word _ _ => acc
  | .space => acc
  | .par _ => acc
  | .ctrl _ _ => acc
  | .sym _ _ => acc
  | .verb _ _ _ => acc

end

/-- Whether an engine picture is *possible*, and what it would measure. The
negative answer is the one that has to be trustworthy, and it is: `.picture`
blocks have exactly one producer, the `{tikzpicture}` arm of the body walk,
so no such environment means no node is ever measured and no face is needed
to elaborate. A positive answer promises nothing — a picture may still
refuse whole to the boundary, and a label may take its formula from a macro
this walk cannot see — which is why it only buys a *provisional* face, and
why the driver checks that face against the settled one. -/
def picWants (raws : Array Raw) : PicWants :=
  picWantsLevel false {} raws.toList

/-- **The preamble as its own document.** What the font environment is a
function of, run through the very fold the full elaboration runs
(`elabDoc` over the preamble and an empty body), so the `\fonts`, `\page`
and `\documentclass` a provisional face resolves from are the declarations
the document itself settles on — class defaults, theme bundle and compat
rewrites included — rather than a second reading of the same lines.

Diagnostics are the full pass's; this one's are discarded, so nothing a
reader sees is said twice. -/
def preambleDoc (file : String) (p : Prepared) : Doc :=
  let docIdx := p.raws.findIdx? fun r =>
    match r with
    | .env "document" _ _ => true
    | _ => false
  let raws := match docIdx with
    | some idx => (p.raws.extract 0 idx).push (.env "document" #[] ⟨0, 0⟩)
    | none => #[.env "document" #[] ⟨0, 0⟩]
  ((elabDoc file raws p.picPre p.picSets p.picMacros).run
    { warnedUnknown := p.warned }).1.1

/-- Elaborate prepared input against a measurement, with the boundary
requests fulfilment withdrew (`picWithdrawn`; empty on a first pass). -/
def runPrepared (file : String) (p : Prepared) (earlier : Array Diag := #[])
    (picMetric : Ir.Pic.LabelMetric := fun _ _ => {})
    (picWithdrawn : Array String := #[]) :
    Doc × Array Diag × ReqSpans :=
  let raws := p.raws
  let compatDiags := p.compatDiags
  let warned := p.warned
  -- One warn-once key set for the document, not one per pass: the rewrite
  -- fires keys this walk also fires (`spec:overlay`), so the elaborator
  -- starts from what the document has already been told, not from empty.
  let ((doc, table), st) :=
    (elabDoc file raws p.picPre p.picSets p.picMacros picMetric picWithdrawn).run
      { warnedUnknown := warned }
  -- The realization pass rewrites the document where a (role, ground)
  -- pair fails and the solver can meet it (Core/Contrast.lean): both
  -- backends then read the realized values, and the diagnostics carry
  -- N0022 where a pair realized, the pairing warnings where none could.
  let (doc, contrast) := Contrast.realizeDoc doc (colorSiteOf st.spans.colors)
  let outline := Ir.outlineDiags doc
  -- The file-image face only: boundary pictures are judged by the driver
  -- after fulfilment (`Ir.picAltDiags`), where E0382's outcome is known.
  let alt := Ir.altDiags doc fun src => (st.spans.images.find? (·.1 == src)).map (·.2)
  let links := Ir.linkDiags doc
  let sequences := Ir.footerSequenceDiags doc
  (doc, Diag.tallySites
    (earlier ++ compatDiags ++ st.diags ++ contrast ++ outline ++ alt ++ links ++ sequences),
    { bib := st.spans.bib
      images := st.spans.images
      fallbacks := st.spans.fallbacks
      refs := (st.refSites.foldl (init := (#[], (∅ : Std.HashSet String)))
        fun (out, seen) (key, _, pos) =>
          if seen.contains key then (out, seen)
          else (out.push (key, ⟨file, pos⟩), seen.insert key)).1
      labels := table })

/-- Elaborate parsed input. LaTeX idioms are rewritten first, so a document
written for another engine compiles as written. Returns the request spans
too, for the driver's missing-file and per-picture diagnostics. The
unresolved-reference judge (`Ir.refDiags`) is not run here: the driver
runs it after `Bib.apply`, over the very document the backends read, so
the resolution gate (`pending_named`) is one statement over that tail;
`runRaws`, the face that fulfils nothing, runs it itself.

The prepare-and-run face, for every caller that reads a document once: the
driver splits the two so a provisional face can be resolved between them. -/
def runRawsSpanned (file : String) (raws : Array Raw) (earlier : Array Diag := #[])
    (picMetric : Ir.Pic.LabelMetric := fun _ _ => {}) :
    Doc × Array Diag × ReqSpans :=
  runPrepared file (prepare file raws) earlier picMetric

/-- The span a reporting record holds for a key, for the judges. -/
def ReqSpans.spanOf (rs : Array (String × Span)) (key : String) : Option Span :=
  (rs.find? (·.1 == key)).map (·.2)

/-- The span-free face: what every caller that fulfils no file requests
reads — with the unresolved-reference judge run over the elaborated
document, since no bibliography resolution follows here. Fulfilling
nothing, it has no boundary tool either, so it withdraws every request the
rendered subset can stand in for (`ReqSpans.fallbacks`) and elaborates
again, as the driver does on a machine with no tool and a cold cache
(`Cli.Boundary.withdraw`): the document it returns is the page such a build
ships, the subset's drawing with its refusals named. The first pass — the
requests, stated from the document alone — is `runRawsSpanned`'s. -/
def runRaws (file : String) (raws : Array Raw) (earlier : Array Diag := #[])
    (picMetric : Ir.Pic.LabelMetric := fun _ _ => {}) :
    Doc × Array Diag :=
  let p := prepare file raws
  let first := runPrepared file p earlier picMetric
  let (doc, diags, rs) := if first.2.2.fallbacks.isEmpty then first
    else runPrepared file p earlier picMetric first.2.2.fallbacks
  (doc, Diag.tallySites (diags ++ Ir.refDiags rs.labels (ReqSpans.spanOf rs.refs) doc))

def run (file input : String) : Doc × Array Diag :=
  let (toks, lexDiags) := Lex.lex file input
  let (raws, parseDiags) := Parse.parse file toks
  runRaws file raws (lexDiags ++ parseDiags)

end LeanTex.Core.Elab
