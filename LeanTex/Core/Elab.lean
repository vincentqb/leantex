module

public import Std.Data.HashSet
public import LeanTex.Core.Lex
public import LeanTex.Core.Parse
import LeanTex.Core.MathParse
import LeanTex.Core.TextSymData
public import LeanTex.Core.Ir
import LeanTex.Core.ListMark
public import LeanTex.Core.Dim
import LeanTex.Core.Decl
import LeanTex.Core.KeyVal
public import LeanTex.Core.Theme
public import LeanTex.Core.Compat
import LeanTex.Core.Contrast
public import LeanTex.Core.Picture
import LeanTex.Core.PictureCensus
import LeanTex.Core.FaIcons
import LeanTex.Core.BibAccent
import LeanTex.Core.PdfContract
import LeanTex.Core.PdfDate
import LeanTex.Core.Referent
public import LeanTex.Core.ListingReply
import LeanTex.Core.Listing
import LeanTex.Core.LexerName
public import LeanTex.Core.BeamerColor
public import LeanTex.Core.UnusedSetting
public import LeanTex.Core.Blueprint

namespace LeanTex.Core.Elab

open LeanTex.Core LeanTex.Core.Parse LeanTex.Core.Ir LeanTex.Core.Dim

public inductive ParamType where
  | text
  | content
  deriving Repr, BEq

public structure Param where
  name : String
  type : ParamType
  optional : Bool
  /-- The replacement references this parameter; an unreferenced argument is
  consumed without elaboration. -/
  referenced : Bool := true
  /-- A minted command in the replacement reads this parameter as code. -/
  code : Bool := false
  /-- The text an absent optional argument takes: its definition's `[default]`. -/
  default : Option (Array Raw) := none
  deriving Repr, BEq

public structure UserCmd where
  name : String
  params : Array Param
  body : Array Raw
  span : Span
  deriving Repr, BEq

/-- An environment the document defines with `\defineenv` or
`\newenvironment`. -/
public structure UserEnv where
  name : String
  params : Array Param
  beginBody : Array Raw
  endBody : Array Raw
  /-- The halves see only the commands defined before this environment. -/
  cmdLimit : Nat
  ignoresLead : Bool := false
  trimsTail : Bool := false
  ignoresAfterEnd : Bool := false
  deriving Repr, BEq

/-- A theorem style: the kernel's (latex.ltx `\@begintheorem`) without
amsthm, else one of amsthm's three. -/
public inductive ThmStyle where
  | kernel
  | plain
  | definition
  | remark
  deriving Repr, BEq, Inhabited

private def ThmStyle.space : ThmStyle → Ir.ThmSpace
  | .kernel => .kernel
  | .plain | .definition => .ams
  | .remark => .amsHalf

/-- One `\newtheorem`; `counter` is `none` for amsthm's unnumbered
`\newtheorem*`. -/
public structure ThmDef where
  env : String
  heading : Array Inline
  counter : Option String
  style : ThmStyle
  deriving Repr, BEq

/-- The theorem environments the preamble declared and the counters the body
steps. -/
public structure ThmDecls where
  defs : Array ThmDef := #[]
  counters : Array (String × Option Nat) := #[]
  style : ThmStyle := .kernel
  nums : Array (String × String × Nat) := #[]
  /-- How many proofs are open; a `\qedhere` outside one sets nothing. -/
  proofs : Nat := 0
  /-- The innermost proof's `\qedhere` has set its mark, so its end sets
  none. -/
  qedPlaced : Bool := false
  deriving Repr, BEq

/-- Whether amsthm is loaded. -/
private def ThmDecls.ams (d : ThmDecls) : Bool := d.style != .kernel

public structure PicCtx where
  /-- The external TeX that draws pictures outside the rendered subset;
  `none` is the declared refusal. -/
  tool : Option String := some "lualatex"
  /-- Whether an external converter may draw a figure the engine cannot draw
  whole. -/
  convert : Bool := true
  /-- Boundary requests the driver withdrew, drawn natively instead. -/
  withdrawn : Array String := #[]
  /-- The preamble lines a boundary standalone needs, as written. -/
  preamble : String := ""
  /-- The document's macro definitions for the boundary standalone. -/
  macros : Array (String × String) := #[]
  /-- The directories the document's last `\graphicspath` names. -/
  graphics : Array String := #[]
  /-- The document's `\tikzset` key lists in source order, each beside its
  line's span. -/
  sets : Array (Span × Array Raw) := #[]
  /-- How a node label's content measures at a per-mille size; the default
  answers nothing. -/
  metric : Ir.Pic.LabelMetric := fun _ _ => {}

/-- An expansion's open semantic role and the first emitted node it owns. -/
private structure MacroRun where
  origin : MacroOrigin
  start : Nat
  /-- The open paragraph began before this owner: only the next completed
  block can belong to this run. -/
  pendingPara : Bool := false

/-- Semantic names carried by the compatibility pass's executed tokens. -/
public structure MacroRoles where
  private inherited : List MacroOrigin := []
  private inlines : Array MacroRun := #[]
  private blocks : Array MacroRun := #[]
  private blockKinds : List (MacroOrigin × Bool) := []

public def MacroRoles.empty : MacroRoles := {}

private def MacroRoles.enter (roles : MacroRoles) : MacroRoles :=
  { inherited := roles.inherited ++ roles.blocks.toList.map (·.origin)
      ++ roles.inlines.toList.map (·.origin) }

private def relativeOrigins (owned actual : List MacroOrigin) : List MacroOrigin :=
  actual.filter (!owned.contains ·)

private def commonOrigins : List MacroOrigin → List MacroOrigin → Nat
  | a :: as, b :: bs => if a == b then 1 + commonOrigins as bs else 0
  | _, _ => 0

/-- Closes inner runs first; a run that owns no node wraps nothing. -/
private def closeMacroRuns (wrap : String → Array α → α)
    (acc : Array α) : List MacroRun → Array α
  | [] => acc
  | run :: rest =>
    let acc := if !run.pendingPara && run.start < acc.size then
        (acc.extract 0 run.start).push (wrap run.origin.name (acc.extract run.start acc.size))
      else acc
    closeMacroRuns wrap acc rest

private def moveMacroRuns (wrap : String → Array α → α)
    (active : Array MacroRun) (desired : List MacroOrigin) (acc : Array α)
    (pending : Bool := false) :
    Array MacroRun × Array α :=
  let keep := commonOrigins (active.toList.map (·.origin)) desired
  let acc := closeMacroRuns wrap acc (active.toList.drop keep).reverse
  let active := active.extract 0 keep ++
    (desired.drop keep).toArray.map (fun origin =>
      { origin, start := acc.size, pendingPara := pending })
  (active, acc)

/-- The lists around content as LaTeX counts them where a list opens: `\@listdepth`, each kind's
own depth, and the spacing the innermost declares. -/
public structure ListNest where
  depth : Nat := 0
  itemize : Nat := 0
  enumerate : Nat := 0
  description : Nat := 0
  set : Ir.ListSet := {}
  deriving Repr, BEq, Inhabited

/-- A list kind's own depth, as enumitem counts its levels. -/
public def ListNest.kindDepth (nest : ListNest) (kind : String) : Nat :=
  if kind == "enumerate" then nest.enumerate
  else if kind == "description" then nest.description else nest.itemize

/-- One list of `kind` deeper, its declared spacing in force. -/
public def ListNest.enter (nest : ListNest) (kind : String) (set : Ir.ListSet) : ListNest :=
  { nest with depth := nest.depth + 1, set := set
              itemize := if kind == "itemize" then nest.itemize + 1 else nest.itemize
              enumerate := if kind == "enumerate" then nest.enumerate + 1 else nest.enumerate
              description := if kind == "description" then nest.description + 1
                else nest.description }

/-- One quotation deeper: a level whose own macro sets the skips again. -/
public def ListNest.quoted (nest : ListNest) (l : Ir.ListLineage) (size : Sp) : ListNest :=
  { nest with depth := nest.depth + 1, set := Ir.ListSet.within l size (nest.depth + 1) nest.set }

/-- The elaboration context; `limit` bounds the prefix of `user` a command
sees. -/
public structure Ctx where
  file : String
  /-- The outer written call that stored replacement code is attributed to. -/
  callSite : Option (Span × String) := none
  /-- The highlighting replies the driver captured. -/
  listingReplies : Array ListingReply.Answer := #[]
  user : Array UserCmd := #[]
  limit : Nat := 0
  /-- Document-defined environments; `envLimit` bounds the visible prefix. -/
  userEnvs : Array UserEnv := #[]
  envLimit : Nat := 0
  args : Array (String × Option (Array Inline)) := #[]
  /-- Palette names usable as colour commands, from `\palette`. -/
  palette : Palette := {}
  /-- The palette in force when the body opens. -/
  basePalette : Palette := {}
  /-- The cancel package's load options: the marks every formula draws. -/
  cancel : Math.CancelSpec := {}
  /-- Where a blueprint's Lean names and discussions link, from its `\dochome` and `\github`. -/
  blueprint : Blueprint.Site := {}
  /-- The document's main locale, which generated furniture is worded in. -/
  locale : Locale := Locale.en
  /-- Named lengths from `\tokens`. -/
  tokens : Tokens := {}
  /-- The resolved page the engine length tokens resolve against. -/
  page : Ir.PageSpec := {}
  /-- The surface the main document was written in. -/
  surface : Ir.Surface := .tex
  /-- Inside raws markdown or a code file lowered, which the document's own commands and
  environments do not reach. -/
  kept : Bool := false
  /-- The class's list lineage, which a listing's frame reads. -/
  lists : Ir.ListLineage := .sizeFile
  /-- The class's preamble font, in which a length the class fixes at load is fixed. -/
  preamble : Ir.PreambleFace := Ir.PreambleFace.article
  /-- The engine's length tokens, resolved from the final page. -/
  engineTokens : Array (String × Dim.SymGlue) := #[]
  /-- Element styles declared so far (`\style`, theme bundles). -/
  styles : Styles := {}
  /-- Inside mono/verbatim content, where punctuation stays literal. -/
  literalText : Bool := false
  /-- The steps on which a conditional mono face keeps punctuation literal. -/
  literalWhen : Option OverlaySpec := none
  /-- Inside a speaker note, where a reserved character is literal text. -/
  noteBody : Bool := false
  /-- The ground a region paints under the content being elaborated. -/
  ground : Option Color := none
  /-- The frame's ground that inline code's derived colours fit to. -/
  codeGround : Option Color := none
  /-- The position of the `\note` whose body is being elaborated. -/
  notePos : Option Pos := none
  /-- Inside a user command's or environment's argument, where a reserved
  character is the caller's literal token. -/
  argBody : Bool := false
  /-- Overlay steps `\pause` opened in enclosing scopes. -/
  stepBase : Nat := 0
  slides : Bool := false
  /-- The class's ground depth for a palette generated in the body. -/
  groundDepth : GroundDepth := .documents
  /-- A frame's vertical alignment when its options name none, from beamer's
  class options `t` and `c`. -/
  frameAlign : VAlign := .center
  /-- The page model is `face`: display text with no note apparatus. -/
  face : Bool := false
  numberHeadings : Bool := false
  /-- The backends the enclosing `{ifbackend}` conditionals leave in force. -/
  backendTargets : List String := Ir.backendNames
  pic : PicCtx := {}
  /-- A definition body reads as document content, as its use will. -/
  atUse : Bool := false
  /-- The semantic ancestry of executed compatibility macros. -/
  macroRoles : MacroRoles := .empty
  /-- The lists around the content being elaborated. -/
  listNest : ListNest := {}
  /-- Whether the abstract is a quotation, and so a list level, as `article`'s is. -/
  abstractNests : Bool := false

/-- The span of `pos`, or of the written call when inside replacement code. -/
public def Ctx.sourceSpan (ctx : Ctx) (pos : Pos) : Span :=
  (ctx.callSite.map (·.1)).getD ⟨ctx.file, pos⟩

/-- Enters replacement code, keeping an enclosing written call. -/
private def Ctx.atCall (ctx : Ctx) (name : String) (pos : Pos) : Ctx :=
  { ctx with callSite := ctx.callSite.orElse (fun _ =>
      some (⟨ctx.file, pos⟩, "\\" ++ name)) }

public theorem Ctx.sourceSpan_call_projects (ctx : Ctx) (span : Span) (name : String) (pos : Pos) :
    ({ ctx with callSite := some (span, name) } : Ctx).sourceSpan pos = span := by rfl

/-- A counter's numeral style: `\arabic`, `\alph`, `\Alph`, `\roman` or
`\Roman`. -/
public inductive SecNumStyle where
  | arabic
  | alph
  | uAlph
  | roman
  | uRoman
  deriving Repr, BEq

/-- One piece of a `\the<counter>` format: literal text, a section counter's
numeral, or another level's format. -/
public inductive SecPart where
  | lit (s : String)
  | num (style : SecNumStyle) (level : Nat)
  | the (level : Nat)
  deriving Repr, BEq

/-- An algorithm2e keyword the document defines (`\SetKw` and family). -/
public inductive AlgKwDef where
  | word (body : Array Raw)
  | io (label : String)
  | func (name : Array Raw)
  | data (name : Array Raw)
  deriving Repr, BEq

/-- The algorithm2e keywords and display defaults the preamble declares. -/
public structure AlgSt where
  kws : Array (String × AlgKwDef) := #[]
  semis : Bool := true
  numbered : Bool := false
  deriving Repr, BEq

/-- The frame sources of the current block accumulator, spliced into the
document at `base`, or owned by a wrapper when `base` is `none`. -/
public structure FrameSources where
  base : Option Nat := none
  sites : Array (Nat × Span) := #[]
  /-- The next fresh accumulator's absolute offset. -/
  nextBase : Option Nat := none
  deriving Repr, BEq

public def FrameSources.offset (s : FrameSources) (n : Nat) : Option Nat :=
  s.base.map (· + n)

public def FrameSources.record (s : FrameSources) (n : Nat) (source : Span) : FrameSources :=
  match s.offset n with
  | some i => { s with sites := s.sites.push (i, source) }
  | none => s

/-- Drops the sites from offset `n` on, which a retained wrapper now owns. -/
public def FrameSources.keepPrefix (s : FrameSources) (n : Nat) : FrameSources :=
  match s.offset n with
  | some i => { s with sites := s.sites.filter (·.1 < i) }
  | none => s

/-- The spans the reporting layer reads back out of elaboration. -/
public structure SpanRecords where
  bib : Array (String × Span) := #[]
  images : Array (String × Span) := #[]
  cites : Array (String × Span) := #[]
  /-- Each colour expression's and source value's first use in its palette. -/
  colors : Array (Palette × String × Color × Bool × Span) := #[]
  /-- The declaration sites furniture and implicit foregrounds report. -/
  colorDeclarations : Array (String × Color × Bool × Span) := #[]
  /-- Each `\palette` entry that declares an author colour under the key
  `ink` or `surface`, at its first declaration. -/
  tokenKeys : Array (String × Span) := #[]
  /-- The declared `tokenKeys` some resolved colour expression spells, once
  each. -/
  colorReads : Array String := #[]
  /-- How many picture settings and macro definitions `colorReads` has read. -/
  pictureContextRead : Nat × Nat := (0, 0)
  /-- Whether `colorReads` has read the boundary preamble. -/
  picturePreambleRead : Bool := false
  /-- Boundary pictures the rendered subset draws in part, by picture id. -/
  fallbacks : Array String := #[]
  /-- Pictures drawn in part under `tool = none`, by picture id. -/
  declined : Array String := #[]
  /-- Inline code the highlighter must classify, as language and source. -/
  code : Array (String × String) := #[]
  /-- Top-level frame openings, maintained with the block accumulator. -/
  frames : FrameSources := {}
  /-- The log at the last content-recovery emission. -/
  recoveryDiags : Array Diag := #[]
  /-- The first site a document declares the frame title's font. -/
  frameTitleFont : Option Span := none
  /-- The first declared frame-title font that asks only for what the plain title sets. -/
  frameTitleRestated : Option Span := none
  /-- Each `\palette[seeds]` generation by seeds and targets, with its colours
  or its failure. -/
  seedPalettes : Array (SeedPalette.Seeds × SeedPalette.Targets ×
    Option SeedPalette.Colors × Option SeedPalette.Failure) := #[]
  /-- The roles the document declared through a role door and no theme has
  installed over since. -/
  docRoles : Array Role := #[]
  deriving Repr, BEq

/-- The headline logos: beamer's `\logo` and the `\logoleft`/`\logoright`
corner slots, the last of each winning. -/
public structure Logos where
  main : Option (Array Inline) := none
  left : Option (Array Inline) := none
  right : Option (Array Inline) := none
  deriving Repr, BEq

/-- The argument shapes a counted refusal's sites have met, as a set. -/
public structure RunShape where
  /-- Some site of this group led with a `[...]` run. -/
  withRun : Bool := false
  /-- Some site of this group led with no `[...]` run. -/
  withoutRun : Bool := false
  deriving Repr, BEq, DecidableEq

public def RunShape.add (s : RunShape) (optionRun : Bool) : RunShape :=
  if optionRun then { s with withRun := true } else { s with withoutRun := true }

public theorem runShape_fold_exact (bs : List Bool) :
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

/-- The counters the flow keeps, and the heading-number state they render
through. -/
public structure Counters where
  /-- The section counters, levels 1–3. -/
  secNums : Nat × Nat × Nat := (0, 0, 0)
  /-- LaTeX's `secnumdepth`: the deepest level a heading numbers at; 3 is
  article's. -/
  secDepth : Int := 3
  /-- The `paragraph` and `subparagraph` counters. -/
  runNums : Nat × Nat := (0, 0)
  /-- The declared heading-number format of each level, the last winning; a
  level with none takes the class default. -/
  secFmts : Array (Nat × Array SecPart) := #[]
  /-- `\appendix` was declared: headings from here on letter (`A`, `B`, …). -/
  inAppendix : Bool := false
  /-- The equation counter, restarting under the `\numberwithin` level
  `eqWithin` when one is declared. -/
  eqNum : Nat := 0
  eqWithin : Option Nat := none
  eqSnap : String := ""
  /-- The listing counter, stepped per captioned listing. -/
  lstNum : Nat := 0
  /-- The footnote counter, stepped by `Ir.footnoteMark`. -/
  fnNum : Nat := 0
  /-- Inside a bibliography field's reading, where an unoverridden
  `\footnote`'s mark is left to its list. -/
  fnDefer : Bool := false
  /-- The notes each `\bibliography` list's fields set, in document order. -/
  listNotes : Array Nat := #[]
  /-- The footnote counter where each `\bibliography` list stands. -/
  notesAt : Array Nat := #[]
  thm : ThmDecls := {}

/-- A global assignment made inside a group, which the group's end replays. -/
public inductive GlobalWrite where
  /-- A palette name set or cleared; `native` when Beamer's role state
  follows it. -/
  | entry (ref : ColorRef) (value : Option Color) (decorative : Bool) (native : Bool)
  /-- The cover fraction a body `\palette{ covered = ... }` set. -/
  | covered (fraction : Option Nat)
  /-- The generated palette a body `\palette[seeds]{...}` installed. -/
  | seeded (state : Option SeedPalette.SeedState)
  deriving Repr, BEq, Inhabited

/-- The declaration state TeX's save stack governs, and the log of global
assignments each group's end replays. -/
public structure GroupScope where
  /-- The palette in force in flow order and the named Beamer colours. -/
  palette : BeamerColor.State := {}
  /-- The language a block-level `\selectlanguage` set, `none` for the
  document's main language. -/
  lang : Option String := none
  /-- The family a `\url` sets in, from url.sty's `\urlstyle`; `none` is the
  running face. -/
  urlFamily : Option Ir.Style := some .mono
  /-- The declarations met between blocks in the enclosing scopes, outermost
  first, which wrap every inline region built under them. -/
  blockDecls : List Ir.Decl := []
  /-- Every global assignment in flow order, which a group's end keeps. -/
  globals : Array GlobalWrite := #[]
  deriving Inhabited

/-- Replays one global assignment over a restored colour state; `base` is the
palette an unset `current` stands for. -/
@[expose] public def GlobalWrite.replay (base : Palette) (s : BeamerColor.State) :
    GlobalWrite → BeamerColor.State
  | .entry ref value decorative native =>
    let pal := s.current.getD base
    let s := { s with current := some (match value with
      | some c => pal.declare ref c decorative
      | none => pal.erase ref) }
    match value, native, ref with
    | some c, true, .role r => s.native r c
    | _, _, _ => s
  | .covered fraction =>
    { s with current := some { s.current.getD base with coveredFraction := fraction } }
  | .seeded state =>
    { s with current := some { s.current.getD base with seeded := state } }

@[expose] public def GlobalWrite.movesRoles : GlobalWrite → Bool
  | .entry _ _ _ native => native
  | .covered _ => false
  | .seeded _ => false

/-- The scope a group's end leaves: the fields its start held, with the
global assignments logged since replayed over them. -/
@[expose] public def GroupScope.restore (base : Palette) (saved closed : GroupScope) :
    GroupScope :=
  let logged := closed.globals.extract saved.globals.size closed.globals.size
  let s := logged.foldl (GlobalWrite.replay base) saved.palette
  let s := if logged.any GlobalWrite.movesRoles && !s.elements.isEmpty then
      let (s, pal, _) := s.resolve (s.current.getD base)
      { s with current := some pal }
    else s
  { saved with palette := s, globals := closed.globals }

public theorem GroupScope.restore_id (base : Palette) (saved closed : GroupScope)
    (h : closed.globals = saved.globals) : saved.restore base closed = saved := by
  unfold GroupScope.restore
  rw [h]
  have hnone : saved.globals.extract saved.globals.size saved.globals.size = #[] := by
    simp only [Array.extract_eq_empty_iff]; omega
  rw [hnone]
  simp

public structure ESt where
  diags : Array Diag := #[]
  /-- Warn-once keys already fired. -/
  warnedUnknown : Array String := #[]
  /-- Per counted-refusal key: its sites' shapes and the index in `diags` of
  the line carrying the group's total. -/
  runShapes : Array (String × RunShape × Nat) := #[]
  /-- `\title`, `\subtitle`, `\author`, `\institute` and `\date`, wherever
  they appear. -/
  title : Option (Array Inline) := none
  subtitle : Option (Array Inline) := none
  author : Option (Array Inline) := none
  institute : Option (Array Inline) := none
  date : Option (Array Inline) := none
  /-- Beamer's optional short forms, read by its `\insertshort...` commands. -/
  shortTitles : List (TitleDatum × Array Inline) := []
  /-- A `\maketitle` already set the title, which LaTeX typesets once. -/
  titleDone : Bool := false
  /-- The last refused `\maketitle` redefinition's body, read again at the
  preamble's end for its title styling. -/
  refusedTitleBody : Option (Array Raw) := none
  /-- Refused size-command redefinitions' bodies, read again at the
  preamble's end for their `\@setfontsize` ladder. -/
  refusedSizeBodies : Array (String × Array Raw × Span) := #[]
  /-- Speaker-note bodies met inside inline content, which the enclosing
  frame drains to its end. -/
  pendingNotes : Array (Array Raw × Pos) := #[]
  logos : Logos := {}
  /-- Boundary picture requests by content hash, one per distinct source. -/
  pictures : Array (String × Ir.PicSrc) := #[]
  salvage : Array Ir.Recovered := #[]
  /-- The top-level block index where the deck's frame count starts over. -/
  frameRestart : Option Nat := none
  /-- What the document's own `\AtBeginSection` and `\AtBeginSubsection` declare. -/
  sectionHook : Option Ir.SectionHook := none
  subsectionHook : Option Ir.SectionHook := none
  /-- Whether a deck has set a section and a subsection, which a later hook cannot open. -/
  sectionsSeen : Bool × Bool := (false, false)
  /-- The `\bibliographystyle` name, wherever it appears. -/
  bibStyle : Option String := none
  /-- The citation setup, `none` until natbib or biblatex is loaded. -/
  citeSetup : Option (Array CiteDecl) := none
  scope : GroupScope := {}
  /-- Lengths the body declares (`\setlength` mid-document). -/
  flowTokens : Option Tokens := none
  /-- Bumped by each body declaration, so the block loop re-reads the flow
  state only when it moved. -/
  flowGen : Nat := 0
  /-- The scalar settings the document has declared, by `(decl, key)`, each
  beside its value as written. -/
  seenScalars : Array (String × String × String) := #[]
  /-- The keyed entries the document itself declared, `(decl, key)`, that no
  theme install has replaced. -/
  declaredKeys : Array (String × String) := #[]
  /-- The settings the document itself declares, each at its site, which the unused-setting
  judge reads. -/
  settings : Array UnusedSetting.Declared := #[]
  /-- The document's own colours no colour read has named yet. -/
  owedColors : Std.HashSet String := {}
  /-- The words a construct the engine refused or could not resolve spells, which still name what
  they name. -/
  mentions : Std.HashSet String := {}
  /-- The files a package or class file inputs, whose declarations are the package's. -/
  packageInputs : Array String := #[]
  /-- The declaration sites whose deletion changes an artifact otherwise, which the unused-setting
  judge skips. -/
  unjudged : Array Span := #[]
  ctr : Counters := {}
  /-- The binding of the nearest preceding numbered thing, which a `\label`
  declared here takes. -/
  refTarget : Option Ir.RefBinding := none
  /-- The label table in flow order; a key's first declaration wins. -/
  labels : Array (String × Option Ir.RefBinding) := #[]
  /-- The label table's key set. -/
  labelKeys : Std.HashSet String := {}
  /-- Every reference site with its form, judged once the label table is
  complete. -/
  refSites : Array (String × Ir.RefForm × Pos) := #[]
  spans : SpanRecords := {}
  /-- The colorants the document declared, each with its first alternate. -/
  inks : Array Ink := #[]
  alg : AlgSt := {}
  /-- The blueprint marks the innermost open statement or proof collects. -/
  blueprint : Blueprint.Scope := {}

/-- The declared title datum, empty when undeclared. -/
public def ESt.titlePart (st : ESt) : TitleDatum → Array Inline
  | .title => st.title.getD #[]
  | .subtitle => st.subtitle.getD #[]
  | .author => st.author.getD #[]
  | .institute => st.institute.getD #[]
  | .date => st.date.getD #[]

/-- A Beamer `\insert…` command's content, from the elaborated metadata. -/
public def ESt.titleInsert? (st : ESt) (name : String) : Option (Array Inline) := do
  if name.startsWith "insertshort" then
    let datum ← TitleDatum.ofName? (name.drop "insertshort".length).copy
    return (st.shortTitles.lookup datum).getD (st.titlePart datum)
  else if name.startsWith "insert" then
    let datum ← TitleDatum.ofName? (name.drop "insert".length).copy
    return st.titlePart datum
  else none

public theorem ESt.titleInsert_exact (st : ESt) (datum : TitleDatum) :
    st.titleInsert? ("insert" ++ datum.name) = some (st.titlePart datum) := by
  have hdrop : (("insert" ++ datum.name).drop "insert".length).copy = datum.name := by
    apply String.toList_injective
    simp [← String.length_toList]
  dsimp only [ESt.titleInsert?]
  rw [hdrop]
  rw [TitleDatum.ofName_name]
  have hshort : ("insert" ++ datum.name).startsWith "insertshort" = false := by
    cases datum <;> simp +decide [TitleDatum.name_exact]
  simp [hshort]

/-- The reporting state a trial elaboration starts from, every field that
indexes or dedups against `diags` reset with it. -/
public def ESt.freshReport (e : ESt) : ESt :=
  { e with
    diags := #[]
    warnedUnknown := #[]
    runShapes := #[]
    spans := { e.spans with recoveryDiags := #[] } }
/-- Where a listing body's content starts: past the option head and, for
`{minted}`, its language argument. -/
private def listingContentStart (env s : String) : Nat :=
  let afterOpt := ((Parse.listingOptHead s).map (·.2)).getD 0
  if env == "minted" then
    ((Parse.mintedLangHead s afterOpt).map (·.2)).getD afterOpt
  else afterOpt

/-- A keyval value without its one surrounding brace group, as listings
reads it. -/
private def listingVal (v : String) : String := (KeyVal.unbrace v).trimAscii.toString

public abbrev EM := StateM ESt

/-- A TeX group: its end restores its start's scope and places a
`.setPalette` after it when the palette in force changed. -/
@[expose] public def texGroup (base : Palette) (act : EM α) : EM (α × Array Block) := fun st =>
  let (a, done) := act st
  let scope := st.scope.restore base done.scope
  let restored := scope.palette.current.getD base
  let epoch := if (done.scope.palette.current.getD base).sameAs restored then #[]
    else #[Block.setPalette restored]
  ((a, epoch), { done with scope := scope, flowGen := done.flowGen + 1 })

public theorem texGroup_scope_exact (base : Palette) (act : EM α) (st : ESt) :
    ((texGroup base act).run st).2.scope = st.scope.restore base (act.run st).2.scope := rfl

public theorem texGroup_scope_id (base : Palette) (act : EM α) (st : ESt)
    (hglobal : (act.run st).2.scope.globals = st.scope.globals) :
    ((texGroup base act).run st).2.scope = st.scope := by
  rw [texGroup_scope_exact]
  exact GroupScope.restore_id base st.scope _ hglobal

public theorem texGroup_globals_exact (base : Palette) (act : EM α) (st : ESt) :
    ((texGroup base act).run st).2.scope.globals = (act.run st).2.scope.globals := rfl

/-- An inline TeX group: the same restore, with no palette epoch. -/
@[expose] public def inlineGroup (base : Palette) (act : EM α) : EM α := fun st =>
  let (a, done) := act st
  (a, { done with scope := st.scope.restore base done.scope })

public theorem inlineGroup_scope_exact (base : Palette) (act : EM α) (st : ESt) :
    ((inlineGroup base act).run st).2.scope = st.scope.restore base (act.run st).2.scope := rfl

public theorem inlineGroup_pure (base : Palette) (x : α) :
    inlineGroup base (pure x : EM α) = pure x := by
  funext st
  show (x, { st with scope := st.scope.restore base st.scope }) = (x, st)
  rw [GroupScope.restore_id base st.scope st.scope rfl]

private def logGlobal (w : GlobalWrite) : EM Unit :=
  modify fun st => { st with scope := { st.scope with globals := st.scope.globals.push w } }

private def setFrameSourceBase (base : Option Nat) : EM Unit :=
  modify fun st => { st with spans := { st.spans with
    frames := { st.spans.frames with base } } }

/-- Runs `scope` as a child accumulator whose blocks splice in at `offset`. -/
@[noinline] private def splicedFrameScope (offset : Option Nat)
    (scope : EM (Array Block)) : EM (Array Block) := do
  modify fun st => { st with spans := { st.spans with frames :=
    { st.spans.frames with nextBase := offset.bind st.spans.frames.offset } } }
  scope

private def recordFrameSource (ctx : Ctx) (pos : Pos) (offset : Nat) : EM Unit :=
  modify fun st => { st with spans := { st.spans with
    frames := st.spans.frames.record offset (ctx.sourceSpan pos) } }

private def keepFrameSourcePrefix (size : Nat) : EM Unit :=
  modify fun st => { st with spans := { st.spans with
    frames := st.spans.frames.keepPrefix size } }

/-- The diagnostic `diag` pushes, as a value. -/
private def diagOf (ctx : Ctx) (code : DiagCode) (msg : String) (pos : Option Pos)
    (help : Option String := none) (subject : Option String := none)
    (refused : Option String := none) (trigger : Option String := none)
    (recovery : Option Diag.Recovery := none) (output : Option Diag.Output := none)
    (detail : Option String := none) : Diag :=
  let trigger := if pos.isSome then (ctx.callSite.map (·.2)).orElse (fun _ => trigger)
    else trigger
  Diag.of code msg (pos.map ctx.sourceSpan) help subject refused trigger recovery output detail

private def diag (ctx : Ctx) (code : DiagCode) (msg : String) (pos : Option Pos)
    (help : Option String := none) (refused : Option String := none) : EM Unit :=
  modify fun st => { st with
    diags := st.diags.push (diagOf ctx code msg pos help (refused := refused)) }

/-- One reporting effect a preamble apply step asks for. -/
private inductive PEvent where
  | say (d : Diag)
  | scalar (decl key value : String) (pos : Pos)
  | declared (decl key : String)
  | setting (s : UnusedSetting.Setting) (pos : Pos)

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
  | .setting setting pos =>
    let package := Compat.packageFile ctx.file || st.packageInputs.contains ctx.file
    if UnusedSetting.ownSite package ctx.callSite.isSome pos then
      let st := { st with settings := st.settings.push ⟨setting, ctx.sourceSpan pos⟩ }
      match setting with
      | .color n => { st with owedColors := st.owedColors.insert n }
      | .face _ | .style _ => st
    else st

private def emitEvents (ctx : Ctx) (evs : Array PEvent) : EM Unit :=
  modify fun st => evs.foldl (applyEvent ctx) st

/-- One site of a warning delivered once per construct and counted every
time: later sites, and `demote`d ones, are notes. -/
private def warnOnceDiag (ctx : Ctx) (key : String) (code : DiagCode) (msg : String)
    (pos : Pos) (help : Option String) (demote first : Bool)
    (trigger : Option String := none) (recovery : Option Diag.Recovery := none)
    (output : Option Diag.Output := none) (detail : Option String := none) : Diag :=
  let d := diagOf ctx code msg (some pos) (if first then help else none) (subject := some key)
    (trigger := trigger) (recovery := recovery) (output := output) (detail := detail)
  if demote || !first then d.demote else d

private theorem demote_kind (d : Diag) : d.demote.kind = d.kind := by
  have h := congrArg Diag.kind (Diag.demote_record_exact d)
  exact h

private theorem demote_subject (d : Diag) : d.demote.subject = d.subject := by
  have h := congrArg Diag.subject (Diag.demote_record_exact d)
  exact h

private theorem demote_output (d : Diag) : d.demote.output = d.output := by
  have h := congrArg Diag.output (Diag.demote_record_exact d)
  exact h

private theorem warnOnceDiag_kind_exact (ctx : Ctx) (key : String) (code : DiagCode) (msg : String)
    (pos : Pos) (help : Option String) (demote first : Bool)
    (trigger : Option String := none) (recovery : Option Diag.Recovery := none)
    (output : Option Diag.Output := none) (detail : Option String := none) :
    (warnOnceDiag ctx key code msg pos help demote first trigger recovery output detail).kind = code := by
  unfold warnOnceDiag diagOf
  dsimp only
  split <;> simp only [demote_kind, Diag.of_record_exact]

private theorem warnOnceDiag_subject_exact (ctx : Ctx) (key : String) (code : DiagCode) (msg : String)
    (pos : Pos) (help : Option String) (demote first : Bool)
    (trigger : Option String := none) (recovery : Option Diag.Recovery := none)
    (output : Option Diag.Output := none) (detail : Option String := none) :
    (warnOnceDiag ctx key code msg pos help demote first trigger recovery output detail).subject = some key := by
  unfold warnOnceDiag diagOf
  dsimp only
  split <;> simp only [demote_subject, Diag.of_record_exact]

private theorem warnOnceDiag_output_exact (ctx : Ctx) (key : String) (code : DiagCode) (msg : String)
    (pos : Pos) (help : Option String) (demote first : Bool)
    (trigger : Option String := none) (recovery : Option Diag.Recovery := none)
    (output : Option Diag.Output := none) (detail : Option String := none) :
    (warnOnceDiag ctx key code msg pos help demote first trigger recovery output detail).output = output := by
  unfold warnOnceDiag diagOf
  dsimp only
  split <;> simp only [demote_output, Diag.of_record_exact]

/-- A warn-once key, suffixed by the output a loss is scoped to, if any. -/
private def warnOnceKey (key : String) : Option Diag.Output → String
  | none => key
  | some .pdf => key ++ "\npdf"
  | some .html => key ++ "\nhtml"
  | some .md => key ++ "\nmd"

/-- Records one loss site; a repeat changes presentation, not the count. -/
public def warnOnceState (ctx : Ctx) (key : String) (code : DiagCode) (msg : String)
    (pos : Pos) (help : Option String) (demote : Bool) (st : ESt)
    (trigger : Option String := none) (recovery : Option Diag.Recovery := none)
    (output : Option Diag.Output := none) (detail : Option String := none) : ESt :=
  let siteKey := warnOnceKey key output
  let first := !st.warnedUnknown.contains siteKey
  { st with
    warnedUnknown := if first then st.warnedUnknown.push siteKey else st.warnedUnknown
    diags := st.diags.push (warnOnceDiag ctx key code msg pos help demote first
      trigger recovery output detail) }

private theorem warnOnceState_diags_exact (ctx : Ctx) (key : String) (code : DiagCode) (msg : String)
    (pos : Pos) (help : Option String) (demote : Bool) (st : ESt)
    (trigger : Option String := none) (recovery : Option Diag.Recovery := none)
    (output : Option Diag.Output := none) (detail : Option String := none) :
    (warnOnceState ctx key code msg pos help demote st trigger recovery output detail).diags =
      st.diags.push (warnOnceDiag ctx key code msg pos help demote
        (!st.warnedUnknown.contains (warnOnceKey key output)) trigger recovery output detail) := by rfl

public theorem warnOnce_sites_exact (ctx : Ctx) (key : String) (code : DiagCode) (msg : String)
    (pos : Pos) (help : Option String) (demote : Bool) (st : ESt) (d : Diag)
    (trigger : Option String := none) (recovery : Option Diag.Recovery := none)
    (output : Option Diag.Output := none) (detail : Option String := none) :
    ((warnOnceState ctx key code msg pos help demote st trigger recovery output detail).diags.filter
      (Diag.sameLoss d)).size =
      (st.diags.filter (Diag.sameLoss d)).size +
        if d.kind = code ∧ d.output = output ∧ d.subject = some key then 1 else 0 := by
  have hid (first : Bool) :
      Diag.sameLoss d (warnOnceDiag ctx key code msg pos help demote first
        trigger recovery output detail) =
        decide (d.kind = code ∧ d.output = output ∧ d.subject = some key) := by
    apply Bool.eq_iff_iff.mpr
    rw [Diag.sameLoss_iff, decide_eq_true_eq,
      warnOnceDiag_kind_exact ctx key code msg pos help demote first trigger recovery output detail,
      warnOnceDiag_output_exact ctx key code msg pos help demote first trigger recovery output detail,
      warnOnceDiag_subject_exact ctx key code msg pos help demote first trigger recovery output detail]
    constructor
    · rintro ⟨⟨hc, ho⟩, hs, _⟩
      exact ⟨hc, ho, hs⟩
    · rintro ⟨hc, ho, hs⟩
      exact ⟨⟨hc, ho⟩, hs, by rw [hs]; rfl⟩
  rw [warnOnceState_diags_exact ctx key code msg pos help demote st trigger recovery output detail,
    Array.filter_push, hid]
  split <;> simp_all

private def warnOnce (ctx : Ctx) (key : String) (code : DiagCode) (msg : String) (pos : Pos)
    (help : Option String := none) (demote : Bool := false)
    (trigger : Option String := none) (recovery : Option Diag.Recovery := none)
    (output : Option Diag.Output := none) (detail : Option String := none) : EM Unit :=
  modify fun st => warnOnceState ctx key code msg pos help demote st trigger recovery output detail

/-- Records each citation key's first `\cite` span. -/
private def recordCiteSites (ctx : Ctx) (keys : List String) (pos : Pos) : EM Unit :=
  modify fun st => { st with spans := keys.foldl (fun sp k =>
    if sp.cites.any (·.1 == k) then sp
    else { sp with cites := sp.cites.push (k, ctx.sourceSpan pos) }) st.spans }

/-- Records a non-text object's census key with its first span. -/
private def recordImageSpan (ctx : Ctx) (src : String) (pos : Pos) : EM Unit :=
  modify fun st =>
    if st.spans.images.any (·.1 == src) then st
    else { st with spans :=
      { st.spans with images := st.spans.images.push (src, ctx.sourceSpan pos) } }

private def recordNativePictureSpan (ctx : Ctx) (pos : Pos) : EM Unit := do
  let k := ((← get).spans.images.filter fun e => e.1.startsWith Ir.picKeyPrefix).size
  recordImageSpan ctx (Ir.picKeyPrefix ++ toString k) pos

/-- The `\palette` keys `ink` and `surface`: author colours, named when
nothing reads them. -/
private def legacyScreenKeys : List String := ["ink", "surface"]

/-- Whether a declared colour the engine has not read yet stands: a legacy key or the document's
own. -/
private def readsOwed : EM Bool := do
  let st ← get
  return !st.owedColors.isEmpty ||
    st.spans.tokenKeys.any fun (k, _) => !st.spans.colorReads.contains k

/-- Records the owed keys among colour names the engine read. -/
private def noteColorNames (names : Array String) : EM Unit := do
  let st ← get
  let keys := st.spans.tokenKeys
  if keys.isEmpty && st.owedColors.isEmpty then return
  let reads := st.spans.colorReads
  let (more, owed) := names.foldl (init := (reads, st.owedColors)) fun (acc, owed) n =>
    if owed.contains n then (acc.push n, owed.erase n)
    else if keys.any (·.1 == n) && !acc.contains n then (acc.push n, owed)
    else (acc, owed)
  if more.size != reads.size then
    modify fun st => { st with spans := { st.spans with colorReads := more }, owedColors := owed }

/-- Records the owed colour names a resolved expression spells. -/
private def noteColorReads (expr : String) : EM Unit := do
  let st ← get
  unless st.spans.tokenKeys.isEmpty && st.owedColors.isEmpty do
    noteColorNames (Ir.colorNames expr)

/-- Records the words a construct the engine refuses or cannot resolve spells, read wherever the
document declares them. -/
private def noteMentions (src : String) : EM Unit :=
  unless src.isEmpty do
    modify fun st => { st with mentions := (Ir.colorNames src).foldl (·.insert ·) st.mentions }

private def noteDocRoles (rs : List Role) : EM Unit :=
  modify fun st =>
    let roles := rs.foldl (fun acc r => if acc.contains r then acc else acc.push r)
      st.spans.docRoles
    { st with spans := { st.spans with docRoles := roles } }

/-- Records a colour expression's first use in its palette. -/
private def recordColorSpan (ctx : Ctx) (expr : String) (c : Color) (role : Bool)
    (pos : Pos) : EM Unit := do
  noteColorReads expr
  modify fun st =>
    if st.spans.colors.any (fun (p, e, v, _, _) =>
      p == ctx.palette && e == expr && v.sameSource c) then st
    else { st with spans :=
      { st.spans with colors :=
        st.spans.colors.push (ctx.palette, expr, c, role, ctx.sourceSpan pos) } }

private def recordColorDeclaration (key : String) (c : Color) (span : Span) : EM Unit :=
  modify fun st =>
    if st.spans.colorDeclarations.any (fun (e, v, _, _) => e == key && v.sameSource c)
      then st
    else { st with spans :=
      { st.spans with colorDeclarations :=
        st.spans.colorDeclarations.push (key, c, true, span) } }

private def warnPaletteMiss (ctx : Ctx) (key : String) (pos : Pos) : EM Unit :=
  warnOnce ctx ("palette:" ++ key) .W0304
    s!"'{key}' is not in the palette; content kept uncoloured" pos
    (help := if ctx.palette.entries.isEmpty then
        "declare colours with \\palette{ name = #RRGGBB }"
      else s!"declared: {String.intercalate ", "
        (ctx.palette.entries.toList.map (·.1.key))}")

/-- The reporting site of a colour: its first use matching role, source and
palette, else its declaration. -/
public def colorSiteOf (colors : Array (Palette × String × Color × Bool × Span))
    (name : Option String) (c : Color)
    (declarations : Array (String × Color × Bool × Span) := #[])
    (palette : Option Palette := none) :
    Option (String × Span) :=
  let matchesSite := fun (e, v, role, _) =>
    v.sameSource c && match name with
      | some r => e == r
      | none => !role
  let used := colors.find? fun (p, entry) =>
    palette.all (· == p) && matchesSite entry
  (used.map fun (_, e, _, _, sp) => (e, sp)).orElse fun _ =>
    (declarations.find? matchesSite).map fun (e, _, _, sp) => (e, sp)

/-- Records a `\bibliography` list here: its span, and the footnote counter
stepped by the notes its fields set. -/
private def recordBibSpan (ctx : Ctx) (src : String) (pos : Pos) : EM Unit :=
  modify fun st =>
    let c := st.ctr
    let step := c.listNotes[c.notesAt.size]?.getD 0
    { st with spans := { st.spans with bib := st.spans.bib.push (src, ctx.sourceSpan pos) }
              ctr := { c with notesAt := c.notesAt.push c.fnNum, fnNum := c.fnNum + step } }

/-- A markdown reference list off the bridged control at `i`: its style and sources, no heading,
and the index past its two groups. -/
private def markdownBibArm (ctx : Ctx) (raws : Array Raw) (i : Nat) (pos : Pos) :
    EM { t : Nat × Option Ir.Block // i < t.1 } := do
  match raws[i + 1]?, raws[i + 2]? with
  | some (.group styleBody _), some (.group body _) =>
    let src := (rawSrc body).trimAscii.toString
    recordBibSpan ctx src pos
    pure ⟨(i + 3, some (.bibliography src (some (rawSrc styleBody).trimAscii.toString) #[])),
      by simp⟩
  | _, _ => pure ⟨(i + 1, none), by simp⟩

/-- The family a url.sty `\urlstyle` value names, `some none` for `same`'s
face in force. -/
private def urlStyleFamily? : String → Option (Option Ir.Style)
  | "tt" => some (some .mono)
  | "rm" => some (some .roman)
  | "sf" => some (some .sans)
  | "same" => some none
  | _ => none

/-- Reserved control words with the code each skip earns. -/
private def reservedCtrl : List (String × DiagCode) :=
  [("vspace", .W0329), ("noindent", .W0329),
   ("fontfallback", .W0329), ("figure", .W0307), ("pageref", .W0307)]

/-- Declarations that take a `{...}` block and are handled in the preamble. -/
public def declCtrl : List String :=
  ["page", "pdfmeta", "assert", "fonts", "palette", "tokens", "style", "output",
   "theme", "chrome", "pictures", "figures", "allow"]

/-- The only boundary tools a document may select to draw its pictures. -/
private def picTools : List String := ["lualatex"]

/-- Preamble declarations that take one inline-content group. -/
public def runningCtrl : List String := ["runninghead", "runningfoot"]

private def pageKeys : List String :=
  ["size", "width", "height", "margin", "vmargin", "hmargin",
   "textwidth", "textheight", "leading", "baselineskip", "parskip",
   "measure", "fontsize", "bleed", "hyphenate", "justify", "protrusion",
   "expansion", "numbers", "marks", "mark-gap", "mark-thickness", "linenumbers", "modulo",
   "furnituregap", "headsep", "footskip", "rule", "front-rule", "cropbox", "bleedbox", "trimbox",
   "artbox", "bottom"]

/-- The `\page` keys that declare the page's physical extent, and so claim
the page as declared. -/
private def pageGeometryKeys : List String :=
  ["size", "width", "height", "margin", "vmargin", "hmargin",
   "textwidth", "textheight", "bleed"]

private def metaKeys : List String :=
  ["title", "author", "subject", "keywords", "url", "image", "favicon",
   "language", "version", "standard", "intent", "intent-condition", "intent-info",
   "intent-registry", "intent-components", "created", "modified", "trapped"]

private def fontKeys : List String :=
  ["body", "sans", "mono", "math", "rm", "sf", "tt", "dir",
   "mathrm", "mathit", "mathbf", "mathsf", "mathtt"]

/-- Named page sizes: ISO 216's A4 and A5 at TeX's big-point rounding, and
US letter and legal. -/
private def pageSizes : List (String × (Sp × Sp)) :=
  [("letter", (pt 612, pt 792)),
   ("legal", (pt 612, pt 1008)),
   ("a4", (Dim.pt 595, Dim.pt 842)),
   ("a5", (Dim.pt 420, Dim.pt 595))]

/-- The slides stage beamer's `aspectratio=` option selects, else beamer's
default 4:3. -/
private def slidesStageOf (opts : List String) : Sp × Sp :=
  (opts.findSome? fun o => match KeyVal.entry o with
    | ("aspectratio", some v) => Ir.slidesStageNamed v
    | _ => none).getD Ir.slidesStage43

/-- The picture environments, whose body is never a paragraph's text. -/
private def reservedEnv : List String :=
  ["external", "tikzpicture", "tikzcd"]

/-- The alignment environments rendered as grids: the column model, and
whether LaTeX numbers the rows. -/
public def alignEnvs : List (String × Math.GridKind × Bool) :=
  [("align", .align, true), ("align*", .align, false),
   ("gather", .gather, true), ("gather*", .gather, false)]

/-- The display-math environments set as one centred formula, and whether
LaTeX numbers them. -/
public def displayMathEnvs : List (String × Bool) :=
  [("equation*", false), ("displaymath", false), ("equation", true)]

private def isMathEnv (name : String) : Bool :=
  (displayMathEnvs.lookup name).isSome || (alignEnvs.lookup name).isSome

/-- Title-page declarations, storable from the preamble or the body. -/
private def titleCtrls : List String :=
  ["title", "subtitle", "author", "institute", "date"]

/-- The NFSS font axes: each value with its declaration and its text-command
spelling (fntguide §2.2). -/
public def fontAxes : List (String × String × Style) :=
  [("rmfamily", "textrm", .roman), ("sffamily", "textsf", .sans),
   ("ttfamily", "texttt", .mono),
   ("mdseries", "textmd", .medium), ("bfseries", "textbf", .bold),
   ("upshape", "textup", .upright), ("itshape", "textit", .italic),
   ("slshape", "textsl", .italic), ("scshape", "textsc", .smallcaps),
   ("normalfont", "textnormal", .normal), ("em", "emph", .emph)]

public def argStyles : List (String × Style) :=
  fontAxes.map fun (_, arg, s) => (arg, s)

public def declStyles : List (String × Style) :=
  (fontAxes.map fun (decl, _, s) => (decl, s)) ++
  [("sans", .sans)] ++
  (["tiny", "scriptsize", "footnotesize", "small", "normalsize", "large",
    "Large", "LARGE", "huge", "Huge"].map fun n => (n, Style.size n))

private def fontCmdNocorr : Raw → Bool
  | .ctrl "nocorr" _ => true
  | _ => false

/-- Which edges of a text-font command's argument get ltfntcmd's
`\maybe@ic`, as `(before, after)`. -/
private def fontCmdEdges (body : List Raw) (next? : Option Raw) : Bool × Bool :=
  Ir.fontCmdEdges (· == .space) fontCmdNocorr
    (fun
      | some (.word s _) => !(s.startsWith "," || s.startsWith ".")
      | _ => true)
    body next?

/-- The argument without the top-level `\nocorr` markers ltfntcmd
consumes. -/
private def fontCmdContent (body : Array Raw) : Array Raw :=
  body.filter fun r => !fontCmdNocorr r

public def escapes : List (String × String) :=
  [("%", "%"), ("{", "{"), ("}", "}"), ("$", "$"), ("&", "&"), ("#", "#"),
   ("_", "_"), ("~", "~"), (" ", " "),
   -- TeX's control-symbol spaces, as fixed-width Unicode spaces.
   (",", "\u2009"), (":", "\u2005"), (";", "\u2004"),
   -- plain.tex: \quad 1 em, \qquad 2 em, \enspace ½ em.
   ("quad", "\u2003"), ("qquad", "\u2003\u2003"), ("enspace", "\u2002"),
   ("LaTeX", "LaTeX"), ("TeX", "TeX"), ("LaTeXe", "LaTeX2ε"),
   ("textdegree", "°"), ("texteuro", "€"),
   -- latex.ltx `\lq` and `\rq`, as lualatex sets them.
   ("lq", "‘"), ("rq", "’")]

private def blockOnly : List String :=
  ["section", "subsection", "subsubsection", "item", "documentclass", "define",
   "defineenv", "block", "framefoot", "pagebreak"]

/-- The overlay commands, whose content dims off its steps, or with `\visible` is invisible
there; `\only` only where `Compat.onlyAlternations` leaves it unread. -/
private def overlayCtrls : List String :=
  ["uncover", "visible", "only", "onslide"]

/-- An overlay command's numbered selector, invisible off its steps for `\visible`. -/
private def overlaySpecFor (name w : String) : Option Ir.OverlaySpec :=
  (Ir.overlayRange w).map fun s => { s with invisible := name == "visible" }

private def decorationCtrls : List (String × Ir.Decoration) :=
  [("underline", .underline), ("uline", .underline), ("sout", .lineThrough)]

public def builtinNames : List String :=
  ["begin", "end", "par", "define", "ifgiven", "documentclass", "textcolor",
   "ul", "varul"] ++ (decorationCtrls.map (·.1)) ++ [
   -- Spelled out, not derived from `Picture.phantomCtrl`, so the phantom coverage theorem can fail.
   "vphantom", "hphantom", "phantom"] ++
  blockOnly ++ (escapes.map (·.1)) ++ (argStyles.map (·.1)) ++
  (declStyles.map (·.1)) ++ (reservedCtrl.map (·.1)) ++ declCtrl ++
  (Lex.textSymbols.map (·.1))

/-- Built-ins a definition may never touch, whatever its body: the names the
walks' shape depends on, the underline family and `\tabularxcolumn`. -/
public def structuralNames : List String :=
  ["begin", "end", "par", "define", "ifgiven", "documentclass",
   "ul", "varul", "tabularxcolumn",
   "item", "defineenv", "block", "framefoot", "pagebreak"] ++
  (decorationCtrls.map (·.1)) ++
  (escapes.map (·.1)) ++ (reservedCtrl.map (·.1)) ++ declCtrl

/-- Built-ins the engine renders that a document may redefine; a
redefinition wins only if its body, expanded once, loses nothing. -/
public def renderedBuiltins : List String :=
  ["maketitle", "titlepage", "logo", "appendix", "note", "pause",
   "centering", "alt", "hfill", "ensuremath", "label", "ref", "eqref",
   "cref", "Cref", "crefrange", "Crefrange", "labelcref", "namecref", "nameCref",
   "paragraph", "subparagraph", "href", "link", "hyperlink", "hypertarget",
   "url", "nolinkurl", "hspace", "rule", "fontsize", "includegraphics",
   "animategraphics", "faIcon", "pagenumber", "pagecount",
   "bibliography", "bibliographystyle", "textcolor",
   "refstepcounter", "stepcounter", "addtocounter", "setcounter",
   "section", "subsection", "subsubsection",
   "vphantom", "hphantom", "phantom", "mintinline", "mint"] ++ Ir.natbibCites.map (·.1) ++
  titleCtrls ++ overlayCtrls ++ runningCtrl ++ (argStyles.map (·.1)) ++
  (declStyles.map (·.1)) ++ (Lex.textSymbols.map (·.1))

/-- The axes a phantom command reserves of its argument (plain.tex): width,
and height with depth. -/
public structure PhantomAxes where
  width : Bool
  extent : Bool
  deriving Repr, BEq, Inhabited

public def phantomAxes : List (String × PhantomAxes) :=
  [("vphantom", ⟨false, true⟩), ("hphantom", ⟨true, false⟩),
   ("phantom", ⟨true, true⟩)]

private def accentMap : Std.HashMap String Char := Std.HashMap.ofList TextSymData.accents

private def textSymbolMap : Std.HashMap String Char := Std.HashMap.ofList TextSymData.symbols

/-- The combining mark an accent command adds to its base (TU's table). -/
private def accentMarkOf (name : String) : Option Char :=
  accentMap[name]?

/-- The literal text an escape, a one-character word command (`\ss`) or a TU
text symbol splices. -/
public def escapeOf (name : String) : Option String :=
  match escapes.lookup name with
  | some lit => some lit
  | none =>
    match (Bib.charCommands.find? (·.1 == name)).map (·.2) with
    | some lit => some lit
    | none => textSymbolMap[name]?.map (String.ofList [·])

/-- The letter a command stands for as an accent's base: `\i` and `\j` are
the dotted letters, as tuenc.def composes them. -/
public def accentBase (d : String) : Option Char :=
  if d == "i" then some 'i' else if d == "j" then some 'j'
  else match (escapeOf d).map (·.toList) with
    | some [c] => some c
    | _ => none

/-- The composed text of an accent command applied to what follows, or
`none` when no precomposed scalar exists. -/
public def accentCompose (name : String) (r : Parse.Raw) : Option String := do
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

/-- Whether a phantom's argument sets only running-face characters, whose
height and depth the line already carries. -/
private def phantomBorrowsOne : Raw → Bool
  | .word _ _ | .space | .sym _ _ => true
  | .group body _ => phantomBorrowsList body.toList
  | .ctrl n _ =>
    (accentMarkOf n).isSome || (escapeOf n).isSome ||
      (Lex.textSymbols.lookup n).isSome
  | _ => false

private def phantomBorrowsList : List Raw → Bool
  | [] => true
  | r :: rest => phantomBorrowsOne r && phantomBorrowsList rest

end

private def phantomBorrows (raws : Array Raw) : Bool := phantomBorrowsList raws.toList

/-- A declaration style by name, or by a language, series or font slot marker. -/
private def declStyleOf (name : String) : Option Ir.Style :=
  match Marker.read? name with
  | some (.lang, tag) => some (.lang tag)
  | some (.series, s) => (Ir.Weight.parseSeries s).map fun (w, _) => .series w
  | some (.family, slot) => slot.toNat?.map .family
  | _ => declStyles.lookup name

/-- The block-level language switch; a switch back to the main language
clears the attribute. -/
private def flowLangUpdate (ctx : Ctx) (tag : String) (st : ESt) : ESt :=
  { st with scope := { st.scope with lang := if tag == ctx.locale.tag then none else some tag } }

/-- A paragraph, wrapped in the flow language's attribute when one is set. -/
private def paraUnder (lang : Option String) (inlines : Array Ir.Inline) : Ir.Block :=
  match lang with
  | some tag => .para (Ir.langWrap tag inlines)
  | none => .para inlines

/-- The last entry named `want` below the bound, with its index. -/
@[specialize] private def latestNamed {α : Type} (nameOf : α → String) (xs : Array α)
    (want : String) :
    Nat → Option (Nat × α)
  | 0 => none
  | k + 1 =>
    if h : k < xs.size then
      if nameOf xs[k] == want then some (k, xs[k]) else latestNamed nameOf xs want k
    else latestNamed nameOf xs want k

private theorem latestNamed_lt {α : Type} {nameOf : α → String} {xs : Array α} {want : String}
    {n k : Nat} {x : α} (h : latestNamed nameOf xs want n = some (k, x)) : k < n := by
  fun_induction latestNamed nameOf xs want n with
  | case1 => simp at h
  | case2 m hm _ => simp_all
  | case3 m _ _ ih => exact Nat.lt_succ_of_lt (ih h)
  | case4 m _ ih => exact Nat.lt_succ_of_lt (ih h)

private def lookupUser (ctx : Ctx) (name : String) : Option (Nat × UserCmd) :=
  if ctx.kept then none else latestNamed (·.name) ctx.user name ctx.limit

private theorem lookupUser_latest {ctx : Ctx} {name : String} {x : Nat × UserCmd}
    (h : lookupUser ctx name = some x) : latestNamed (·.name) ctx.user name ctx.limit = some x := by
  unfold lookupUser at h
  split at h
  · exact absurd h (by simp)
  · exact h

private theorem lookupUser_lt {ctx : Ctx} {name : String} {k : Nat}
    {cmd : UserCmd} (h : lookupUser ctx name = some (k, cmd)) : k < ctx.limit :=
  latestNamed_lt (lookupUser_latest h)

private def lookupUserEnv (ctx : Ctx) (name : String) : Option (Nat × UserEnv) :=
  if ctx.kept then none else latestNamed (·.name) ctx.userEnvs name ctx.envLimit

private theorem lookupUserEnv_lt {ctx : Ctx} {name : String} {k : Nat}
    {env : UserEnv} (h : lookupUserEnv ctx name = some (k, env)) :
    k < ctx.envLimit := by
  unfold lookupUserEnv at h
  split at h
  · exact absurd h (by simp)
  · exact latestNamed_lt h

private def isSpace : Raw → Bool
  | .space => true
  | _ => false

private def isSpaceOrPar : Raw → Bool
  | .space => true
  | .par _ => true
  | _ => false

/-- Stray content between `column`s, which flushes the columns row: neither
space nor `\hfill`, beamer's gutter glue there. -/
private def isColumnStray (r : Raw) : Bool :=
  !isSpaceOrPar r && !(r matches .ctrl "hfill" _)

/-- The index past the run of raws from `i` satisfying `p`. -/
private def spanRaws (raws : Array Raw) (i : Nat) (p : Raw → Bool) : Nat :=
  if h : i < raws.size then
    if p raws[i] then spanRaws raws (i + 1) p else i
  else i
termination_by raws.size - i

private theorem spanRaws_ge (raws : Array Raw) (i : Nat) (p : Raw → Bool) :
    i ≤ spanRaws raws i p := by
  fun_induction spanRaws raws i p <;> omega

/-- The index where the trailing run satisfying `p` starts. -/
private def spanRawsEnd (raws : Array Raw) (p : Raw → Bool) : Nat := Id.run do
  let mut b := raws.size
  for _ in [0:raws.size] do
    match raws[b - 1]? with
    | some r => if b > 0 && p r then b := b - 1 else break
    | none => break
  return b

private def trimBy (raws : Array Raw) (p : Raw → Bool) : Array Raw :=
  raws.extract (spanRaws raws 0 p) (spanRawsEnd raws p)

private def trimRaws (raws : Array Raw) : Array Raw :=
  trimBy raws isSpaceOrPar

/-- A begin code's outer edge trimmed: the edge facing the body is content,
as TeX reads it. -/
private def trimLead (raws : Array Raw) : Array Raw :=
  raws.extract (spanRaws raws 0 isSpaceOrPar) raws.size

private def trimTail (raws : Array Raw) : Array Raw :=
  raws.extract 0 (spanRawsEnd raws isSpaceOrPar)

/-- Whether a minted command in `rs` reads parameter `name` as code. -/
private def referencesParamCode (name : String) : List Raw → Bool
  | [] => false
  | .verb e s _ :: rest =>
    ((e == "mintinline" || e == "mint") && name.startsWith "a" &&
      (s.splitOn ("#" ++ (name.drop 1).toString)).length > 1) || referencesParamCode name rest
  | .group body _ :: rest => referencesParamCode name body.toList || referencesParamCode name rest
  | .env _ body _ :: rest => referencesParamCode name body.toList || referencesParamCode name rest
  | .math _ body _ :: rest => referencesParamCode name body.toList || referencesParamCode name rest
  | _ :: rest => referencesParamCode name rest
termination_by l => sizeOf l
decreasing_by raws_dec

/-- A defined environment from its halves, with the space rules
`\ignorespaces`, environ and `\ignorespacesafterend` state at its seams. -/
private def envOfHalves (name : String) (params : Array Param) (b e : Array Raw)
    (limit : Nat) : UserEnv :=
  let isCtrl (n : String) (r : Raw) : Bool := match r with
    | .ctrl m _ => m == n
    | _ => false
  let b := trimLead b
  let e := trimTail e
  let ink := spanRawsEnd b (· matches .space)
  let closing := if ink > 0 then b[ink - 1]? else none
  let environ := closing.any (isCtrl (Marker.name .environBody ""))
  let lead := environ || closing.any (isCtrl "ignorespaces")
  let params := params.map fun p => { p with code := referencesParamCode p.name (b.toList ++ e.toList) }
  { name, params, cmdLimit := limit,
    beginBody := if lead then b.extract 0 (ink - 1) else b
    endBody := e.filter (!isCtrl "ignorespacesafterend" ·)
    ignoresLead := lead, trimsTail := environ,
    ignoresAfterEnd := e.any (isCtrl "ignorespacesafterend") }

/-- Binds a user command's parameters from raws, each value kept as raws for
the math parser to read. -/
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

/-- How many of the document's definitions a formula reads: none inside raws markdown or a code
file lowered. -/
private def mathLimit (ctx : Ctx) : Nat := if ctx.kept then 0 else ctx.limit

/-- Expands `\define`d commands inside a formula's raws, right to left, each
body under only the definitions before it. -/
private def expandMathList (user : Array UserCmd) (limit : Nat)
    (args : Array (String × Array Raw)) : List Raw → Array Raw
  | [] => #[]
  | .ctrl n pos :: rest =>
    let tail := expandMathList user limit args rest
    if let some (_, sub) := args.find? (·.1 == n) then
      sub ++ tail
    else if let some source := Marker.value? .ink n then
      -- Compat's colour markers in macro bodies resolve as a direct \color.
      #[Raw.ctrl "color" pos, Raw.group #[Raw.word source pos] pos] ++ tail
    else
      match latestNamed (·.name) user n limit with
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
decreasing_by raws_dec

/-- The recovery a degraded formula's warning names: its text content, or a
placeholder when it has none. -/
private def floorWording (src : String) : String :=
  if (Ir.floorChars src).isEmpty then
    "sets as a placeholder: it has no text content"
  else "sets as its text content"

/-- Reports one parser note, prefixed by `where_` inside an alignment. -/
private def mathNote (ctx : Ctx) (note : MathParse.Note) (where_ : String)
    (pos : Pos) : EM Unit := do
  match note with
  | .ragged kind detail =>
    warnOnce ctx ("math:ragged:" ++ where_ ++ kind.key) .W0014
      (if where_.isEmpty then s!"an alignment {kind.words}" else s!"{where_}a {kind.words}") pos
      (detail := some detail)
  | .styleDropped what =>
    warnOnce ctx ("math:style:" ++ what) .W0385
      s!"{where_}{what} inside math sets in the surrounding style" pos
  | .constructFloored what =>
    warnOnce ctx ("math:contain:" ++ what) .W0389
      s!"{where_}math with {what} is not rendered yet; its content operand sets \
in its place" pos
  | .inkUsed expr c entry => recordColorSpan ctx expr c entry pos
  | .inkMissed expr => warnPaletteMiss ctx expr pos

/-- The colour expression the document's `\CancelColor` selects, if it
defines one. -/
private def cancelKey? (ctx : Ctx) : Option String :=
  (lookupUser ctx "CancelColor").bind fun (_, cmd) =>
    match (cmd.body.filter fun r => !(r matches .space)).toList with
    | [] => none
    | [.ctrl n _] =>
      some ((Marker.value? .ink n).getD n)
    | [.ctrl "color" _, .group g _] => some (rawSrc g).trimAscii.toString
    | _ => some (rawSrc cmd.body).trimAscii.toString

private def cancelColorOf (ctx : Ctx) : Except String (Option (Color × Option ColorRef)) :=
  match cancelKey? ctx with
  | none => .ok none
  | some key =>
    match ctx.palette.resolve key with
    | some c => .ok (some (c, ctx.palette.refOf? key))
    | none => .error key

/-- A formula's colour resolver and cancel marks, read through the text
path's palette. -/
private def mathEnv (ctx : Ctx) : MathParse.Env :=
  let (color, miss) := match cancelColorOf ctx with
    | .ok c => (c, none)
    | .error key => (none, some key)
  { ink := fun key => (ctx.palette.resolve key).map fun c => (c, ctx.palette.refOf? key)
    cancel := { ctx.cancel with color }
    cancelMiss := miss }

/-- Notes `\CancelColor` as read where the formula spells a cancel mark. -/
private def noteFormulaReads (ctx : Ctx) (expanded : Array Parse.Raw) : EM Unit := do
  if let some key := cancelKey? ctx then
    let names := Ir.ctrlNames (Parse.rawSrc expanded)
    if ["cancel", "bcancel", "xcancel", "cancelto"].any names.contains then
      noteColorReads key

private def sourceInline (ctx : Ctx) (pos : Pos) (inline : Inline) : Inline :=
  .located (ctx.sourceSpan pos) #[inline]

/-- W0440 for each colour expression a picture's or a formula's source spells that mixes an ink
away, and for each gradient a picture shades through an ink and another colour. -/
private def noteLostInks (ctx : Ctx) (src : String) (pos : Pos)
    (gradients : Array Gfx.Gradient := #[]) : EM Unit := do
  for (e, i) in ctx.palette.lostInkExprs src do
    modify fun st => { st with diags := st.diags.push (diagOf ctx .W0440
      s!"'{e}' mixes the ink '{i.name}' with a colour other than the paper or its own tint; \
it prints as a process colour" (some pos)
      (help := "mix an ink only with the paper, as 'name!50'; a mix of two colours is a third")
      (subject := some s!"ink:{i.name}")) }
  for g in gradients do
    if g.singleInk?.isNone then
      if let some i := g.stops.findSome? fun s => s.color.ink?.map (·.1) then
        modify fun st => { st with diags := st.diags.push (diagOf ctx .W0440
          s!"a gradient shades the ink '{i.name}' into another colour; it prints as a process \
colour" (some pos)
          (help := "shade an ink only into the paper, as 'left color=name, right color=white'")
          (subject := some s!"ink:{i.name}")) }

/-- One formula: parsed into math atoms, or kept as its text content with a
warning naming the construct it cannot model. -/
private def elabMathInline (ctx : Ctx) (display : Bool) (body : Array Parse.Raw)
    (pos : Pos) : EM Ir.Inline := do
  let expanded := expandMathList ctx.user (mathLimit ctx) #[] body.toList
  match MathParse.parseMath display expanded (mathEnv ctx) with
  | .ok (l, notes) =>
    for note in notes do
      mathNote ctx note "" pos
    noteFormulaReads ctx expanded
    noteLostInks ctx (Parse.rawSrc expanded) pos
    return sourceInline ctx pos (.formula display (Parse.rawSrc body) l)
  | .error what =>
    let src := Parse.rawSrc body
    noteMentions src
    warnOnce ctx ("math:" ++ what) .W0012
      s!"math with {what} is not rendered yet; the formula {floorWording src}" pos
    return sourceInline ctx pos (.math display src)

/-- One alignment environment (`align`, `gather`, starred or not) as one
display grid formula, or its text content when the parser cannot model it. -/
private def elabMathEnv (ctx : Ctx) (name : String) (kind : Math.GridKind)
    (numbered : Bool) (body : Array Parse.Raw) (pos : Pos) : EM Ir.Inline := do
  let expanded := expandMathList ctx.user (mathLimit ctx) #[] body.toList
  match MathParse.parseMathRows kind expanded (mathEnv ctx) with
  | .ok (l, notes) =>
    for note in notes do
      mathNote ctx note s!"'\{{name}}': " pos
    noteFormulaReads ctx expanded
    noteLostInks ctx (Parse.rawSrc expanded) pos
    if numbered then
      warnOnce ctx ("math:eqnum:" ++ name) .W0015
        s!"equation numbers are not rendered yet; '\{{name}}' sets unnumbered" pos
        (help := if (alignEnvs.lookup name).any (·.2)
          then some s!"'\{{name}*}' spells the unnumbered form, which renders the same"
          else none)
    return sourceInline ctx pos (.formula true (Parse.rawSrc body) l)
  | .error what =>
    let src := Parse.rawSrc body
    noteMentions src
    warnOnce ctx ("math:" ++ what) .W0012
      s!"math with {what} is not rendered yet; '\{{name}}' {floorWording src}" pos
    return sourceInline ctx pos (.math true src)

/-- The run an unclosed `[` owns: the spaces, words and symbols on its
command's line, and groups or math there only when `groups`. -/
private def malformedRun (raws : Array Raw) (i : Nat) (anchor : Pos)
    (groups : Bool) : Nat :=
  spanRaws raws i fun r =>
    match r with
    | .space => true
    | .word _ p | .sym _ p => p.line == anchor.line
    | .group _ p | .math _ _ p => groups && p.line == anchor.line
    | _ => false


private def allText (xs : Array Inline) : Bool :=
  Ir.foldInlines (fun ok x => ok && match x with
    | .text _ | .role _ _ | .located _ _ => true
    | _ => false) true xs

/-- A text leaf with smart punctuation unless literal, or both spellings
under a monospace selector. -/
private def punctuationInline (literal : Bool) (when? : Option OverlaySpec)
    (s : String) : Inline :=
  if literal then .text s else
  let smart := smartPunct s
  if smart == s then .text s else
  match when? with
  | some spec => .alternate spec #[.text s] #[.text smart]
  | none => .text smart

/-- A bare-word argument, carrying the macro owners a braced word would. -/
private def wordInlines (ctx : Ctx) (s : String) (pos : Pos) : Array Inline :=
  (relativeOrigins ctx.macroRoles.enter.inherited pos.origins).foldr
    (fun origin inner => #[.role origin.name inner])
    #[sourceInline ctx pos (punctuationInline ctx.literalText ctx.literalWhen s)]

/-- The literal-punctuation scope under a font modifier: the union of the
active monospace selectors. -/
private def modifierLiteral (ctx : Ctx) (style : Style) (spec : Option OverlaySpec) :
    Bool × Option OverlaySpec :=
  if style != .mono || ctx.literalText then (ctx.literalText, ctx.literalWhen) else
  match spec with
  | none => (true, ctx.literalWhen)
  | some selected => (false, some ((ctx.literalWhen.map (·.union selected)).getD selected))

private def specWord? : Raw → Option String := Compat.overlayWord?

private def modifierStyle? (name : String) : Option Style :=
  if name == Compat.alertMark true || name == Compat.alertMark false then some .bold
  else argStyles.lookup name

/-- Consumes an overlay selector at `start`, apart from ordinary arguments. -/
private def selectorHead (raws : Array Raw) (start : Nat) : Option String × Nat :=
  let j := skipSpaces raws start
  match raws[j]?.bind specWord? with
  | some w => (some w, skipSpaces raws (j + 1))
  | none => (none, j)

private theorem selectorHead_monotone (raws : Array Raw) (start : Nat) :
    start ≤ (selectorHead raws start).2 := by
  have h := skipSpaces_ge raws start
  have h' := skipSpaces_ge raws (skipSpaces raws start + 1)
  unfold selectorHead
  dsimp only
  split <;> dsimp <;> omega

/-- A selector head for `\hyperlink` and `\hypertarget` only. -/
private def linkSelectorHead (name : String) (raws : Array Raw) (start : Nat) :
    Option String × Nat :=
  if name == "hyperlink" || name == "hypertarget" then selectorHead raws start
  else (none, skipSpaces raws start)

private theorem linkSelectorHead_monotone (name : String) (raws : Array Raw) (start : Nat) :
    start ≤ (linkSelectorHead name raws start).2 := by
  unfold linkSelectorHead
  split
  · exact selectorHead_monotone raws start
  · exact skipSpaces_ge raws start

/-- A modifier's reading: alternated under its selector, else styled. -/
private def pushModifier (acc : Array Inline) (spec : Option OverlaySpec)
    (active otherwise : Array Inline) : Array Inline :=
  match spec with
  | some s => acc.push (.alternate s active otherwise)
  | none => acc ++ active

/-- Wraps non-empty content in its selector's cover. -/
private def selectedCover {α : Type} (wrap : OverlaySpec → Array α → α)
    (spec : Option OverlaySpec) (body : Array α) : Array α :=
  if body.isEmpty then #[] else
  match spec with
  | some spec => #[wrap spec body]
  | none => body

private def flushText (acc : Array Inline) (sb : String) : Array Inline :=
  if sb == "" then acc else acc.push (.text sb)

/-- Moves the open macro roles to a token's owners; a separator keeps only
the ancestry its neighbours share. -/
private def inlineMacroStep (roles : MacroRoles) (raw : Option Raw)
    (acc : Array Inline) (sb : String) (following : List MacroOrigin := []) :
    MacroRoles × Array Inline × String :=
  let active := roles.inlines.toList.map (·.origin)
  let desired := match raw with
    | none => []
    | some raw => match raw.origins? with
      | none => active.take (commonOrigins active (relativeOrigins roles.inherited following))
      | some origins => relativeOrigins roles.inherited origins
  if desired == active then (roles, acc, sb)
  else
    let (active, acc) := moveMacroRuns Inline.role roles.inlines desired (flushText acc sb)
    ({ roles with inlines := active }, acc, "")

/-- Steps the macro roles at `raws[i]`, reading the next token's owners past
a separator. -/
private def inlineMacroAt (roles : MacroRoles) (raws : Array Raw) (i : Nat)
    (acc : Array Inline) (sb : String) : MacroRoles × Array Inline × String :=
  let following := if raws[i]? matches some .space then
      ((raws[skipSpaces raws (i + 1)]?).bind Raw.origins?).getD []
    else []
  inlineMacroStep roles raws[i]? acc sb following

/-- Enters an accent operand's additional macro owners once, keeping the
accent's own. -/
private def accentOperandStep (roles : MacroRoles) (operand : Option Raw)
    (acc : Array Inline) (sb : String) : MacroRoles × Array Inline × String :=
  let origins := match operand with
    | some (.group body p) =>
      p.origins ++ relativeOrigins p.origins ((body[0]?.bind Raw.origins?).getD [])
    | _ => (operand.bind Raw.origins?).getD []
  let extra := relativeOrigins roles.enter.inherited origins
  if extra.isEmpty then (roles, acc, sb)
  else
    let desired := roles.inlines.toList.map (·.origin) ++ extra
    let (active, acc) := moveMacroRuns Inline.role roles.inlines desired (flushText acc sb)
    ({ roles with inlines := active }, acc, "")

/-- TeX's `\unskip` at a point of an inline run: the pending text, else the
run's last text, without the space it ends with. -/
private def unskipText (acc : Array Inline) (sb : String) : Array Inline :=
  if sb != "" then flushText acc sb.trimAsciiEnd.toString
  else if let some (.text s) := acc.back? then flushText acc.pop s.trimAsciiEnd.toString
  else acc

/-- The label key a text-mode `\qedhere` mark stands under until its proof
sets it; no document can spell its NUL. -/
private def qedHereKey : String := "\u0000qedhere"

/-- amsthm.sty's `\qed` in text, `\hbox{}\nobreak\hfill\quad\hbox{\qedsymbol}`,
with the mark's place (`qedHereKey`) for the symbol. -/
private def qedHereRun : Array Inline :=
  #[.strut {}, .fill, .text "\u2003", .label qedHereKey]

/-- What one `[...]` argument scan found. -/
private inductive ArgScan where
  | took (next : Nat)
  | unclosed (bpos : Pos)
  | content

/-- The index of the next `]` symbol at or past `k`, if any. -/
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

/-- Scans an optional `[...]` argument opened on `anchor`'s line: `.took` past
its `]`, `.unclosed` with the `[`'s position, else `.content`. -/
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
  next j bpos _ =>
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

/-- The raws between the brackets `scanBracketArg` took from `i` to `k`. -/
private def bracketInner (raws : Array Raw) (i k : Nat) : Array Raw :=
  raws.extract (skipSpaces raws i + 1) (k - 1)

private def bracketSrc (raws : Array Raw) (i k : Nat) : String := rawSrc (bracketInner raws i k)

/-- An environment body's opening `[...]` where LaTeX's `\@ifnextchar[` finds it: on the opening
line as `scanBracketArg` takes it, or past the space a line end makes, never a blank line, when
`admits` reads its text as the option, a bracket the option cannot read being the body's own. -/
private def scanOpeningArg (raws : Array Raw) (anchor : Pos) (admits : String → Bool) : ArgScan :=
  match scanBracketArg raws 0 anchor with
  | .took k => .took k
  | .unclosed bpos => .unclosed bpos
  | .content =>
    let j := skipSpaces raws 0
    match raws[j]?, closeBracketFrom raws (j + 1) with
    | some (.sym '[' _), some c =>
      if admits (bracketSrc raws 0 (c + 1)) then .took (c + 1) else .content
    | _, _ => .content

/-- The raws inside a complete optional `[...]` argument at `i`, if any. -/
private def bracketArgRaws? (raws : Array Raw) (i : Nat) (anchor : Pos) :
    Option (Array Raw) :=
  match scanBracketArg raws i anchor with
  | .took k => some (bracketInner raws i k)
  | _ => none

/-- A box's `[pos]`: latex.ltx's `t`, `c` and `b`, and beamer's `T` for the
top edge. -/
private def boxPosOf (src : String) : Option Ir.BoxPos :=
  match src.trimAscii.toString with
  | "t" => some .first
  | "c" => some .center
  | "b" => some .last
  | "T" => some .top
  | _ => none

private def warnUnclosed (ctx : Ctx) (after : String) (bpos : Pos) : EM Unit :=
  diag ctx .W0310 s!"'[' after {after} never closes; it is not an argument" (some bpos)
    (help := "add the matching ']'")

/-- The index of a command's `{...}` group past its optional argument, with
whether it recovered from an unclosed `[`, the malformed run, and that `[`'s
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
  next bpos _ =>
    split <;> simp <;> omega

private def skipOptArg (ctx : Ctx) (name : String) (raws : Array Raw)
    (start : Nat) (pos : Pos) : EM ({ j : Nat // start ≤ j } × Bool × Array Raw) := do
  match h : scanOptArg raws start pos with
  | (j, recovered, junk, unclosed) =>
    if let some bpos := unclosed then
      warnUnclosed ctx s!"'\\{name}'" bpos
    return (⟨j, by have := scanOptArg_ge raws start pos; rw [h] at this; exact this⟩,
      recovered, junk)

/-- Where an unknown environment's body starts past the arguments on its
`\begin` line, with an unclosed `[`'s position and the groups dropped. -/
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

/-- Names the groups an unknown wrapper's `\begin` line drops, and records what its arguments
spell. -/
private def warnDroppedArgs (ctx : Ctx) (name : String) (args : Array Raw) (dropped : Nat)
    (pos : Pos) : EM Unit := do
  noteMentions (Parse.rawSrc args)
  if dropped > 0 then
    let noun := if dropped == 1 then "group" else "groups"
    diag ctx .E0336
      s!"{dropped} \{...} {noun} on the '\\begin\{{name}}' line went with the unknown wrapper" (some pos)
      (help := "content, not an argument? put it after the '\\begin' line")

private def warnSkippedDecl (ctx : Ctx) (name : String) (pos : Pos) : EM Unit :=
  diag ctx .W0312 s!"no \{...} group after '\\{name}'; it is skipped" (some pos)
    (help := s!"write \\{name}\{...}")

/-- The index past consecutive closed `[...]` option runs opened on
`anchor`'s line, with the `[` of an unclosed one that stops the scan. -/
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

/-- The index past a skipped command's option runs and up to the given number
of `{...}` groups, with the position of an unclosed `[` that stops it. -/
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

/-- The sum of a pointwise measure over a list. -/
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

/-- The pointwise measure summed over the slice from `i`. -/
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

private theorem sliceMeas_splice {μ : α → Nat} {raws : Array α} {i : Nat}
    (h : i < raws.size) (seg : Array α) :
    sliceMeas μ (raws.extract 0 i ++ seg ++ raws.extract (i + 1) raws.size) i + μ raws[i]
      ≤ sliceMeas μ raws i + measList μ seg.toList := by
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

private theorem rawWeightList_eq (l : List Raw) :
    rawWeightList l = measList rawWeight l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [rawWeightList, measList, ih]

/-- The weight of the slice from `i`, kept over `rawWeightList` so the knot's
facts unfold it. -/
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

private theorem sliceWeight_lt (raws : Array Raw) {i j : Nat}
    (hi : i < raws.size) (hij : i < j) : sliceWeight raws j < sliceWeight raws i := by
  have h1 := sliceMeas_here rawWeight raws hi
  have h2 := sliceMeas_le rawWeight raws (show i + 1 ≤ j by omega)
  have h3 := rawWeight_pos raws[i]
  simp only [sliceWeight_eq]
  omega

private theorem elem_weight_le {raws : Array Raw} {j : Nat} {r : Raw}
    (h : raws[j]? = some r) {i : Nat} (hij : i ≤ j) :
    rawWeight r ≤ sliceWeight raws i := by
  simp only [sliceWeight_eq]; exact sliceMeas_elem_le h hij

private theorem extract_weight_le (body : Array Raw) (a b : Nat) :
    rawWeightList (body.extract a b).toList ≤ rawWeightList body.toList := by
  simp only [rawWeightList_eq]; exact measList_extract_le ..

private theorem sliceWeight_splice {raws : Array Raw} {i : Nat}
    (h : i < raws.size) {name : String} {body : Array Raw} {pos : Pos}
    (hr : raws[i] = .env name body pos) (keptFrom : Nat) :
    sliceWeight (raws.extract 0 i ++ body.extract keptFrom body.size
      ++ raws.extract (i + 1) raws.size) i < sliceWeight raws i := by
  simp only [sliceWeight_eq]
  have hs := sliceMeas_splice (μ := rawWeight) h (body.extract keptFrom body.size)
  have h2 := measList_extract_le rawWeight body keptFrom body.size
  rw [hr] at hs
  simp only [rawWeight, rawWeightList_eq] at hs
  omega

/-- The body measure `f` summed over the user commands below an index: the
bodies the walk can still expand. -/
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

private def visWeightGo (user : Array UserCmd) : Nat → Nat :=
  visGo (fun cmd => rawWeightList cmd.body.toList) user

private theorem latestNamed_mem {α : Type} {nameOf : α → String} {xs : Array α}
    {want : String} {n k : Nat} {x : α}
    (h : latestNamed nameOf xs want n = some (k, x)) : xs[k]? = some x := by
  fun_induction latestNamed nameOf xs want n with
  | case1 => simp at h
  | case2 m hm _ =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, Array.getElem?_eq_getElem hm, h.2]
  | case3 m _ _ ih => exact ih h
  | case4 m _ ih => exact ih h

private theorem visGo_expand {f : UserCmd → Nat} {ctx : Ctx} {name : String}
    {k : Nat} {cmd : UserCmd} (h : lookupUser ctx name = some (k, cmd)) :
    f cmd + visGo f ctx.user k ≤ visGo f ctx.user ctx.limit := by
  have hlt := lookupUser_lt h
  have hfound := latestNamed_mem (lookupUser_latest h)
  obtain ⟨hk, hbody⟩ := Array.getElem?_eq_some_iff.mp hfound
  have hstep : visGo f ctx.user (k + 1) = f cmd + visGo f ctx.user k := by
    simp only [visGo, hk, dite_true, hbody]
  have hmono := visGo_mono f ctx.user (show k + 1 ≤ ctx.limit by omega)
  omega

private theorem visWeight_expand {ctx : Ctx} {name : String} {k : Nat}
    {cmd : UserCmd} (h : lookupUser ctx name = some (k, cmd)) :
    rawWeightList cmd.body.toList + visWeightGo ctx.user k
      ≤ visWeightGo ctx.user ctx.limit := by
  unfold visWeightGo
  exact visGo_expand (f := fun cmd => rawWeightList cmd.body.toList) h

/-- An argument read as text, such as a URL or a palette key, with the
command's parameters substituted. -/
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

/-- Whether a paragraph break inside inline content adds a space: only where
none is already there. -/
private def needsSep (acc : Array Inline) (sb : String) : Bool :=
  if sb.isEmpty then
    match acc.back? with
    | some (.text t) => !t.endsWith " "
    | _ => true
  else !sb.endsWith " "

/-- Whether a space token adds glue: not against a space this scan already
holds, as TeX's input reader collapses a run of blanks. -/
private def spaceSeps (sb : String) : Bool := !sb.endsWith " "

/-- Records a label in the flow-ordered table and its key set together. -/
private def labelStep (st : ESt) (key : String) (target : Option Ir.RefBinding) : ESt :=
  { st with
    labels := st.labels.push (key, target)
    labelKeys := st.labelKeys.insert key }

private theorem labelStep_set_eq (st : ESt) (key k : String)
    (target : Option Ir.RefBinding)
    (h : st.labelKeys.contains k = st.labels.any (·.1 == k)) :
    (labelStep st key target).labelKeys.contains k
      = (labelStep st key target).labels.any (·.1 == k) := by
  simp only [labelStep, Std.HashSet.contains_insert, Array.any_push, h]
  exact Bool.or_comm _ _

private theorem labelKeys_set_eq_empty (k : String) :
    (∅ : Std.HashSet String).contains k
      = (#[] : Array (String × Option Ir.RefBinding)).any (·.1 == k) := by
  simp

/-- Records one `\label` binding; the first declaration of a key wins, as in
LaTeX. -/
private def recordLabel (ctx : Ctx) (key : String) (target : Option Ir.RefBinding)
    (pos : Pos) : EM Unit := do
  let st ← get
  if st.labelKeys.contains key then
    diag ctx .W0350 s!"'{key}' is already a \\label'ed key; the first wins" (some pos)
      (help := s!"one \\label\{{key}} per key: give this one its own name")
  else
    modify fun st => labelStep st key target

/-- Strips a display body's top-level `\label` keys, `\nonumber`/`\notag`,
and first `\tag{t}`/`\tag*{t}` before the math parser sees it. -/
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

/-- A rigid absolute length from source, its measures limited to those
`admits` allows. -/
private def affineLength (ctx : Ctx) (admits : Measure → Bool) (src : String) :
    Except String (Affine Measure) := do
  let e ← Decl.parseAffineLengthExprFor
    (ctx.tokens.entries ++ ctx.engineTokens) admits src
  if e.rigidAbsolute then return e
  throw "rubber and font-relative terms are not available in this length context"

/-- A table measure's length: any affine length but one that reads the text height. -/
private def tableMeasure (ctx : Ctx) (src : String) : Except String (Affine Measure) :=
  affineLength ctx (· != .textHeight) src

/-- One `p{...}` column width, resolved against the table's local measure. -/
private def colWidth (ctx : Ctx) (src : String) : Except String Ir.ColWidth :=
  .sized <$> tableMeasure ctx src

private def tableTarget (ctx : Ctx) (src : String) : Except String Ir.TableTarget :=
  .sized <$> tableMeasure ctx src

/-- An array `>{decl}`/`<{decl}` group's alignment, the last of
`\raggedright`, `\raggedleft` and `\centering`, with every other effect as a
keyed warning. -/
private def decodeColMods (g : Array Raw) :
    Option Ir.HAlign × Array (String × String × String) := Id.run do
  let mut align : Option Ir.HAlign := none
  let mut warns : Array (String × String × String) := #[]
  for r in g do
    match r with
    | .ctrl name _ =>
      match name with
      | "raggedright" => align := some .left
      | "raggedleft" => align := some .right
      | "centering" => align := some .center
      | "arraybackslash" => pure ()
      | _ =>
        warns := warns.push (s!"colmod:{name}",
          s!"column modifier '\\{name}' is not modelled; the column keeps its \
alignment", "")
    | _ =>
      unless isSpaceOrPar r do
        warns := warns.push ("colmod",
          "a column modifier is not modelled; the column keeps its alignment", "")
  return (align, warns)

/-- Parses a `tabular` column spec into its columns, the outer-pad flags, and
keyed warnings for what it does not model. -/
private def parseColSpec (ctx : Ctx) (spec : Array Raw)
    (flexTarget : Option Ir.TableTarget := none) :
    Array Ir.ColSpec × Bool × Bool × Array (String × String × String) := Id.run do
  let mut cols : Array Ir.ColSpec := #[]
  let mut padL := true
  let mut padR := true
  let mut warns : Array (String × String × String) := #[]
  let mut i : Nat := 0
  let mut pendingAlign : Option Ir.HAlign := none
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
          | 'l' | 'c' | 'r' =>
            let align := if c == 'c' then .center else if c == 'r' then .right else .left
            cols := cols.push { width := .natural, align := align }
            pendingAlign := none
          | 'X' =>
            match flexTarget with
            | some target =>
              cols := cols.push { width := .flex target, align := pendingAlign.getD .left
                                  ragged := pendingAlign.isSome }
            | none =>
              warns := warns.push ("colspec",
                "unsupported column type 'X'; set as 'l'", "load tabularx and use its environment")
              cols := cols.push { width := .natural, align := .left }
            pendingAlign := none
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
            cols := cols.push { width := width, align := pendingAlign.getD .left
                                ragged := pendingAlign.isSome }
            pendingAlign := none
          | '>' | '<' =>
            let group := if ci == last then spec[i + 1]? else none
            match group with
            | some (.group g _) =>
              tookGroup := true
              let (align, ws) := decodeColMods g
              if let some a := align then
                if c == '>' then pendingAlign := some a
                else if cols.size > 0 then
                  cols := cols.modify (cols.size - 1) fun col =>
                    if col.width matches .natural then col else { col with align := a, ragged := true }
              warns := warns ++ ws
            | _ =>
              warns := warns.push ("colspec",
                s!"unsupported column type '{c}'; set as 'l'", "")
              cols := cols.push { width := .natural, align := .left }
              pendingAlign := none
          | '@' =>
            -- `@{...}` can also lex inside a word, its group beside it.
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
              pendingAlign := none
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

/-- Trims a table cell's edge spaces, as the template's `\ignorespaces` and
`\unskip` do. -/
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

/-- A defined environment's body from `j`, its edges trimmed as the
definition declares. -/
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

private def skipStar (raws : Array Raw) (j : Nat) : Nat :=
  match raws[j]? with
  | some (.word "*" _) => skipSpaces raws (j + 1)
  | _ => j

private theorem skipStar_ge (raws : Array Raw) (j : Nat) : j ≤ skipStar raws j := by
  unfold skipStar
  split
  · have := skipSpaces_ge raws (j + 1); omega
  · omega

/-- The index past a `[short]` title and the spaces after it. -/
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

/-- The content of the `[...]` run at `j`; an unclosed run takes the rest. -/
private def bracketRunSrc (raws : Array Raw) (j : Nat) : Option (Array Raw) :=
  match raws[j]? with
  | some (.sym '[' _) =>
    match closeBracketFrom raws (j + 1) with
    | some c => some (raws.extract (j + 1) c)
    | none => some (raws.extract (j + 1) raws.size)
  | _ => none

/-- The index past the `[...]` run at `j` and the spaces after it. -/
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

/-- One citation note, the `[...]` run at `j` elaborated by `el`, with the
index past it; `none` at `j` when no bracket opens there. -/
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

/-- natbib's citation family at `i`: one node per citation group, its keys as
written and its form beside them, and the index past what was read. -/
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
      let keys := KeyVal.items (argText ctx body)
      if base.cmd == .nocite then
        -- `\@bsphack`/`\@esphack`: a space before swallows the spaces after.
        let j4 := skipSpaces raws (j3 + 1)
        have hj4 := skipSpaces_ge raws (j3 + 1)
        return (#[.cite form keys],
          if raws[i - 1]? matches some .space then ⟨j4, by omega⟩ else ⟨j3 + 1, by omega⟩)
      -- Judged in elabDoc: the `\bibliography` may follow the citation.
      recordCiteSites ctx keys.toList pos
      return (#[.cite form keys], ⟨j3 + 1, by omega⟩)
  | _ =>
    diag ctx .E0304 s!"'\\{name}' needs a \{keys} group" pos
    return (#[], ⟨j3, by omega⟩)

mutual
/-- Smart punctuation over this level's text, descending only through roles
and spans: other bodies carry their own literal setting. -/
-- conserves: none — smart punctuation changes the text's scalar sequence.
private def mapSmartText (when? : Option OverlaySpec) : Inline → Inline
  | .text t => punctuationInline false when? t
  | .role name inner => .role name (mapSmartTextList when? #[] inner.toList)
  | .located source inner => .located source (mapSmartTextList when? #[] inner.toList)
  | x@(.math ..) | x@(.formula ..) | x@(.styled ..)
  | x@(.colored ..) | x@(.link ..) | x@(.label ..) | x@(.ref ..)
  | x@(.decorated ..) | x@(.fill) | x@(.hspace ..) | x@(.rule ..)
  | x@(.pageNumber) | x@(.pageCount) | x@(.linebreak ..) | x@(.strut ..)
  | x@(.italicCorr ..) | x@(.onSteps ..) | x@(.altSteps ..)
  | x@(.image ..) | x@(.icon ..) | x@(.cite ..) | x@(.cited ..) | x@(.footnote ..) => x

private def mapSmartTextList (when? : Option OverlaySpec) (acc : Array Inline) :
    List Inline → Array Inline
  | [] => acc
  | x :: xs => mapSmartTextList when? (acc.push (mapSmartText when? x)) xs
end

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

/-- The first register operation in a length that the affine grammar does not
model, if any. -/
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

/-- One `\fontsize` argument as a rigid dimension, a bare decimal read in `pt`
as NFSS reads it. -/
private def fontDim (ctx : Ctx) (src : String) : Except String (Affine Measure) := do
  let trimmed := src.trimAscii.toString
  let src := if (Decl.parseDecimal trimmed).isSome then trimmed ++ "pt" else trimmed
  let e ← Decl.parseAffineLengthExpr (ctx.tokens.entries ++ ctx.engineTokens) src
  if e.rigid then return e
  throw "rubber is not a font dimension"

/-- Decodes a `\fontsize` marker's value into one typed size declaration. -/
private def readFontSizeStyle (ctx : Ctx) (spec : String) (pos : Pos) :
    EM (Option Style) := do
  match Marker.fontSizeParts spec with
  | some (sizeSrc, leadingSrc) =>
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
  | none =>
    diag ctx .E0331 "cannot read the affine dimensions in '\\fontsize'" pos
    return none

/-- An `\hspace` argument as affine glue, its fill stretch one fill. -/
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

/-- One blueprint command at `raws[i]`: its mark on the innermost open statement or proof and its
references' sites recorded, and after `\uses` and `\proves` the spaces their print macros ignore
skipped; outside a statement or proof it marks nothing and is named. -/
private def blueprintMarkArm (ctx : Ctx) (raws : Array Raw) (i : Nat) (m : Blueprint.Mark)
    (pos : Pos) : EM { j : Nat // i < j } := do
  let j0 := skipSpaces raws (i + 1)
  have hj0 := skipSpaces_ge raws (i + 1)
  let mut arg := ""
  let mut next : { j : Nat // i < j } := ⟨i + 1, by omega⟩
  if m.takesGroup then
    match raws[j0]? with
    | some (.group g _) =>
      arg := argText ctx g
      next := ⟨j0 + 1, by omega⟩
    | _ =>
      diag ctx .E0304 s!"'\\{m.name}' needs a \{...} group" pos
      return next
  let ⟨j, hj⟩ := next
  let scope := (← get).blueprint
  if scope.inside then
    let sites := (m.keys arg).map fun k => (k, Ir.RefForm.headed, pos)
    modify fun st => { st with blueprint := { scope with marks := scope.marks.mark m arg }
                               refSites := st.refSites ++ sites }
    -- premise: blueprintChecks — a name a template cannot fill is set unlinked
    if m == .lean && !ctx.blueprint.unfilled.isEmpty then
      warnOnce ctx "blueprint:link" .W0436
        "the link template names a part a Lean name alone cannot fill; its names are set without links"
        pos (help := "name only `{name}` in the template, or declare '\\dochome'")
        (output := some .html) (detail := some s!"it names {", ".intercalate ctx.blueprint.unfilled}")
  else
    warnOnce ctx ("blueprint:outside:" ++ m.name) .W0387
      s!"'\\{m.name}' stands outside any statement or proof, so it marks nothing" pos
      (help := "move it into the statement or proof it marks, after its '\\begin'")
  if m.ignoresSpaces then
    return ⟨skipSpaces raws j, Nat.lt_of_lt_of_le hj (skipSpaces_ge raws j)⟩
  return ⟨j, hj⟩

/-- Whether the blueprint marks are the package's: loaded, or named by a definition of the
document's, as a blueprint's print macros define them. -/
private def blueprintMarksOn (ctx : Ctx) : Bool :=
  ctx.blueprint.loaded || Blueprint.Mark.all.any fun m => (lookupUser ctx m.name).isSome

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

/-- An image dimension through the shared affine parser, every local measure
carried to layout. -/
private def imageLenOf (ctx : Ctx) (v : String) : Except String Image.Len := do
  let e ← affineLength ctx (fun _ => true) v
  return ⟨e⟩

/-- The text of an `alt={...}` value, braced or quoted. -/
private def altValueText (v : String) : String :=
  if v.startsWith "{" && v.endsWith "}" && v.length ≥ 2 then
    String.ofList (v.toList.drop 1).dropLast
  else if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then
    String.ofList (v.toList.drop 1).dropLast
  else v

/-- An image's settings, with its ignored and refused animation keys
collected for one diagnostic. -/
private structure ImageOptions where
  spec : Image.Spec := {}
  alt : Ir.Alt := .undeclared
  ignored : Array String := #[]
  refused : Array String := #[]
  valid : Bool := true

/-- Reads graphicx's size keys and one-based `page`, and animate's zero-based
`poster` frame. -/
private def readImageOpts (ctx : Ctx) (optSrc : Option (Array Raw))
    (pos : Pos) (animated : Bool) : EM ImageOptions := do
  let mut spec : Image.Spec := { animated }
  let mut alt : Ir.Alt := .undeclared
  let mut ignored : Array String := #[]
  let mut refused : Array (String × String) := #[]
  -- A repeated key keeps its last value, so only its last error counts.
  let mut pageErr : Option String := none
  let mut posterErr : Option String := none
  if let some src := optSrc then
    for e in Decl.splitEntries (rawSrc src) do
      if let some (key, _) := Decl.splitEntry e then
        refused := refused.filter (·.1 != key)
      match Decl.splitEntry e with
      | some ("width", v) =>
        match imageLenOf ctx v with
        | .ok l => spec := { spec with width := some l }
        | .error _ =>
          diag ctx .E0331 s!"cannot read a length from '{v}'" pos
            (help := "image sizes look like 3cm or 0.8\\textwidth")
      | some ("height", v) | some ("totalheight", v) =>
        -- An image has no depth, so totalheight is its height.
        match imageLenOf ctx v with
        | .ok l => spec := { spec with height := some l }
        | .error _ =>
          diag ctx .E0331 s!"cannot read a length from '{v}'" pos
            (help := "image sizes look like 3cm or 0.3\\textheight")
      | some ("scale", v) =>
        match Decl.parseDecimal v with
        | some (m, sc) => spec := { spec with scaleNum := m, scaleDen := sc }
        | none => diag ctx .E0321 s!"'scale' needs a number, got {v.quote}" pos
      | some ("keepaspectratio", v) =>
        match listingVal v with
        | "true" => spec := { spec with keepAspect := true }
        | "false" => spec := { spec with keepAspect := false }
        | _ =>
          diag ctx .E0321 s!"'keepaspectratio' needs true or false, got {v.quote}" pos
      | some ("page", v) =>
        if animated then
          ignored := ignored.push e
        else
          match (listingVal v).toNat? with
          | some (n + 1) => spec := { spec with page := .number (n + 1) }; pageErr := none
          | _ =>
            pageErr := some
              s!"'\\includegraphics' page needs a positive one-based integer, got {v.quote}"
      | some ("poster", v) =>
        if animated then
          match listingVal v with
          | "first" => spec := { spec with page := .first }; posterErr := none
          | "last" => spec := { spec with page := .last }; posterErr := none
          | "none" =>
            refused := refused.push ("poster", "'poster=none' has no static PDF poster")
            posterErr := none
          | n =>
            match n.toNat? with
            | some n => spec := { spec with page := .number (n + 1) }; posterErr := none
            | none =>
              posterErr := some
                s!"'\\animategraphics' poster needs first, last, none, or a zero-based integer, got {v.quote}"
        else
          ignored := ignored.push e
      | some ("every", v) =>
        if animated then
          unless (listingVal v).toNat? == some 1 do
            refused := refused.push ("every", s!"'{e}' changes the frame sequence")
        else
          ignored := ignored.push e
      | some ("timeline", _) =>
        if animated then
          refused := refused.push ("timeline", s!"'{e}' changes the frame sequence")
        else
          ignored := ignored.push e
      | some ("type", v) =>
        if animated then
          unless listingVal v == "pdf" || (listingVal v).isEmpty do
            refused := refused.push
              ("type", s!"'{e}' selects a source other than a multipage PDF")
        else
          ignored := ignored.push e
      | some ("alt", v) =>
        alt := Ir.Alt.declare (altValueText v)
      | _ =>
        if e.trimAscii.toString == "keepaspectratio" then
          spec := { spec with keepAspect := true }
        else if animated && e.trimAscii.toString == "poster" then
          refused := refused.filter (·.1 != "poster")
          spec := { spec with page := .first }
          posterErr := none
        else if e.trimAscii.toString == "artifact" ||
            (Decl.splitEntry e).any (·.1 == "artifact") then
          -- latex-lab-graphic's decoration key; its value is ignored.
          alt := .decorative
        else
          ignored := ignored.push e
  if let some msg := pageErr then diag ctx .E0321 msg pos
  if let some msg := posterErr then diag ctx .E0321 msg pos
  let valid := pageErr.isNone && posterErr.isNone
  unless animated do
    for e in ignored do
      warnOnce ctx ("imgopt:" ++ e) .W0110
        s!"'\\includegraphics' option '{e}' is not modelled; ignored" pos
        (help := "modelled keys: page, width, height, totalheight, scale, keepaspectratio, alt, artifact")
  return { spec, alt, ignored, refused := refused.map (·.2), valid }

/-- Reads up to the given number of mandatory groups, stopping at the first
non-group. -/
private def imageGroups (raws : Array Raw) (start : Nat) :
    Nat → Array (Array Raw) × { j : Nat // start ≤ j }
  | 0 => (#[], ⟨start, Nat.le_refl _⟩)
  | n + 1 =>
    let j := skipSpaces raws start
    have hj := skipSpaces_ge raws start
    match raws[j]? with
    | some (.group arg _) =>
      let (args, ⟨k, hk⟩) := imageGroups raws (j + 1) n
      (#[arg] ++ args, ⟨k, by omega⟩)
    | _ => (#[], ⟨j, hj⟩)

/-- `\includegraphics` and `\animategraphics`; an animation ships its static
poster with its playback named as lost. -/
private def imageArm (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (pos : Pos) (animated : Bool) :
    EM (Option Inline × { j : Nat // i < j }) := do
  let j0 := skipSpaces raws (i + 1)
  have hj0 := skipSpaces_ge raws (i + 1)
  let optSrc := bracketRunSrc raws j0
  let j1 := skipBracketRun raws j0
  have hj1 := skipBracketRun_ge raws j0
  let arity := if animated then 4 else 1
  let (args, ⟨j, hj⟩) := imageGroups raws j1 arity
  let next : { j : Nat // i < j } := ⟨j, by omega⟩
  if args.size != arity then
    diag ctx .E0304 (if animated then
      "'\\animategraphics' needs {fps}{basename}{first}{last} groups" else
      "'\\includegraphics' needs a {file} group") pos
    return (none, next)
  let opts ← readImageOpts ctx optSrc pos animated
  if !opts.valid then return (none, next)
  if animated then
    let mut refused := opts.refused
    let first := (argText ctx (args.getD 2 #[])).trimAscii.toString
    let last := (argText ctx (args.getD 3 #[])).trimAscii.toString
    if !first.isEmpty || !last.isEmpty then
      refused := refused.push
        "nonempty first/last ranges and numbered file sequences are not supported"
    unless refused.isEmpty do
      let why := String.intercalate "; " refused.toList
      warnOnce ctx "animategraphics:source" .W0307
        s!"'\\animategraphics' is not rendered: {why}" pos
        (help := "use a multipage PDF with empty first/last groups and poster=first, last, or a zero-based frame number")
      return (none, next)
    let fps := argText ctx (args.getD 0 #[])
    let ignored := if opts.ignored.isEmpty then "" else
      "; options " ++ String.intercalate ", " opts.ignored.toList
    warnOnce ctx "animategraphics:playback" .W0110
      "animation playback is unavailable" pos
      (trigger := "\\animategraphics")
      (recovery := some (.replacedBy "the selected static poster")) (output := some .pdf)
    warnOnce ctx "animategraphics:playback" .W0110
      s!"unsupported playback settings: frame rate '{fps}'{ignored}" pos
      (help := "set timing and playback behavior in the SVG")
      (trigger := "\\animategraphics") (recovery := some .ignored) (output := some .html)
  let src := argText ctx (args.getD (if animated then 1 else 0) #[])
  recordImageSpan ctx src pos
  return (some (.image src opts.spec opts.alt), next)

/-- `\\faIcon`'s option run: only `label = ...` is modelled, overriding the
icon's default text alternative. -/
private def readIconLabel (ctx : Ctx) (labelSrc : Option (Array Raw))
    (pos : Pos) : EM (Option String) := do
  let mut label : Option String := none
  if let some optSrc := labelSrc then
    for e in KeyVal.items (rawSrc optSrc) do
      match KeyVal.pair? e with
      | some ("label", v) =>
        if v.trimAscii.isEmpty then
          warnOnce ctx ("faopt:" ++ e) .W0110
            s!"'\\faIcon' option '{e}' is blank; the icon keeps its own text alternative" pos
        else label := some v
      | _ =>
        warnOnce ctx ("faopt:" ++ e) .W0110
          s!"'\\faIcon' option '{e.trimAscii.toString}' is not modelled; ignored" pos
          (help := "the face that renders an icon is whichever declared or installed face covers its scalar; 'label = ...' overrides the icon's text alternative")
  return label

/-- Discharges the knot's termination goals by navigating the lexicographic
tuple to the component the `have` beside each call decreases. -/
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

/-- The heading level of a block heading control, independent of the section
counters. -/
private def blockHeading? : String → Option Ir.HeadingLevel
  | "section" => some .h2
  | "subsection" => some .h3
  | "subsubsection" => some .h4
  | n => Parse.headingControl? n

seal blockHeading?

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

/-- classes.dtx's default heading number: `\arabic{section}`, `\Alph` after
`\appendix`, each deeper level prefixed by its parent. -/
private def defaultSecNum (nums : Nat × Nat × Nat) (inApp : Bool)
    (level : Nat) : String :=
  let (n1, n2, n3) := nums
  let base := if inApp then ListMark.AlphN n1 else ListMark.arabicN n1
  match level with
  | 1 => base
  | 2 => s!"{base}.{n2}"
  | _ => s!"{base}.{n2}.{n3}"

private theorem defaultSecNum_appendix_inj (m n : Nat × Nat × Nat)
    (h : defaultSecNum m true 1 = defaultSecNum n true 1) : m.1 = n.1 :=
  match m, n with
  | (_, _, _), (_, _, _) => ListMark.letterN_inj (.inr rfl) h

mutual
/-- One level's heading number: its last declared format, else the class
default; an exhausted `fuel` gives the bare arabic value. -/
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

/-- Three section levels chain through each other at most once each. -/
private def secFmtFuel : Nat := 3

/-- A definition body as a heading-number format (words, spaces, numerals
over section counters, `\the<level>` references), or `none`. -/
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

/-- A parameterless `\the<section counter>` definition whose body reads as a
heading-number format. -/
private def secFmtDefine? (cmd : UserCmd) : Option (Nat × Array SecPart) :=
  if !cmd.params.isEmpty then none
  else (theCounterLevel? cmd.name).bind fun lvl =>
    (secFmtOfBody cmd.body).map ((lvl, ·))

/-- Declares one level's heading-number format, in flow scope. -/
private def applySecFmt (lvl : Nat) (parts : Array SecPart) : EM Unit :=
  modify fun st =>
    { st with ctr := { st.ctr with
        secFmts := Ir.redeclare st.ctr.secFmts lvl parts } }

private def counterCtrl (n : String) : Bool :=
  n == "refstepcounter" || n == "stepcounter"
    || n == "addtocounter" || n == "setcounter"

/-- Applies a counter command to a section counter as ltcounts.dtx does: a
step zeroes the levels below, `\refstepcounter` also sets the `\ref` target,
and a negative result clamps to zero. -/
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
    -- A bare counter step numbers no node, so its label is kindless.
    modify fun st => { st with refTarget := some { kind := none, num := num } }

/-- The reader and writer of each non-section counter the flow keeps. -/
private def flowCounter? (ctr : String) :
    Option ((Counters → Int) × (Counters → Int → Counters)) :=
  match ctr with
  | "secnumdepth" => some (fun c => c.secDepth, fun c v => { c with secDepth := v })
  | "footnote" => some (fun c => c.fnNum, fun c v => { c with fnNum := v.toNat })
  | "equation" => some (fun c => c.eqNum, fun c v => { c with eqNum := v.toNat })
  | _ => none

/-- Sets, adds to or steps a flow counter; `secnumdepth` alone may go below
zero. -/
private def applyFlowCounter (name : String)
    (rw : (Counters → Int) × (Counters → Int → Counters)) (n : Int) : EM Unit :=
  modify fun st => { st with
    ctr := rw.2 st.ctr (match name with
      | "setcounter" => n
      | "addtocounter" => rw.1 st.ctr + n
      | _ => rw.1 st.ctr + 1) }

/-- A counter command's integer argument: a value, a counter the flow does
not keep, or source text no reading reaches. -/
private inductive CounterArg where
  | int (v : Int)
  | unkept (c : String)
  | unread (shown : String)

/-- The plain.tex integer constants a counter value may name. -/
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

/-- One counter command from `i`: applied to a kept counter, otherwise
named and its arguments consumed; returns the index past them. -/
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

/-- A `\paragraph` or `\subparagraph` title: bold, after its number when
`secnumdepth` reaches its level. -/
private def runInHead (ctx : Ctx) (name : String) (starred : Bool) (title : Array Inline) :
    EM Inline := do
  let st ← get
  let level : Int := if name == "paragraph" then 4 else 5
  -- premise: counterChecks — numbered only within secnumdepth
  if starred || !ctx.numberHeadings || level > st.ctr.secDepth then
    return .styled .bold title
  let (n4, n5) := st.ctr.runNums
  let runs := if level == 4 then (n4 + 1, 0) else (n4, n5 + 1)
  let parent := renderSecLevel st.ctr.secFmts st.ctr.secNums st.ctr.inAppendix secFmtFuel 3
  let num := if level == 4 then s!"{parent}.{runs.1}" else s!"{parent}.{runs.1}.{runs.2}"
  modify fun st => { st with ctr := { st.ctr with runNums := runs }
                             refTarget := some { kind := some .heading, num := num } }
  return .styled .bold (#[.text (num ++ "\u2003")] ++ title)

/-- The number in `\footnote[num]`'s bracket, or `none` when there is none
or it is not a number. -/
private def footnoteOverride (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (pos : Pos) : Option Nat :=
  match scanBracketArg raws i pos with
  | .took k => (argText ctx (bracketInner raws i k)).trimAscii.toString.toNat?
  | _ => none

private def hasParRaw (body : Array Raw) : Bool :=
  body.any (fun r => r matches .par _)

private def footnoteWarnPar (ctx : Ctx) (pos : Pos) : EM Unit :=
  warnOnce ctx "footnote:par" .W0371
    "a paragraph break inside '\\footnote' is set as a space" pos
    (help := "a footnote is one paragraph; split a long note into \
two \\footnote calls")

private def footnoteWarnFace (ctx : Ctx) (pos : Pos) : EM Unit :=
  warnOnce ctx "footnote:face" .W0374
    "a footnote on this card is kept inline; a card face has no \
note apparatus" pos
    (help := "write the aside in the running text, or declare \
\\documentclass{article} to give notes a page foot")

private def thanksWarn (ctx : Ctx) (pos : Pos) : EM Unit :=
  warnOnce ctx "ctrl:thanks" .W0373
    "'\\thanks' content is kept inline in the title block" pos
    (help := "a plain \\footnote in the body text renders as a page footnote")

/-- Steps the footnote counter and returns the mark's number; an override or
a deferred mark steps nothing, and a deferred one returns `none`. -/
private def footnoteStepNum (override : Option Nat) : EM (Option Nat) := do
  let c := (← get).ctr
  if override.isNone && c.fnDefer then return none
  let (num, fn) := Ir.footnoteMark c.fnNum override
  modify fun st => { st with ctr := { st.ctr with fnNum := fn } }
  return some num

private def noteNeedsGroup (ctx : Ctx) (name : String) (pos : Pos) : EM Unit :=
  diag ctx .E0304 s!"'\\{name}' needs a \{...} group" pos

/-- A refusal's recovery clause, led by the fate of a dropped `[...]` run. -/
private def optionRunClause (optionRun : Bool) (kept : String) : String :=
  if optionRun then s!"its [...] options were dropped and {kept}" else kept

/-- The recovery clause for a group of sites, true of every site it counts. -/
private def RunShape.clause (s : RunShape) (kept : String) : String :=
  if !s.withRun then kept
  else if !s.withoutRun then optionRunClause true kept
  else s!"any [...] options were dropped and {kept}"

/-- The help a dropped `[...]` run appends to its refusal's own help. -/
private def optionRunAdvice (optionRun : Bool) : String :=
  if optionRun then "; content, not options? start the '[' on the next line" else ""

/-- ragged2e's alignment declarations (manual §2), which change nothing. -/
private def raggedTwoE : List String :=
  ["justifying", "RaggedRight", "RaggedLeft", "Centering"]

/-- An unknown command's help: the native key where the construct's purpose
is known, else the `\define` route. -/
private def unknownCmdHelp (name : String) (optionRun : Bool) : String :=
  let route :=
    if name == "AddToHook" || name == "AddToHookNext" then
      "a hook body cannot be interpreted; \\page{ marks = cut } declares \
printer's cut marks, derived from the trim and bleed"
    else if raggedTwoE.contains name then
      "the text keeps its page's own setting; \\page{ justify = on } or \
\\page{ justify = off } sets the whole document's"
    else "\\define \\name(...) {body} declares it"
  s!"{route}{optionRunAdvice optionRun}"

/-- The code, message and help a refused command earns for a site shape. -/
public def unknownCmdDiag (name : String) (shape : RunShape) :
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

private def RunShape.one (optionRun : Bool) : RunShape := ({} : RunShape).add optionRun

/-- Rewords the diagnostic at `idx` to the group's widened shape. -/
private def runShapeReword (name : String) (new : RunShape) (idx : Nat)
    (ds : Array Diag) : Array Diag :=
  let (_, msg, help) := unknownCmdDiag name new
  match ds[idx]? with
  | none => ds
  | some d => ds.setIfInBounds idx
      { d with message := msg, help := d.help.map fun _ => help }

private theorem runShapeReword_size_exact (name : String) (new : RunShape) (idx : Nat)
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
      runShapes := Ir.redeclare st.runShapes key (new, idx)
      diags := if new == old then st.diags else runShapeReword name new idx st.diags }

private theorem bumpRunShape_size_exact (name key : String) (optionRun : Bool) (st : ESt) :
    (bumpRunShape name key optionRun st).diags.size = st.diags.size := by
  unfold bumpRunShape
  split
  · rfl
  · dsimp only
    split <;> simp [runShapeReword_size_exact]

/-- Records an unknown command's refusal and its site shape. -/
private def warnUnknownCmd (ctx : Ctx) (name : String) (optionRun : Bool)
    (pos : Pos) : EM Unit :=
  let key := "ctrl:" ++ name
  let (code, msg, help) := unknownCmdDiag name (RunShape.one optionRun)
  modify fun st =>
    let emitted := warnOnceState ctx key code msg pos help
      (code == .W0301 && Compat.styInternal ctx.file name)
      (bumpRunShape name key optionRun st)
    { emitted with spans := { emitted.spans with recoveryDiags := emitted.diags } }

private theorem warnUnknownCmd_recovery_exact (ctx : Ctx) (name : String) (optionRun : Bool)
    (pos : Pos) (st : ESt) :
    ((warnUnknownCmd ctx name optionRun pos).run st).2.spans.recoveryDiags =
      ((warnUnknownCmd ctx name optionRun pos).run st).2.diags := by rfl

/-- The index past up to `n` `{...}` groups, each after any spaces; spaces
after the last group stay. -/
private def argGroupsEnd (raws : Array Raw) (j : Nat) : Nat → Nat
  | 0 => j
  | n + 1 =>
    let k := skipSpaces raws j
    match raws[k]? with
    | some (.group _ _) => argGroupsEnd raws (k + 1) n
    | _ => j

private theorem argGroupsEnd_ge (raws : Array Raw) (j n : Nat) : j ≤ argGroupsEnd raws j n := by
  induction n generalizing j with
  | zero => simp [argGroupsEnd]
  | succ n ih =>
    simp only [argGroupsEnd]
    split
    · have h1 := skipSpaces_ge raws j
      have h2 := ih (skipSpaces raws j + 1)
      omega
    · omega

public def groupAt (raws : Array Raw) (m : Nat) : Bool :=
  match raws[m]? with
  | some (.group _ _) => true
  | _ => false

public def spaceOrGroupAt (raws : Array Raw) (m : Nat) : Bool :=
  match raws[m]? with
  | some .space | some (.group _ _) => true
  | _ => false

/-- How many `{...}` groups stand among the `len` raws from `j`. -/
public def groupsIn (raws : Array Raw) (j : Nat) : Nat → Nat
  | 0 => 0
  | len + 1 => (if groupAt raws j then 1 else 0) + groupsIn raws (j + 1) len

private theorem skipSpaces_spaces (raws : Array Raw) (i : Nat) :
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

private theorem groupsIn_add (raws : Array Raw) (j a b : Nat) :
    groupsIn raws j (a + b) = groupsIn raws j a + groupsIn raws (j + a) b := by
  induction a generalizing j with
  | zero => simp [groupsIn]
  | succ a ih =>
    rw [Nat.succ_add, groupsIn, groupsIn, ih (j + 1)]
    have : j + 1 + a = j + (a + 1) := by omega
    rw [this]
    omega

private theorem groupsIn_spaces (raws : Array Raw) (j len : Nat)
    (h : ∀ m, j ≤ m → m < j + len → raws[m]? = some .space) : groupsIn raws j len = 0 := by
  induction len generalizing j with
  | zero => rfl
  | succ len ih =>
    have hj : groupAt raws j = false := by
      unfold groupAt
      rw [h j (by omega) (by omega)]
    rw [groupsIn, hj, ih (j + 1) (fun m h1 h2 => h m (by omega) (by omega))]
    rfl

private theorem groupsIn_one (raws : Array Raw) (j : Nat) :
    groupsIn raws j 1 = if groupAt raws j then 1 else 0 := by rfl

/-- The index passes only spaces and at most `n` groups, and stops short of
`n` only where no group follows. -/
private theorem argGroupsEnd_covers (raws : Array Raw) (j n : Nat) :
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

/-- The warn-once key of an unknown LaTeX internal in package code. -/
public def pkgCodeKey (name : String) : String := "pkgcode:" ++ name

private def pkgCodeMsg (name : String) : String :=
  s!"unknown command '\\{name}' in package code; any [...] options and its " ++
    "{...} arguments were dropped, not set as text"

/-- Refuses an unknown LaTeX internal in package code, returning the index
past up to nine `{...}` groups, which are dropped. -/
public def recoverPackageCmd (ctx : Ctx) (name : String) (raws : Array Raw) (j : Nat)
    (pos : Pos) : EM { k : Nat // j ≤ k } := do
  modify (warnOnceState ctx (pkgCodeKey name) .W0391 (pkgCodeMsg name)
    pos (some (unknownCmdHelp name false)) (Compat.styInternal ctx.file name))
  return ⟨argGroupsEnd raws j 9, argGroupsEnd_ge raws j 9⟩

/-- Records a refusal's kept text with its code and command; empty text
records nothing. -/
private def noteSalvage (code : DiagCode) (name text : String) : EM Unit := do
  let t := text.trimAscii.toString
  unless t.isEmpty do
    modify fun st =>
      { st with
        salvage := st.salvage.push { code := code, command := name, text := t } }

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

private def warnReservedCtrl (ctx : Ctx) (name : String) (code : DiagCode)
    (pos : Pos) : EM Unit :=
  if name == "block" then
    warnOnce ctx "ctrl:block:inline" code
      "a vertical skip inside a paragraph, a table cell or an argument is not set here; skipped"
      pos (help := "put the skip between paragraphs")
  else
    warnOnce ctx ("ctrl:" ++ name) code s!"'\\{name}' is not implemented yet; skipped" pos

/-- The code a reserved control at `i` earns in inline content, including a
`\block` skip with an option and an empty group. -/
private def reservedCtrlAt (raws : Array Raw) (i : Nat) (name : String) (pos : Pos) :
    Option DiagCode :=
  if blockOnly.contains name && name == "block" then
    let (k, unclosed) := skipOptionRuns raws (i + 1) pos
    match unclosed, raws[skipSpaces raws k]? with
    | none, some (.group body _) => if body.isEmpty && i + 1 < k then some .W0329 else none
    | _, _ => none
  else reservedCtrl.lookup name

private inductive ColorRead where
  | resolved (color : Color) (token : Option ColorRef)
  | missing
  | rejected

/-- The one alternate a colorant has: its first declaration's, a later different one named. -/
private def inkOnce (ctx : Ctx) (c : Color) (pos : Pos) : EM Color := do
  match c.ink? with
  | none => return c
  | some (i, t) =>
    match (← get).inks.find? (·.name == i.name) with
    | some j =>
      if j == i then return c
      modify fun st => { st with diags := st.diags.push (diagOf ctx .W0441
        s!"the ink '{i.name}' is declared again with another alternate; its first alternate stands"
        (some pos) (help := "a colorant names one ink: give each ink its own colorant, as \\definespotcolor{name}{Other Ink}{c,m,y,k}")
        (subject := some s!"ink:{i.name}")) }
      return Color.ofInk j t
    | none =>
      modify fun st => { st with inks := st.inks.push i }
      return c

/-- The one door that parses and resolves a source colour, naming what it
rejects. -/
private def readColor (ctx : Ctx) (pal : Palette) (model : Option String)
    (src : String) (pos : Pos) : EM ColorRead := do
  if model.isNone && src == Compat.normalInkSource then
    return .resolved (Ir.Design.printInk ctx.basePalette) none
  let label := match model with
    | some m => s!"{m.trimAscii.toString}({src.trimAscii.toString})"
    | none => src.trimAscii.toString
  if model.isNone then noteColorReads src
  match pal.resolveSource model src with
  | .ok (some c) =>
    let c ← inkOnce ctx c pos
    if model.isNone then
      if let some i := pal.lostInk? src then
        modify fun st => { st with diags := st.diags.push (diagOf ctx .W0440
          s!"'{src.trimAscii.toString}' mixes the ink '{i.name}' with a colour other than the paper \
or its own tint; it prints as a process colour" (some pos)
          (help := "mix an ink only with the paper, as 'name!50'; a mix of two colours is a third")
          (subject := some s!"ink:{i.name}")) }
    let token := if model.isNone then pal.refOf? label else none
    return .resolved c token
  | .ok none =>
    if model.isNone then noteMentions src
    return .missing
  | .error (.unsupported m) =>
    diag ctx .W0102
      s!"colour model '{m}' is not supported; use {String.intercalate ", " Decl.colorModelNames}" pos
    return .rejected
  | .error (.malformed m detail) =>
    diag ctx .E0321 s!"cannot read {m} colour {src.trimAscii.toString.quote}: {detail}" pos
      (help := "model values use their documented component count and range")
    return .rejected

/-- A coloured run as it ships on the current ground: a generated role that
does not read there takes its family's tone. -/
private def coloredRun (ctx : Ctx) (c : Color) (ref : Option ColorRef) (body : Array Inline) :
    Inline :=
  match ctx.ground with
  | some g => ctx.palette.groundRun g (.colored c ref body)
  | none => .colored c ref body

/-- Whether an alert in `c` sets on the mark `m`: a generated mark stands under the generated alert
only, and not on a ground the accent reads on as text, where the alert takes its tone there. -/
private def marksAlert (ctx : Ctx) (c m : Color) : Bool :=
  ctx.palette.seeded.all fun st =>
    st.colors.alertMark != some m ||
      (st.colors.alert == c && !(ctx.ground.any fun g => decide (Contrast.aaText ≤ Contrast.contrastMilli m g)))

/-- The inlines a font command or `\alert` sets around an elaborated body. -/
private def modifierInlines (ctx : Ctx) (name : String) (style : Style)
    (edges : Bool × Bool) (inner : Array Inline) (pos : Pos) : EM (Array Inline) := do
  if name == Compat.alertMark false then return #[.styled .bold inner]
  if name != Compat.alertMark true then return Ir.fontCmdInlines style edges inner
  -- beamer's `\alert` sets the `alerted text` role, not a colour named `alert`; a mark under it
  -- where the palette declares one.
  match Ir.Design.declared? ctx.palette .alert with
  | some c =>
    recordColorSpan ctx "alert" c true pos
    match Ir.Design.declared? ctx.palette .alertMark with
    | some m =>
      if marksAlert ctx c m then
        return #[.decorated (.highlight m (some (.role .alertMark))) #[.colored c (some (.role .alert)) inner]]
      else return #[coloredRun ctx c (some (.role .alert)) inner]
    | none => return #[coloredRun ctx c (some (.role .alert)) inner]
  | none =>
    warnPaletteMiss ctx "alert" pos
    return #[.styled .bold inner]

private def warnOverlaySpec (ctx : Ctx) (w : String) (pos : Pos) : EM Unit :=
  warnOnce ctx "spec:overlay" .W0105
    s!"overlay specification '{w}' does not name a step; its content is \
shown on every step" pos
    (help := "write a numbered spec: <2>, <2->, or <2-3>; incremental \
specs are not modelled")

/-- A modifier's overlay selector, named when the step model cannot number
it. -/
private def selectorSpec (ctx : Ctx) (head : Option String) (pos : Pos) : EM (Option OverlaySpec) := do
  match head with
  | none => return none
  | some w =>
    let spec := Ir.overlayRange w
    unless spec.isSome do warnOverlaySpec ctx w pos
    return spec

/-- A link or target over an elaborated body, selected whole by its spec as
beamerbaseoverlay.sty's `\only` does. -/
private def targetInlines (ctx : Ctx) (name key : String)
    (spec : Option OverlaySpec) (inner : Array Inline) (pos : Pos) : EM (Array Inline) := do
  let wrapped ← if name == "hyperlink" then
      if Ir.anyInline (·.anchorBearing) inner then do
        warnOnce ctx "link:nested" .W0104
          "a link wrapper contains another link; the outer link is skipped" pos
          (help := "links cannot nest; move the inner link outside the outer wrapper")
        pure inner
      else
        pure #[.link ("#".append (Ir.labelAnchor key)) (ctx.styles.linkInk "link" inner)]
    else
      pure (#[.label key] ++ inner)
  return pushModifier #[] spec wrapped #[]

private def warnAltSpec (ctx : Ctx) (pos : Pos) : EM Unit :=
  warnOnce ctx "spec:overlay" .W0105
    "'\\alt' without a numbered specification shows its first \
alternative on every step" pos
    (help := "write a numbered spec: <2>, <2->, or <2-3>; incremental \
specs are not modelled")

/-- The form each reference command resolves with: `\ref`, `\eqref` and
cleveref's (manual v0.21.4 §2). -/
private def refCtrlForm? (name : String) : Option Ir.RefForm :=
  [("ref", Ir.RefForm.plain), ("eqref", .paren),
   ("cref", .cref false), ("Cref", .cref true),
   ("labelcref", .labelOnly),
   ("namecref", .name false), ("nameCref", .name true),
   (Marker.name .crefRange "", .crefRange false),
   (Marker.name .crefRangeUp "", .crefRange true)].lookup name

private def refFormNeedsKind : Ir.RefForm → Bool
  | .cref _ | .crefRange _ | .name _ => true
  | .plain | .paren | .labelOnly | .headed => false

-- Sealed so the knot's fixpoint never unfolds their string code.
seal footnoteOverride hasParRaw footnoteWarnPar footnoteWarnFace
seal thanksWarn footnoteStepNum noteNeedsGroup warnUnknownCmd noteSalvage recoverPackageCmd
seal warnMisplacedDecl warnReservedCtrl optionRunAdvice optionRunClause
seal warnPaletteMiss warnOverlaySpec warnAltSpec targetInlines
seal argText skipBracketRun bracketRunSrc
seal imageArm
seal warnUnclosed warnDroppedArgs
seal refCtrlForm? refFormNeedsKind

/-- Takes latex-lab-tikz's `alt` and `artifact` keys out of a picture's
option run, leaving the body as written without them. -/
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
  for e in Parse.rawEntries opts do
    let text := (rawSrc e).trimAscii.toString
    let key := (KeyVal.entry text).1
    if key == "artifact" then
      alt := .decorative
    else if key == "alt" then
      alt := match KeyVal.rawEntry text with
        | (_, some v) => if v.isEmpty then .undeclared else Ir.Alt.declare (altValueText v)
        | (_, none) => .undeclared
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

/-- A picture label's formula, or its source text and the loss when it does
not parse. -/
private def pictureMath (ctx : Ctx) (d : Bool) (raws : Array Parse.Raw) :
    Ir.Inline × Array Picture.PDiag :=
  let expanded := expandMathList ctx.user (mathLimit ctx) #[] raws.toList
  match MathParse.parseMath d expanded (mathEnv ctx) with
  | .ok (l, _) => (.formula d (Parse.rawSrc raws) l, #[])
  | .error what => (.math d (Parse.rawSrc raws),
      #[(.W0012, s!"math with {what} is not rendered yet; the \
formula {floorWording (Parse.rawSrc raws)}")])

private def subsetPicture (ctx : Ctx) (body : Array Raw) (size : Option String) :
    Ir.Pic.Picture × Array Picture.PDiag :=
  Picture.elabPicture ctx.palette body (pictureMath ctx) ctx.pic.sets ctx.pic.metric
    ctx.pic.macros argStyles ctx.page.scale declStyles ctx.page.fontSize
    (locate := fun pos => some (ctx.sourceSpan pos))
    (metaArrows := Picture.metaArrowsOf ctx.pic.preamble) (outerDecls := size.toArray)

/-- The size switch in force by its ladder name; `none` at `normalsize` or
under an explicit `\fontsize`. -/
private def pictureSizeInForce : EM (Option String) := do
  let size := (← get).scope.blockDecls.foldl (fun size decl => match decl with
    | .style (.size s) => some s
    | .style (.fontSize _ _) => none
    | _ => size) none
  return size.filter (· != "normalsize")

/-- A picture's boundary request, of its kind: its source and the size in force. -/
private def pictureSrcAt (body : Array Raw) (kind : Ir.PicKind := .picture) : EM Ir.PicSrc := do
  return { kind, body := Parse.rawSrc body, size := ← pictureSizeInForce }

/-- Notes the colour names a picture reads: its body's, the boundary preamble's, and those of
each picture setting and macro once. -/
private def notePictureReads (ctx : Ctx) (body : Array Raw) : EM Unit := do
  unless ← readsOwed do return
  noteColorReads (Parse.rawSrc body)
  unless (← get).spans.picturePreambleRead do
    noteColorReads ctx.pic.preamble
  let (sets, macros) := (← get).spans.pictureContextRead
  for (_, rs) in ctx.pic.sets.extract sets ctx.pic.sets.size do
    noteColorReads (Parse.rawSrc rs)
  for (_, def_) in ctx.pic.macros.extract macros ctx.pic.macros.size do
    noteColorReads def_
  modify fun st => { st with spans := { st.spans with
    pictureContextRead := (ctx.pic.sets.size, ctx.pic.macros.size), picturePreambleRead := true } }

/-- States a boundary request once, the drawing named `what`, and returns the image source that
stands for it; `fallback` records a drawing the subset makes beside it. -/
private def boundaryRequest (ctx : Ctx) (src : Ir.PicSrc) (id : String) (pos : Pos)
    (fallback : Bool) (what help : String) : EM String := do
  let tool := ctx.pic.tool.getD "lualatex"
  let img := Ir.picSrcPrefix ++ id
  modify fun st =>
    let st := if st.pictures.any (fun p => p.1 == id) then st
      else { st with pictures := st.pictures.push (id, src) }
    if !fallback || st.spans.fallbacks.contains id then st
    else { st with spans := { st.spans with fallbacks := st.spans.fallbacks.push id } }
  recordImageSpan ctx img pos
  warnOnce ctx ("picture:boundary:" ++ id) .N0023
    s!"this {what} is drawn by {tool} at the boundary; its text is not \
in the document's census" pos (help := help)
  return img

/-- Sends a picture to the boundary and returns the image standing for it; a
block the subset partly draws is recorded as a fallback. -/
private def routePicture (ctx : Ctx) (body : Array Raw) (pic : Ir.Pic.Picture) (pos : Pos)
    (block : Bool) : EM Ir.Inline := do
  let src ← pictureSrcAt body
  let img ← boundaryRequest ctx src (Ir.picHash src.source) pos (block && !pic.shapes.isEmpty)
    "picture" "the box is measured and placed by the engine; alt={...} or \
artifact on the picture, or a figure caption, names it for assistive technology"
  return .image img {} pic.alternative

/-- A picture inside a line: the boundary's image where the boundary is open
and the request stands, else `none` with the loss named. -/
private def inlinePicture (ctx : Ctx) (body : Array Raw) (pos : Pos) :
    EM (Option Ir.Inline) := do
  let (alt, body) := splitPictureAlt body pos
  let id := Ir.picHash (← pictureSrcAt body).source
  -- premise: pictureInlineLineChecks — drawn in its line or named
  if ctx.pic.tool.isSome && !body.isEmpty && !ctx.pic.withdrawn.contains id then
    notePictureReads ctx body
    let (pic, _) := subsetPicture ctx body (← pictureSizeInForce)
    noteLostInks ctx (Parse.rawSrc body) pos pic.gradients
    return some (← routePicture ctx body { pic with alt := alt } pos false)
  warnOnce ctx ("picture:inline:" ++ id) .W0334
    "a picture inside a line of text is not drawn: the rendered subset sets a \
picture only as a block" pos
    (help := "a boundary tool (lualatex) draws it in its line; standing in a \
paragraph of its own, the rendered subset draws it")
  return none

/-- The body and position of a `tikzcd` a display holds alone. -/
private def soleTikzcd (body : Array Raw) : Option (Array Raw × Pos) :=
  match (body.filter fun r => !(r matches .space)).toList with
  | [.env "tikzcd" b p] => some (b, p)
  | _ => none

/-- A `tikzcd` body's boundary request and its content key. -/
private def cdSource (b : Array Raw) : EM (Ir.PicSrc × String) := do
  let src ← pictureSrcAt b .cd
  return (src, Ir.picHash src.source)

/-- A diagram's boundary request, its identity, and the native reader's
drawing with the losses it names. -/
private def cdReading (ctx : Ctx) (b : Array Raw) :
    EM (Ir.PicSrc × String × Ir.Pic.Picture × Array Picture.PDiag) := do
  notePictureReads ctx b
  let (src, id) ← cdSource b
  let (pic, pdiags) := Picture.Cd.elabCd ctx.palette b (pictureMath ctx) ctx.pic.metric
    ctx.page.fontSize Ir.Color.white
    ((src.size.map fun n => (Ir.scaleStepIn ctx.page.scale 1000 n).toNat).getD 1000)
  let pdiags := if (ctx.pic.preamble.splitOn "\\tikzcdset").length > 1 then
      pdiags.push (.W0334, "the document's '\\tikzcdset' settings are outside the native \
diagram reader; the diagram is drawn without them")
    else pdiags
  return (src, id, pic, pdiags)

/-- Names the reader's losses where its drawing ships, keyed under the
picture when its request is withdrawn or declined. -/
private def cdNamed (ctx : Ctx) (id : String) (pic : Ir.Pic.Picture)
    (pdiags : Array Picture.PDiag) (pos : Pos) : EM Unit := do
  let declined := ctx.pic.tool.isNone && !pic.shapes.isEmpty && Picture.namesLoss pdiags
  if declined then
    modify fun st => if st.spans.declined.contains id then st
      else { st with spans := { st.spans with declined := st.spans.declined.push id } }
  for (code, msg) in pdiags do
    let help : Option String := match code with
      | .W0334 => some "write it with arrows, labels and keys the diagram reader draws, \
or let a boundary tool draw it"
      | _ => none
    -- premise: pictureRouteChecks — the driver folds these, none dropped
    if ctx.pic.withdrawn.contains id || declined then
      warnOnce ctx ("picture:" ++ id ++ ":" ++ msg) code msg pos (help := help)
    else
      warnOnce ctx ("picture:" ++ msg) code msg pos (help := help)
  recordNativePictureSpan ctx pos

/-- States a diagram's boundary request once and returns the image source
that stands for it. -/
private def cdRequest (ctx : Ctx) (src : Ir.PicSrc) (id : String) (pos : Pos)
    (fallback : Bool) : EM String :=
  boundaryRequest ctx src id pos fallback "diagram" "the box is measured and placed by the \
engine; a figure caption names it for assistive technology"

/-- A display's sole `tikzcd` as the native reader draws it, or `none` where
it draws nothing or the open boundary takes a lossy drawing. -/
private def tikzcdNative (ctx : Ctx) (body : Array Raw) (pos : Pos) :
    EM (Option Ir.Pic.Picture) := do
  let some (b, _) := soleTikzcd body | return none
  let (_, id, pic, pdiags) ← cdReading ctx b
  if pic.shapes.isEmpty then return none
  -- premise: tikzcdNativeChecks — lossy diagrams go to an open boundary
  if Picture.namesLoss pdiags && ctx.pic.tool.isSome && !ctx.pic.withdrawn.contains id then
    return none
  cdNamed ctx id pic pdiags pos
  return some pic

/-- A display's sole `tikzcd` as the boundary's image, or `none` where the
boundary is closed or withdrew the request. -/
private def tikzcdDisplay (ctx : Ctx) (body : Array Raw) (pos : Pos) :
    EM (Option Ir.Inline) := do
  let some (b, _) := soleTikzcd body | return none
  notePictureReads ctx b
  let (src, id) ← cdSource b
  -- premise: tikzcdRouteChecks — a refused diagram keeps its text floor
  if ctx.pic.tool.isNone || ctx.pic.withdrawn.contains id then return none
  let img ← cdRequest ctx src id pos true
  return some (.role Ir.displayPictureRole #[.image img {} .undeclared])

/-- A block `tikzcd`: the boundary's image where the boundary is open and the
reader falls short, else the reader's drawing or a placeholder. -/
private def tikzcdArm (ctx : Ctx) (body : Array Raw) (pos : Pos)
    (blocks : Array Block) : EM (Array Block) := do
  let (src, id, pic, pdiags) ← cdReading ctx body
  -- premise: tikzcdNativeChecks — lossy diagrams go to an open boundary
  if ctx.pic.tool.isSome && !body.isEmpty &&
      (pic.shapes.isEmpty || (Picture.namesLoss pdiags && !ctx.pic.withdrawn.contains id)) then
    let img ← cdRequest ctx src id pos !pic.shapes.isEmpty
    return blocks.push (.para #[.image img {} pic.alternative])
  cdNamed ctx id pic pdiags pos
  if pic.shapes.isEmpty then
    warnOnce ctx "picture:placeholder" .W0362
      "no part of this diagram is inside the rendered subset; a placeholder box marks \
its place" pos
      (help := "the box holds the diagram's place; \\allow{W0362} accepts the loss")
    return blocks.push (.picture (Picture.placeholder DiagCode.W0362.code))
  return blocks.push (.picture pic)

/-- Code with each bound `#k` replaced by its argument's source and `##` by
`#`, as TeX substitutes before minted reads the code. -/
private def bindCodeParams (ctx : Ctx) (code : String) : String := Id.run do
  if ctx.args.isEmpty || !code.contains '#' then return code
  let cs := code.toList.toArray
  let mut out := ""
  let mut i := 0
  for _ in [0:cs.size] do
    let some c := cs[i]? | break
    let next := cs[i + 1]?
    if c == '#' && next == some '#' then
      out := out.push '#'
      i := i + 2
    else if c == '#' && next.any (fun d => '1' ≤ d && d ≤ '9') then
      let k := (next.map Char.toString).getD ""
      match ctx.args.find? (·.1 == "a" ++ k ++ " source"),
          ctx.args.find? (·.1 == "a" ++ k) with
      | some (_, bound), _ | none, some (_, bound) =>
        out := out ++ Ir.plainText (bound.getD #[])
        i := i + 2
      | none, none =>
        out := out.push c
        i := i + 1
    else
      out := out.push c
      i := i + 1
  return out

/-- `\small` read as `small`, when the size ladder holds it. -/
private def sizeCommand? (v : String) : Option String :=
  if v.startsWith "\\" then
    let name := (v.drop 1).toString
    if Ir.sizeScale.any (·.1 == name) then some name else none
  else none

/-- A `fontsize` entry that keeps the size in force: `auto`, `\relax` or an
empty value. -/
private def keepsSize (bare : String) : Bool :=
  match KeyVal.entry bare with
  | ("fontsize", some v) => let v := listingVal v; v.isEmpty || v == "auto" || v == "\\relax"
  | _ => false

private def noteFormatcom (ctx : Ctx) (pos : Pos) : EM Unit :=
  warnOnce ctx "lstopt:formatcom" .N0102
    "minted's formatcom runs TeX on the Pygments formatter's macros, which only a TeX \
engine runs; the listing's tokens paint by their code roles" pos
    (help := "set a role's colour in the palette by its name: codeink, codekeyword, \
codename, codeliteral, codecomment or codeerror")

/-- Names once a language no known lexer or highlighter reply reads, with the
nearest lexer name as minted's help. -/
private def nameUnknownLexer (ctx : Ctx) (lang : String) (minted : Bool) (pos : Pos) :
    EM Unit := do
  -- premise: Tests.inlineCodeRequestChecks — a refused language is named once
  if LexerName.known lang || ctx.listingReplies.any (·.request.language == lang) then return
  let help := if !minted || (← get).warnedUnknown.contains ("listing-language:" ++ lang) then none
    else match LexerName.nearest? lang with
      | some near => some s!"spell it '{near}', the lexer name nearest it"
      | none => some "name a lexer Pygments registers, such as 'python' or 'lean4'"
  warnOnce ctx ("listing-language:" ++ lang) .W0412
    s!"'{lang}' names no lexer the engine or Pygments has; its code is set as plain text" pos
    (help := help)

/-- An author's language spelling as a listing's language token, named when
no lexer reads it; `none`, named, when it is outside the token grammar. -/
private def codeLanguage (ctx : Ctx) (raw : String) (minted : Bool) (pos : Pos) :
    EM (Option Ir.ListingLang) := do
  match Ir.listingLang? raw with
  | some l =>
    nameUnknownLexer ctx l.val minted pos
    return some l
  | none =>
    let msg := s!"listing language '{raw.trimAscii.toString}' is not a plain name; the \
listing carries no language"
    warnOnce ctx ("lstopt:" ++ msg ++ ":language") .W0110 msg pos
      (help := "spell it as letters, digits, +, #, - or . (python, c++, c#)")
    return none

/-- The minted options inline code reads, later layers winning. -/
private structure InlineCodeOpts where
  size : Option Ir.Style := none
  style : Option Ir.ListingStyle := none
  tabSize : Nat := 8
  breakLines : Bool := false


/-- Inline code's options as minted reads them there; a key inline code does
not honour is named. -/
private def inlineCodeOpts (ctx : Ctx) (opts : String) (pos : Pos) : EM InlineCodeOpts := do
  let unhonoured (item key msg : String) (help : Option String) : EM Unit := do
    noteMentions item
    warnOnce ctx ("lstopt:" ++ msg ++ ":" ++ key) .W0110 msg pos (help := help)
  let mut o : InlineCodeOpts := {}
  for bare in KeyVal.items opts do
    let key := ((KeyVal.pair? bare).map (·.1)).getD bare
    if key == "formatcom" || bare.startsWith "formatcom=" then
      noteMentions bare
      noteFormatcom ctx pos
      continue
    -- premise: inlineCodeChecks — display keys leave inline code unchanged
    if Compat.mintedDisplayKeys.contains key then
      continue
    if keepsSize bare then
      o := { o with size := none }
      continue
    match KeyVal.pair? bare with
    | some ("fontsize", v) =>
      let v := listingVal v
      match sizeCommand? v with
        | some name => o := { o with size := some (.size name) }
        | none =>
          unhonoured bare key s!"inline code fontsize '{v}' is not a supported size command; the size \
around it stands" "use a named size command such as fontsize=\\small, or fontsize=\\relax"
    | some ("style", v) =>
      let v := listingVal v
      match Ir.ListingStyle.ofName? v with
      | some selected => o := { o with style := some selected }
      | none =>
        unhonoured bare key s!"listing style '{v}' is not supported; the current style stands"
          "use style=default or style=friendly"
    | some ("tabsize", v) =>
      let v := listingVal v
      -- FancyVerb's upper bound (fancyvrb.sty, the FV/tabsize key).
      match v.toNat? with
      | some n =>
        if 0 < n && n ≤ 100 then o := { o with tabSize := n }
        else unhonoured bare key s!"listing tabsize '{v}' is outside 1..100; \
the current tab stops stand" none
      | none =>
        unhonoured bare key s!"listing tabsize '{v}' is not an integer; \
the current tab stops stand" none
    | some ("breaklines", v) =>
      let v := listingVal v
      if v == "true" then o := { o with breakLines := true }
      else if v == "false" then o := { o with breakLines := false }
      else unhonoured bare key s!"listing breaklines '{v}' is not true or false; \
the current wrapping stands" none
    | some (k, _) => unhonoured bare key s!"inline code key '{k}' is not honoured; ignored" none
    | none =>
      if bare == "breaklines" then o := { o with breakLines := true }
      else unhonoured bare key s!"inline code key '{bare}' is not honoured; ignored" none
  -- premise: codeRoleChecks — the style is inert under a full palette
  if let some declared := o.style then
    let pal := (← get).scope.palette.current.getD ctx.palette
    if !(ListingHighlight.Role.all.any (CodeColor.styleReads pal)) then
      warnOnce ctx ("lstopt:style:" ++ declared.name) .W0387
        s!"minted's style '{declared.name}' was read and had no effect: the palette names \
or derives a colour for every code role" pos
        (help := "\\allow{W0387} accepts the skip")
  return o

/-- Inline code: lines classified and painted by code role in the mono
family, joined by forced breaks, at any size its options declare. -/
private def inlineCodeOf (ctx : Ctx) (lang : Option Ir.ListingLang) (lines : Array String)
    (o : InlineCodeOpts) : EM (Array Inline) := do
  if lines.all (·.isEmpty) then return #[]
  let source := String.intercalate "\n" lines.toList
  let classified := lang.bind fun l =>
    match ListingHighlight.language? l.val with
    | some lexer => some (ListingHighlight.tokenize lexer lines)
    | none => ListingReply.lookup ctx.listingReplies l.val source
  if let some l := lang then
    if classified.isNone then
      modify fun st => if st.spans.code.contains (l.val, source) then st
        else { st with spans := { st.spans with code := st.spans.code.push (l.val, source) } }
  let tokenLines := classified.getD (lines.map fun line => #[{ text := line }])
  let pal := (← get).scope.palette.current.getD ctx.palette
  let spec : Ir.ListingSpec := { tabSize := o.tabSize, breakLines := o.breakLines }
  let mut body : Array Inline := #[]
  for line in tokenLines do
    unless body.isEmpty do
      body := body.push (.linebreak {})
    if ListingHighlight.lineText line == "" then
      body := body.push (.text "\u00a0")
    else
      let laid := (line.foldl (fun (acc, column) t =>
        let (text, column) := spec.layoutText column t.text
        (acc.push { t with text }, column)) ((#[] : Array ListingHighlight.Token), 0)).1
      body := body ++ Listing.inlineCode pal (ctx.ground.or ctx.codeGround) o.style laid
  let code := #[Inline.styled .mono body]
  return match o.size with
    | some size => #[.styled size code]
    | none => code

/-- Verbatim inside inline content: `\verb` in the mono face, `\mintinline`
as inline code, and a display listing named and set as inline code. -/
private def inlineVerbatim (ctx : Ctx) (env s : String) (pos : Pos) : EM (Array Inline) := do
  if env == "verb" then
    let kept := s.map fun c => if c == ' ' then '\u00a0' else c
    return if kept.isEmpty then #[] else #[.styled .mono #[.text kept]]
  let (opts, afterOpt) := (Parse.listingOptHead s).getD ("", 0)
  if env == "mintinline" || env == "mint" then
    let some (rawLang, afterLang) := Parse.mintedLangHead s afterOpt | return #[]
    if env == "mint" then
      warnOnce ctx "listing-inline:mint" .W0413
        "'\\mint' within a line of text or an argument is set as inline code; LaTeX sets a \
display there, or cannot set it" pos
        (help := s!"write \\mintinline\{{rawLang.trimAscii.toString}}\{…} for inline code, or put \
'\\mint' on a line of its own for a display")
    let o ← inlineCodeOpts ctx opts pos
    let lang ← codeLanguage ctx rawLang true pos
    return ← inlineCodeOf ctx lang #[bindCodeParams ctx (Parse.mintedCode s afterLang)] o
  let lines := Ir.verbatimLines (s.drop (listingContentStart env s)).toString
  let (rawLang, opts) : Option String × String :=
    if env == "minted" then (((Parse.mintedLangHead s afterOpt).map (·.1)), opts)
    else if env == "lstlisting" then
      let entries := (KeyVal.items opts).toList
      let isLang (e : String) := ((KeyVal.pair? e).map (·.1)) == some "language"
      ((entries.find? isLang).bind fun e => (KeyVal.pair? e).map (listingVal ·.2),
        ",".intercalate (entries.filter (!isLang ·)))
    else (none, opts)
  warnOnce ctx ("listing-inline:" ++ env) .W0411
    s!"'\\begin\{{env}}' within a line of text or an argument does not compile under LaTeX; \
it is set as inline code" pos
    (help := match rawLang, env == "minted" with
      | some l, true => s!"write \\mintinline\{{l.trimAscii.toString}}\{…} for inline code"
      | _, _ => "write \\verb|…| for inline code")
  let o ← inlineCodeOpts ctx opts pos
  let lang ← match rawLang with
    | some l => codeLanguage ctx l (env == "minted") pos
    | none => pure none
  inlineCodeOf ctx lang lines o

seal splitPictureAlt subsetPicture routePicture inlinePicture
seal inlineVerbatim
seal secFmtOfBody applySecFmt applyCounter counterCtrl counterArm runInHead
seal theCounterLevel? sectionLevel
seal inlineGroup

mutual
/-- The styles of an inline that is only nested style wrappers around
nothing, outermost first; `none` when it holds content. -/
-- conserves: none — a census, not a rewrite
private def declChainOne : Ir.Inline → Option (Array Ir.Style)
  | .styled st inner => (declChainList inner.toList).map (#[st] ++ ·)
  | _ => none

private def declChainList : List Ir.Inline → Option (Array Ir.Style)
  | [] => some #[]
  | [x] => declChainOne x
  | _ => none
end

/-- A 0-ary expansion split into its content and the trailing declaration
chain, outermost first, that styles the rest of the enclosing group. -/
private def splitTrailingDecls (xs : Array Ir.Inline) :
    Array Ir.Inline × Array Ir.Style :=
  match xs.back? with
  | some x =>
    match declChainOne x with
    | some styles => if styles.isEmpty then (xs, #[]) else (xs.pop, styles)
    | none => (xs, #[])
  | none => (xs, #[])

/-- Binds a parameter's elaboration and, for a code parameter, its source
under its name and a space, which no document name holds. -/
private def bindParam (p : Param) (v : Array Inline) (source : Unit → String)
    (bindings : Array (String × Option (Array Inline))) : Array (String × Option (Array Inline)) :=
  let bindings := bindings.push (p.name, some v)
  if p.code then bindings.push (p.name ++ " source", some #[.text (source ())]) else bindings

/-- The first parameter and its definition's default when its optional argument is absent and the
replacement reads it. -/
private def absentDefault? (params : Array Param)
    (bindings : Array (String × Option (Array Inline))) : Option (Param × Array Raw) := do
  let p ← params[0]?
  let d ← p.default
  let some (b, none) := bindings[0]? | none
  if b == p.name && p.referenced then some (p, d) else none

/-- The bindings with the first parameter bound to its default's reading `v`, as a given argument
binds. -/
private def bindDefault (p : Param) (d : Array Raw) (v : Array Inline)
    (bindings : Array (String × Option (Array Inline))) : Array (String × Option (Array Inline)) :=
  bindParam p v (fun _ => rawSrc d) #[] ++ bindings.extract 1 bindings.size

/-- The index past the first `{...}` group at or after `k`, or `k` when none follows. -/
private def pastGroupFrom (raws : Array Raw) (k : Nat) : Nat := Id.run do
  for j in [k:raws.size] do
    if raws[j]? matches some (.group _ _) then return j + 1
  return k

/-- Whether a command defines what the body cannot hold: a command, an environment or a theorem
environment, or a theorem style. -/
private def bodyDefiner (name : String) : Bool :=
  name == "define" || name == "defineenv" || name == "newtheorem" || name == "theoremstyle"

/-- The index past a body definer's operands from `i`. -/
private def definerEnd (raws : Array Raw) (name : String) (i : Nat) : Nat :=
  if name == "define" then
    let j := skipSpaces raws i
    if raws[j]? matches some (.ctrl _ _) then pastGroupFrom raws (j + 1) else i
  else if name == "defineenv" then Compat.defineEnvEnd raws i
  else Compat.theoremDeclEnd raws name i

/-- A block-level command reached as inline content, named, and the index past what it takes: a
definer's whole form, any other command's word alone. -/
private def inlineBlockOnly (ctx : Ctx) (raws : Array Raw) (name : String) (i : Nat) (pos : Pos) :
    EM { k : Nat // i + 1 ≤ k } := do
  if name == "defineenv" || name == "newtheorem" then
    warnOnce ctx ("ctrl:" ++ name ++ ":body") .W0104 Compat.bodyEnvDefMessage pos
      (help := Compat.bodyEnvDefHelp)
  else if name != "theoremstyle" then
    diag ctx .E0312 s!"'\\{name}' is not allowed here" pos
      (help := "it is a block-level command: use it between paragraphs, " ++
        "not inside inline content")
  if bodyDefiner name then
    return ⟨max (i + 1) (definerEnd raws name (i + 1)), Nat.le_max_left _ _⟩
  return ⟨i + 1, Nat.le_refl _⟩

mutual

/-- Binds the parameters from index `k` on, returning the bindings and the
index past their arguments. -/
private def takeArgsFrom (ctx : Ctx) (params : Array Param) (k : Nat) (name : String)
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
          have _ : rawWeightList (raws.extract (j + 1) c).toList
              < sliceWeight raws start :=
            extract_lt_slice c (by omega) (by omega)
          let v ← if p.referenced then
            elabInlinesCore { ctx with argBody := true } (raws.extract (j + 1) c)
            else pure #[]
          if p.type == .text && !allText v then
            diag ctx .E0305 s!"parameter '{p.name}' of '\\{name}' expects text" pos
          have _ : sliceWeight raws (c + 1) < sliceWeight raws start :=
            sliceWeight_lt raws (by omega) (by omega)
          let (bs, ⟨j2, hj2⟩) ← takeArgsFrom ctx params (k + 1) name raws (c + 1)
            pos (bindParam p v (fun _ => rawSrc (raws.extract (j + 1) c)) bindings)
          return (bs, ⟨j2, by omega⟩)
        | none =>
          diag ctx .E0316 s!"unclosed optional argument for '\\{name}'" pos
          have _ : rawWeightList (raws.extract (j + 1) raws.size).toList
              < sliceWeight raws start :=
            extract_lt_slice raws.size (by omega) (by omega)
          let v ← if p.referenced then
            elabInlinesCore { ctx with argBody := true } (raws.extract (j + 1) raws.size)
            else pure #[]
          if p.type == .text && !allText v then
            diag ctx .E0305 s!"parameter '{p.name}' of '\\{name}' expects text" pos
          have _ : sliceWeight raws raws.size < sliceWeight raws start :=
            sliceWeight_lt raws (by omega) (by omega)
          let (bs, ⟨j2, hj2⟩) ← takeArgsFrom ctx params (k + 1) name raws raws.size
            pos (bindParam p v (fun _ => rawSrc (raws.extract (j + 1) raws.size)) bindings)
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
        have _ : rawWeightList body.toList < sliceWeight raws start :=
          body_lt_slice hj (by simp only [rawWeight]; omega) hjge
        let v ← if p.referenced then
          elabInlinesCore { ctx with argBody := true } body
          else pure #[]
        if p.type == .text && !allText v then
          diag ctx .E0305 s!"parameter '{p.name}' of '\\{name}' expects text" pos
        have _ : sliceWeight raws (j + 1) < sliceWeight raws start :=
          sliceWeight_lt raws (by omega) (by omega)
        let (bs, ⟨j2, hj2⟩) ← takeArgsFrom ctx params (k + 1) name raws (j + 1)
          pos (bindParam p v (fun _ => Parse.rawSrcList body.toList) bindings)
        return (bs, ⟨j2, by omega⟩)
      | some (.word s pword) =>
        have hjlt := getElem?_lt hj
        have _ : sliceWeight raws (j + 1) < sliceWeight raws start :=
          sliceWeight_lt raws (by omega) (by omega)
        let (bs, ⟨j2, hj2⟩) ← takeArgsFrom ctx params (k + 1) name raws (j + 1)
          pos (bindParam p (if p.referenced then wordInlines ctx s pword else #[]) (fun _ => s)
            bindings)
        return (bs, ⟨j2, by omega⟩)
      | _ =>
        diag ctx .E0304 s!"missing argument '{p.name}' for '\\{name}'" pos
        takeArgsFrom ctx params (k + 1) name raws start pos
          (bindings.push (p.name, some #[]))
  else
    return (bindings, ⟨start, Nat.le_refl start⟩)
termination_by (ctx.envLimit, ctx.limit, sliceWeight raws start, 5 + (params.size - k))
decreasing_by all_goals knot_dec

/-- Keeps up to nine of an unknown command's `{...}` groups as content, a
space standing between them. -/
private def elabUnknownArgs (ctx : Ctx) (raws : Array Raw) (j : Nat) (count : Nat)
    (acc : Array Inline) (sb : String) (spaceAfter : Bool) :
    EM (Array Inline × String × { j' : Nat // j ≤ j' } × Nat × Bool) := do
  if 9 ≤ count then
    return (acc, sb, ⟨j, Nat.le_refl j⟩, count, spaceAfter)
  else
    match hj : raws[j]? with
    | some (.group body _) =>
      have hjlt := getElem?_lt hj
      let acc := flushText acc sb
      let acc := flushText acc (if count > 0 then " " else "")
      have _ : rawWeightList body.toList < sliceWeight raws j :=
        body_lt_slice hj (by simp only [rawWeight]; omega) (Nat.le_refl j)
      let inner ← inlineGroup ctx.palette (elabInlinesCore ctx body)
      let j2 := skipSpaces raws (j + 1)
      have hj2ge := skipSpaces_ge raws (j + 1)
      have _ : sliceWeight raws j2 < sliceWeight raws j :=
        sliceWeight_lt raws hjlt (by omega)
      let (acc', sb', ⟨j', hj'⟩, kept, sp) ←
        elabUnknownArgs ctx raws j2 (count + 1) (acc ++ inner) "" (j2 != j + 1)
      return (acc', sb', ⟨j', by omega⟩, kept, sp)
    | _ => return (acc, sb, ⟨j, Nat.le_refl j⟩, count, spaceAfter)
termination_by (ctx.envLimit, ctx.limit, sliceWeight raws j, 0)
decreasing_by all_goals knot_dec


private def elabInlinesCore (ctx : Ctx) (raws : Array Raw) : EM (Array Inline) := do
  let out ← elabInlinesFrom { ctx with macroRoles := ctx.macroRoles.enter } raws 0 #[] ""
  return if ctx.literalText then out else out.map (mapSmartText ctx.literalWhen)
termination_by (ctx.envLimit, ctx.limit, rawWeightList raws.toList, 4)
decreasing_by all_goals knot_dec

/-- The inline elaboration spine: one raw at `i` per step, threading the
inline accumulator and pending text. -/
private def elabInlinesFrom (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (acc : Array Inline) (sb : String) : EM (Array Inline) := do
  let (roles, acc, sb) := inlineMacroAt ctx.macroRoles raws i acc sb
  let ctx := { ctx with macroRoles := roles }
  if h : i < raws.size then
    have hadv1 : sliceWeight raws (i + 1) < sliceWeight raws i :=
      sliceWeight_lt raws h (Nat.lt_succ_self i)
    match hr : raws[i] with
    | .word s pos =>
      elabInlinesFrom ctx raws (i + 1) ((flushText acc sb).push (sourceInline ctx pos (.text s))) ""
    | .space =>
      -- A splice sets one separator per run, and no paragraph opens with one.
      elabInlinesFrom ctx raws (i + 1) acc
        (if spaceSeps sb then sb.push ' ' else sb)
    | .par _ =>
      elabInlinesFrom ctx raws (i + 1) acc
        (if needsSep acc sb then sb.push ' ' else sb)
    | .sym '[' pos =>
      elabInlinesFrom ctx raws (i + 1)
        ((flushText acc sb).push (sourceInline ctx pos (.text "["))) ""
    | .sym ']' pos =>
      elabInlinesFrom ctx raws (i + 1)
        ((flushText acc sb).push (sourceInline ctx pos (.text "]"))) ""
    | .sym '~' pos =>
      elabInlinesFrom ctx raws (i + 1)
        ((flushText acc sb).push (sourceInline ctx pos (.text "\u00a0"))) ""
    | .sym c pos =>
      if ctx.noteBody || ctx.argBody then
        -- In a note or an argument a reserved character is the caller's literal text.
        elabInlinesFrom ctx raws (i + 1)
          ((flushText acc sb).push (sourceInline ctx pos (.text (String.singleton c)))) ""
      else
        diag ctx .E0311 s!"reserved character '{c}'" pos (help := s!"escape it as '\\{c}'")
        elabInlinesFrom ctx raws (i + 1) acc sb
    | .math d body mpos =>
      let acc := flushText acc sb
      let x ← elabMathInline ctx d body mpos
      elabInlinesFrom ctx raws (i + 1) (acc.push x) ""
    | .group body _ =>
      have _ : rawWeightList body.toList < sliceWeight raws i :=
        body_lt_slice' h (by rw [hr]; simp only [rawWeight]; omega)
      let acc := flushText acc sb
      let inner ← inlineGroup ctx.palette (elabInlinesCore ctx body)
      elabInlinesFrom ctx raws (i + 1) (acc ++ inner) ""
    | .env name body pos =>
      have hw : rawWeightList body.toList < sliceWeight raws i :=
        body_lt_slice' h (by rw [hr]; simp only [rawWeight]; omega)
      if name == Parse.scopeEnv then
        let acc := flushText acc sb
        let inner ← elabInlinesCore ctx body
        elabInlinesFrom ctx raws (i + 1) (acc ++ inner) ""
      else if let some f := Parse.inputEnvFile? name then
        let acc := flushText acc sb
        let inner ← elabInlinesCore
          { ctx with file := f, callSite := none, kept := ctx.kept || Parse.isKeptInput name } body
        elabInlinesFrom ctx raws (i + 1) (acc ++ inner) ""
      else if let some numbered := displayMathEnvs.lookup name then
        let acc := flushText acc sb
        -- An inline display has no block to number: it sets unnumbered, named.
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
          -- Halves see only earlier definitions; the content sees the caller's.
          have _ : k < ctx.envLimit := lookupUserEnv_lt he
          have hb0 : sliceWeight body 0 < sliceWeight raws i := by
            have h0 : sliceWeight body 0 = rawWeightList body.toList := by
              simp [sliceWeight]
            omega
          let acc := flushText acc sb
          let (bindings, ⟨j, _⟩) ← takeArgsFrom ctx env.params 0 name body 0 pos #[]
          -- An absent optional argument takes its definition's default, read where the halves read.
          let bindings ← match absentDefault? env.params bindings with
            | some (p, d) => do
              let dctx : Ctx := { ctx with limit := env.cmdLimit, envLimit := k, args := bindings }
              pure (bindDefault p d (← elabInlinesCore { dctx with argBody := true } d) bindings)
            | none => pure bindings
          let envCtx : Ctx := { ctx with
            limit := env.cmdLimit, envLimit := k, args := bindings }
          let ⟨inner, _⟩ : { a : Array Raw // rawWeightList a.toList < sliceWeight raws i } :=
            ⟨envBody env body j, Nat.lt_of_le_of_lt (envBody_le env body j) hb0⟩
          let ⟨next, hnext⟩ : { n : Nat // i + 1 ≤ n } :=
            if env.ignoresAfterEnd then ⟨skipSpaces raws (i + 1), skipSpaces_ge raws (i + 1)⟩
            else ⟨i + 1, Nat.le_refl _⟩
          have _ : sliceWeight raws next < sliceWeight raws i :=
            Nat.lt_of_le_of_lt (sliceWeight_le raws hnext) hadv1
          let a1 ← elabInlinesCore envCtx env.beginBody
          let a2 ← elabInlinesCore ctx inner
          let a3 ← elabInlinesCore envCtx env.endBody
          elabInlinesFrom ctx raws next (acc ++ a1 ++ a2 ++ a3) ""
        | none =>
        if reservedEnv.contains name then
          warnOnce ctx ("env:" ++ name) .W0307
            s!"'\{{name}}' is not implemented yet; its content is not rendered" pos
          elabInlinesFrom ctx raws (i + 1) acc sb
        else
          warnOnce ctx ("env:" ++ name) .W0302 s!"unknown environment '\{{name}}'; its body is kept" pos
            (help := "\\defineenv{name}(...) {begin} {end} declares one")
          -- Spliced into this scan, so its edge spaces are ordinary separators.
          let (keptFrom, unclosed, dropped) := dropEnvArgs body pos
          if let some bpos := unclosed then
            warnUnclosed ctx s!"'\\begin\{{name}}'" bpos
          warnDroppedArgs ctx name (body.extract 0 keptFrom) dropped pos
          have _ : sliceWeight (raws.extract 0 i ++ body.extract keptFrom body.size
              ++ raws.extract (i + 1) raws.size) i < sliceWeight raws i :=
            sliceWeight_splice h hr keptFrom
          elabInlinesFrom ctx (raws.extract 0 i ++ body.extract keptFrom body.size
            ++ raws.extract (i + 1) raws.size) i acc sb
    | .verb env s vpos =>
      let acc := flushText acc sb
      let code ← inlineVerbatim ctx env s vpos
      elabInlinesFrom ctx raws (i + 1) (acc ++ code) ""
    | .ctrl name pos =>
      -- Parameters, then definitions, come before built-ins: order is the rule.
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
          have _ : k < ctx.limit := lookupUser_lt hu
          let acc := flushText acc sb
          let (bindings, ⟨j, hj⟩) ← takeArgsFrom ctx cmd.params 0 name raws (i + 1) pos #[]
          let callCtx : Ctx := { ctx.atCall name pos with limit := k, args := bindings }
          let expanded ← elabInlinesCore callCtx cmd.body
          if cmd.params.isEmpty then
            let (expanded, decls) := splitTrailingDecls expanded
            let acc := acc ++ expanded
            if decls.isEmpty then
              have _ : sliceWeight raws j < sliceWeight raws i :=
                Nat.lt_of_le_of_lt (sliceWeight_le raws hj) hadv1
              elabInlinesFrom ctx raws j acc ""
            else
              have _ : rawWeightList (raws.extract j raws.size).toList
                  < sliceWeight raws i :=
                extract_lt_slice raws.size h (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hj)
              let (roles, acc, _) := inlineMacroStep ctx.macroRoles none acc ""
              let ctx := { ctx with macroRoles := roles }
              let rest ← elabInlinesCore ctx (raws.extract j raws.size)
              let acc := acc ++ decls.foldr (fun st inner => #[Ir.Inline.styled st inner]) rest
              have _ : sliceWeight raws raws.size < sliceWeight raws i :=
                sliceWeight_lt raws h h
              elabInlinesFrom ctx raws raws.size acc ""
          else
            let acc := acc.push (.role cmd.name expanded)
            have _ : sliceWeight raws j < sliceWeight raws i :=
              Nat.lt_of_le_of_lt (sliceWeight_le raws hj) hadv1
            elabInlinesFrom ctx raws j acc ""
        | none =>
        let name := Compat.overlayName name
        if name == "hfill" then
          let acc := flushText acc sb
          elabInlinesFrom ctx raws (i + 1) (acc.push .fill) ""
        else if name == "qedhere" then
          -- amsthm.sty's `\qedhere`: the mark here, the space before taken back.
          let acc := if (← get).ctr.thm.proofs == 0 then flushText acc sb
            else unskipText acc sb ++ qedHereRun
          elabInlinesFrom ctx raws (i + 1) acc ""
        else if name == "ensuremath" then
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
          -- The `[` must be adjacent, so a line opening with `[` keeps it.
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
                have _ : sliceWeight raws j < sliceWeight raws i :=
                  sliceWeight_lt raws h (by omega)
                elabInlinesFrom ctx raws j acc ""
              | none =>
                let extra ← readBreakLen ctx (rawSrc (raws.extract (i + 2) raws.size)) pos
                let acc := (flushText acc sb).push (.linebreak extra)
                have _ : sliceWeight raws raws.size < sliceWeight raws i :=
                  sliceWeight_lt raws h h
                elabInlinesFrom ctx raws raws.size acc ""
            | _ =>
              let acc := (flushText acc sb).push (.linebreak {})
              let j := skipSpaces raws (i + 1)
              have hjge := skipSpaces_ge raws (i + 1)
              have _ : sliceWeight raws j < sliceWeight raws i :=
                sliceWeight_lt raws h (by omega)
              elabInlinesFrom ctx raws j acc ""
          else
            let acc := (flushText acc sb).push (.linebreak {})
            let j := skipSpaces raws (i + 1)
            have hjge := skipSpaces_ge raws (i + 1)
            have _ : sliceWeight raws j < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws j acc ""
        else if let some composed := raws[i + 1]?.bind (accentCompose name) then
          have _ : sliceWeight raws (i + 2) < sliceWeight raws i :=
            sliceWeight_lt raws h (by omega)
          let (roles, acc, sb) := accentOperandStep ctx.macroRoles raws[i + 1]? acc sb
          elabInlinesFrom { ctx with macroRoles := roles } raws (i + 2)
            ((flushText acc sb).push (sourceInline ctx pos (.text composed))) ""
        else if let some lit := escapeOf name then
          -- A control space stays pending, so the blanks after it are skipped.
          if name == " " then
            elabInlinesFrom ctx raws (i + 1) acc (sb ++ lit)
          else
            elabInlinesFrom ctx raws (i + 1)
              ((flushText acc sb).push (sourceInline ctx pos (.text lit))) ""
        else if (Lex.textSymbols.lookup name).isSome then
          elabInlinesFrom ctx raws (i + 1)
            ((flushText acc sb).push (sourceInline ctx pos
              (.text ((Lex.textSymbols.lookup name).getD "")))) ""
        else if let some style := modifierStyle? name then
          let head := selectorHead raws (i + 1)
          let j := head.2
          have hjge : i + 1 ≤ j := selectorHead_monotone raws (i + 1)
          -- beamerbaseoverlay.sty: only `\emph` also takes a trailing selector.
          let tailSpec := if name == "emph" && head.1.isNone then
              raws[j + 1]?.bind specWord? else none
          let next := j + 1 + if tailSpec.isSome then 1 else 0
          have hnext : j + 1 ≤ next := Nat.le_add_right _ _
          let spec ← selectorSpec ctx (head.1.orElse fun _ => tailSpec) pos
          -- beamer's `\emph`: an italic declaration, with no italic correction.
          let style := if name == "emph" && ctx.slides then .italic else style
          let edges := fun body next => if name == "emph" && ctx.slides
            then (false, false) else fontCmdEdges body next
          let literal := modifierLiteral ctx style spec
          let argCtx := { ctx with literalText := literal.1, literalWhen := literal.2 }
          match hj : raws[j]? with
          | some (.group body _) =>
            have hw : rawWeightList body.toList < sliceWeight raws i :=
              body_lt_slice hj (by simp only [rawWeight]; omega) (by omega)
            let acc := flushText acc sb
            have _ : rawWeightList (fontCmdContent body).toList < sliceWeight raws i := by
              exact Nat.lt_of_le_of_lt (by
                simpa [fontCmdContent] using
                  rawWeightList_filter_monotone (fun r => !fontCmdNocorr r) body.toList) hw
            let inner ← elabInlinesCore argCtx (fontCmdContent body)
            have _ : sliceWeight raws next < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            let active ← modifierInlines ctx name style (edges body.toList raws[next]?) inner pos
            elabInlinesFrom ctx raws next (pushModifier acc spec active inner) ""
          | some (.word s p) =>
            have _ : sliceWeight raws next < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            let inner := wordInlines argCtx s p
            let active ← modifierInlines ctx name style (edges [.word s p] raws[next]?) inner pos
            elabInlinesFrom ctx raws next (pushModifier (flushText acc sb) spec active inner) ""
          | _ =>
            diag ctx .E0304 s!"'\\{name}' needs an argument" pos
            elabInlinesFrom ctx raws (i + 1) acc sb
        else if let some decoration := decorationCtrls.lookup name then
          let head := selectorHead raws (i + 1)
          let j := head.2
          have hjge : i + 1 ≤ j := selectorHead_monotone raws (i + 1)
          let spec ← selectorSpec ctx head.1 pos
          match hj : raws[j]? with
          | some (.group body _) =>
            have hjlt := getElem?_lt hj
            have hw : rawWeightList body.toList < sliceWeight raws i :=
              body_lt_slice hj (by simp only [rawWeight]; omega) (by omega)
            let acc := flushText acc sb
            let inner ← elabInlinesCore ctx body
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1)
              (pushModifier acc spec #[.decorated decoration inner] inner) ""
          | some (.word s p) =>
            have hjlt := getElem?_lt hj
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1)
              (pushModifier (flushText acc sb) spec
                #[.decorated decoration (wordInlines ctx s p)] (wordInlines ctx s p)) ""
          | _ =>
            diag ctx .E0304 s!"'\\{name}' needs an argument" pos
            elabInlinesFrom ctx raws (i + 1) acc sb
        else if let some axes := phantomAxes.lookup name then
          -- A phantom's group is sizing alone: consumed unread, the run unbroken.
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
          | some (.word s wordPos) =>
            -- TeX takes one token: the word's first character, the rest still ships.
            have hjlt := getElem?_lt hj
            say true
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1)
              ((flushText acc sb).push (sourceInline ctx (wordPos.next false)
                (.text (s.drop 1).toString))) ""
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
            -- `resolveRefs` fills the number once every label is known.
            let acc := flushText acc sb ++ ctx.styles.linkInk "link" #[.ref key form "??" none]
            modify fun st => { st with refSites := st.refSites.push (key, form, pos) }
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1) acc ""
          | _ =>
            diag ctx .E0304 s!"'\\{name}' needs a \{key} group" pos
            elabInlinesFrom ctx raws (i + 1) acc sb
        else if name == "paragraph" || name == "subparagraph" then
          -- Run-in in article (classes.dtx: a negative afterskip of 1 em).
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
            let inner ← elabInlinesCore ctx body
            let acc := acc.push (← runInHead ctx name (j1 != j0) inner)
            -- The 1 em gap (classes.dtx) as U+2003, absorbing following spaces.
            let j2 := skipSpaces raws (j + 1)
            have hj2 := skipSpaces_ge raws (j + 1)
            have _ : sliceWeight raws j2 < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws j2 acc "\u2003"
          | _ =>
            diag ctx .E0304 s!"'\\{name}' needs a \{title}" pos
            elabInlinesFrom ctx raws (i + 1) acc sb
        else if name == "hyperlink" || name == "hypertarget" then
          let head := selectorHead raws (i + 1)
          let j := head.2
          have hjge : i + 1 ≤ j := selectorHead_monotone raws (i + 1)
          let spec ← selectorSpec ctx head.1 pos
          let j2 := skipSpaces raws (j + 1)
          have hj2ge := skipSpaces_ge raws (j + 1)
          match hj : raws[j]?, hj2 : raws[j2]? with
          | some (.group keyRaw _), some (.group body _) =>
            have _ : rawWeightList body.toList < sliceWeight raws i :=
              body_lt_slice hj2 (by simp only [rawWeight]; omega) (by omega)
            let key := argText ctx keyRaw
            let inner ← elabInlinesCore ctx body
            let acc := flushText acc sb
            let wrapped ← targetInlines ctx name key spec inner pos
            have _ : sliceWeight raws (j2 + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j2 + 1)
              (acc ++ wrapped) ""
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
            let inner ← elabInlinesCore ctx body
            have hadv : sliceWeight raws (j2 + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j2 + 1)
              (acc.push (.link (argText ctx urlRaw) (ctx.styles.linkInk "url" inner))) ""
          | some (.group urlRaw _), _ =>
            have hjlt := getElem?_lt hj
            let url := argText ctx urlRaw
            have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
              sliceWeight_lt raws h (by omega)
            elabInlinesFrom ctx raws (j + 1)
              ((flushText acc sb).push (.link url (ctx.styles.linkInk "url" #[.text url]))) ""
          | _, _ =>
            diag ctx .E0304 s!"'\\{name}' needs a URL group, optionally followed by text" pos
            elabInlinesFrom ctx raws (i + 1) acc sb
        else if name == "urlstyle" then
          -- url.sty's face selector; a group's end restores the face.
          let j := skipSpaces raws (i + 1)
          have hjge := skipSpaces_ge raws (i + 1)
          match hj : raws[j]? with
          | some (.group vRaw _) =>
            have hjlt := getElem?_lt hj
            let v := (Parse.rawSrc vRaw).trimAscii.toString
            match urlStyleFamily? v with
            | some fam => modify fun st => { st with scope := { st.scope with urlFamily := fam } }
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
          let j := skipSpaces raws (i + 1)
          have hjge := skipSpaces_ge raws (i + 1)
          let fam := (← get).scope.urlFamily
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
                (if name == "url" then .link url (ctx.styles.linkInk "url" #[set]) else set)) ""
          | _ =>
            diag ctx .E0304 s!"'\\{name}' needs a \{url} group" pos
            elabInlinesFrom ctx raws (i + 1) acc sb
        else if let some base := Ir.natbibCites.lookup name then
          let (nodes, ⟨j, hj⟩) ← citeArm ctx raws i name base pos
            fun sub _hsub => elabInlinesCore ctx sub
          have _ : sliceWeight raws j < sliceWeight raws i :=
            sliceWeight_lt raws h hj
          elabInlinesFrom ctx raws j (flushText acc sb ++ nodes) ""
        else
          elabInlinesCtrl ctx raws i acc sb name pos h hadv1
  else
    return mergeTexts (flushText acc sb)
termination_by (ctx.envLimit, ctx.limit, sliceWeight raws i, 3)
decreasing_by all_goals knot_dec

/-- The inline control-word arms for space, rules, graphics, icons, page
numbers, title data and colour. -/
private def elabInlinesCtrl (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (acc : Array Inline) (sb : String) (name : String) (pos : Pos)
    (h : i < raws.size)
    (hadv1 : sliceWeight raws (i + 1) < sliceWeight raws i) :
    EM (Array Inline) := do
  if name == "hspace" then
    let (node, ⟨j, hj⟩) ← hspaceArm ctx raws i pos
    let acc := flushText acc sb
    let acc := match node with | some x => acc.push x | none => acc
    have _ : sliceWeight raws j < sliceWeight raws i := sliceWeight_lt raws h hj
    elabInlinesFrom ctx raws j acc ""
  else if name == "rule" then
    let (node, ⟨j, hj⟩) ← ruleArm ctx raws i pos
    let acc := flushText acc sb
    let acc := match node with | some x => acc.push x | none => acc
    have _ : sliceWeight raws j < sliceWeight raws i := sliceWeight_lt raws h hj
    elabInlinesFrom ctx raws j acc ""
  else if name == "includegraphics" || name == "animategraphics" then
    let (node, ⟨j, hj⟩) ← imageArm ctx raws i pos (name == "animategraphics")
    let acc := flushText acc sb
    let acc := match node with | some x => acc.push x | none => acc
    have _ : sliceWeight raws j < sliceWeight raws i := sliceWeight_lt raws h hj
    elabInlinesFrom ctx raws j acc ""
  else if name == "faIcon" then
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
      let iconName := (argText ctx nameRaw).trimAscii.toString
        ++ (if alt then "-alt" else "")
      have _ : sliceWeight raws (j + 1) < sliceWeight raws i :=
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
    elabInlinesFrom ctx raws (i + 1)
      ((flushText acc sb).push (.icon e.scalar e.label)) ""
  else if let some m := Blueprint.Mark.ofName? name then
    if blueprintMarksOn ctx then
      let ⟨j, hj⟩ ← blueprintMarkArm ctx raws i m pos
      have _ : sliceWeight raws j < sliceWeight raws i := sliceWeight_lt raws h hj
      elabInlinesFrom ctx raws j acc sb
    else elabUnknownCtrl ctx raws i acc sb name pos h
  else if name == "pagenumber" then
    elabInlinesFrom ctx raws (i + 1) ((flushText acc sb).push .pageNumber) ""
  else if name == "pagecount" then
    elabInlinesFrom ctx raws (i + 1) ((flushText acc sb).push .pageCount) ""
  else if let some content := (← get).titleInsert? name then
    elabInlinesFrom ctx raws (i + 1) (flushText acc sb ++ content) ""
  else if name == "textcolor" then
    let head := selectorHead raws (i + 1)
    let j0 := head.2
    have hj0ge := selectorHead_monotone raws (i + 1)
    let spec ← selectorSpec ctx head.1 pos
    let model := (bracketRunSrc raws j0).map fun opt =>
      (rawSrc opt).trimAscii.toString
    let j := skipBracketRun raws j0
    have hjge : i + 1 ≤ j := Nat.le_trans hj0ge (skipBracketRun_ge raws j0)
    let j2 := skipSpaces raws (j + 1)
    have hj2ge := skipSpaces_ge raws (j + 1)
    match hj : raws[j]?, hj2 : raws[j2]? with
    | some (.group cname _), some (.group body _) =>
      have _ : rawWeightList body.toList < sliceWeight raws i :=
        body_lt_slice hj2 (by simp only [rawWeight]; omega) (by omega)
      have _ : sliceWeight raws (j2 + 1) < sliceWeight raws i :=
        sliceWeight_lt raws h (by omega)
      let source := argText ctx cname
      let label := match model with
        | some m => s!"{m}({source})"
        | none => source
      match ← readColor ctx ctx.palette model source pos with
      | .resolved c cssName =>
        recordColorSpan ctx label c cssName.isSome pos
        let acc := flushText acc sb
        let inner ← elabInlinesCore ctx body
        elabInlinesFrom ctx raws (j2 + 1)
          (pushModifier acc spec #[coloredRun ctx c cssName inner] inner) ""
      | .missing =>
        warnPaletteMiss ctx source pos
        let acc := flushText acc sb
        let inner ← elabInlinesCore ctx body
        elabInlinesFrom ctx raws (j2 + 1) (pushModifier acc spec inner inner) ""
      | .rejected =>
        let acc := flushText acc sb
        let inner ← elabInlinesCore ctx body
        elabInlinesFrom ctx raws (j2 + 1) (pushModifier acc spec inner inner) ""
    | _, _ =>
      diag ctx .E0304 "'\\textcolor' needs {name} and {content}" pos
      elabInlinesFrom ctx raws (i + 1) acc sb
  else
    elabInlinesCtrl2 ctx raws i acc sb name pos h hadv1
termination_by (ctx.envLimit, ctx.limit, sliceWeight raws i, 2)
decreasing_by all_goals knot_dec

/-- The inline control-word arms for colour declarations, overlays, notes and
recovery. -/
private def elabInlinesCtrl2 (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (acc : Array Inline) (sb : String) (name : String) (pos : Pos)
    (h : i < raws.size)
    -- knot_dec's `assumption` consumes it on the fall-through edges.
    (_hadv1 : sliceWeight raws (i + 1) < sliceWeight raws i) :
    EM (Array Inline) := do
  let inkMarker := (Marker.value? .ink name).isSome
  let source := (Marker.value? .ink name).getD name
  let read ← if inkMarker then
      readColor ctx ctx.palette none source pos
    else
      pure <| match ctx.palette.resolve source with
        | some c => .resolved c (ctx.palette.refOf? source)
        | none => .missing
  if let .resolved c cssName := read then

    -- `\color` took its argument already, so a group after it is content.
    recordColorSpan ctx source c cssName.isSome pos
    let j := if inkMarker then raws.size else skipSpaces raws (i + 1)
    have hjge : i + 1 ≤ j := by
      by_cases hk : inkMarker
      · simp only [j, hk, ↓reduceIte]; omega
      · simp only [j, hk, Bool.false_eq_true, ↓reduceIte]; exact skipSpaces_ge raws (i + 1)
    match hj : raws[j]? with
    | some (.group body _) =>
      have hjlt := getElem?_lt hj
      have hw : rawWeightList body.toList < sliceWeight raws i :=
        body_lt_slice hj (by simp only [rawWeight]; omega) (by omega)
      let acc := flushText acc sb
      let inner ← elabInlinesCore ctx body
      have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
        sliceWeight_lt raws h (by omega)
      elabInlinesFrom ctx raws (j + 1) (acc.push (coloredRun ctx c cssName inner)) ""
    | _ =>
      have _ : rawWeightList (raws.extract (i + 1) raws.size).toList
          < sliceWeight raws i :=
        extract_lt_slice raws.size h (Nat.lt_succ_self i)
      let (roles, acc, _) := inlineMacroStep ctx.macroRoles none (flushText acc sb) ""
      let ctx := { ctx with macroRoles := roles }
      let rest ← elabInlinesCore ctx (raws.extract (i + 1) raws.size)
      let acc := acc.push (coloredRun ctx c cssName rest)
      have _ : sliceWeight raws raws.size < sliceWeight raws i :=
        sliceWeight_lt raws h h
      elabInlinesFrom ctx raws raws.size acc ""
  else if inkMarker then
    match read with
    | .missing => warnPaletteMiss ctx source pos
    | _ => pure ()
    elabInlinesFrom ctx raws (i + 1) acc sb
  else if let some spec := Marker.value? .fontSize name then
    let style ← readFontSizeStyle ctx spec pos
    have _ : rawWeightList (raws.extract (i + 1) raws.size).toList
        < sliceWeight raws i :=
      extract_lt_slice raws.size h (Nat.lt_succ_self i)
    let (roles, acc, _) := inlineMacroStep ctx.macroRoles none (flushText acc sb) ""
    let ctx := { ctx with macroRoles := roles }
    let rest ← elabInlinesCore ctx (raws.extract (i + 1) raws.size)
    let acc := match style with
      | some s => acc.push (.styled s rest)
      | none => acc ++ rest
    have _ : sliceWeight raws raws.size < sliceWeight raws i :=
      sliceWeight_lt raws h h
    elabInlinesFrom ctx raws raws.size acc ""
  else if let some style := declStyleOf source then
    let (roles, acc, _) := inlineMacroStep ctx.macroRoles none (flushText acc sb) ""
    let ctx := { ctx with macroRoles := roles }
    let declCtx := { ctx with
      literalText := style == Style.mono || ctx.literalText }
    have hw : rawWeightList (raws.extract (i + 1) raws.size).toList
        < sliceWeight raws i :=
      extract_lt_slice raws.size h (Nat.lt_succ_self i)
    let rest ← elabInlinesCore declCtx (raws.extract (i + 1) raws.size)
    let acc := acc.push (.styled style rest)
    have _ : sliceWeight raws raws.size < sliceWeight raws i :=
      sliceWeight_lt raws h h
    elabInlinesFrom ctx raws raws.size acc ""
  else if name == "ifgiven" then
    let j := skipSpaces raws (i + 1)
    have hjge := skipSpaces_ge raws (i + 1)
    let j2 := skipSpaces raws (j + 1)
    have hj2ge := skipSpaces_ge raws (j + 1)
    match hj : raws[j]?, hj2 : raws[j2]? with
    | some (.group cond _), some (.group tmpl _) =>
      have _ : rawWeightList tmpl.toList < sliceWeight raws i :=
        body_lt_slice hj2 (by simp only [rawWeight]; omega) (by omega)
      have _ : sliceWeight raws (j2 + 1) < sliceWeight raws i :=
        sliceWeight_lt raws h (by omega)
      let refs := cond.filter (!isSpace ·)
      match refs.toList with
      | [.ctrl pname _] =>
        match ctx.args.find? (·.1 == pname) with
        | some (_, some _) =>
          let inner ← elabInlinesCore ctx tmpl
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
    let j := skipSpaces raws (i + 1)
    have hjge := skipSpaces_ge raws (i + 1)
    match raws[j]?.bind specWord? with
    | some w =>
      match overlaySpecFor name w with
      | some spec =>
        let j2 := skipSpaces raws (j + 1)
        have hj2ge := skipSpaces_ge raws (j + 1)
        match hj2 : raws[j2]? with
        | some (.group gbody _) =>
          have hj2lt := getElem?_lt hj2
          have hw : rawWeightList gbody.toList < sliceWeight raws i :=
            body_lt_slice hj2 (by simp only [rawWeight]; omega) (by omega)
          let acc := flushText acc sb
          let inner ← elabInlinesCore ctx gbody
          have hadv : sliceWeight raws (j2 + 1) < sliceWeight raws i :=
            sliceWeight_lt raws h (by omega)
          elabInlinesFrom ctx raws (j2 + 1) (acc.push (.onSteps spec inner)) ""
        | _ =>
          have _ : rawWeightList (raws.extract (j + 1) raws.size).toList
              < sliceWeight raws i :=
            extract_lt_slice raws.size h (by omega)
          let (roles, acc, _) := inlineMacroStep ctx.macroRoles none (flushText acc sb) ""
          let ctx := { ctx with macroRoles := roles }
          let inner ← elabInlinesCore ctx (raws.extract (j + 1) raws.size)
          have _ : sliceWeight raws raws.size < sliceWeight raws i :=
            sliceWeight_lt raws h h
          elabInlinesFrom ctx raws raws.size (acc.push (.onSteps spec inner)) ""
      | none =>
        warnOverlaySpec ctx w pos
        have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        elabInlinesFrom ctx raws (j + 1) acc sb
    | none =>
      elabInlinesFrom ctx raws (i + 1) acc sb
  else if name == "alt" then
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
        have _ : rawWeightList ga.toList < sliceWeight raws i :=
          body_lt_slice hj2 (by simp only [rawWeight]; omega) (by omega)
        have _ : rawWeightList gb.toList < sliceWeight raws i :=
          body_lt_slice hj3 (by simp only [rawWeight]; omega) (by omega)
        have _ : sliceWeight raws (j3 + 1) < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        let acc := flushText acc sb
        match spec with
        | some spec =>
          let ia ← elabInlinesCore ctx ga
          let ib ← elabInlinesCore ctx gb
          elabInlinesFrom ctx raws (j3 + 1) (acc.push (.alternate spec ia ib)) ""
        | none =>
          warnAltSpec ctx pos
          let ia ← elabInlinesCore ctx ga
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
        have _ : rawWeightList ga.toList < sliceWeight raws i :=
          body_lt_slice hj2 (by simp only [rawWeight]; omega) (by omega)
        have _ : sliceWeight raws (j3 + 1) < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        let acc := flushText acc sb
        warnAltSpec ctx pos
        let ia ← elabInlinesCore ctx ga
        elabInlinesFrom ctx raws (j3 + 1) (acc ++ ia) ""
      | _, _ =>
        diag ctx .E0304 "'\\alt' needs <spec>{content}{content}" pos
          (help := "'\\alt<2>{on step 2}{on the others}' takes a spec and TWO \
braced groups: the second is what every other step shows, so give it even \
when it is empty — '{}'")
        elabInlinesFrom ctx raws (i + 1) acc sb
  else if name == "pause" then
    warnOnce ctx "spec:pause-inline" .W0105
      "'\\pause' inside an argument cannot step; its content is shown" pos
    elabInlinesFrom ctx raws (i + 1) acc sb
  else if name == "note" then
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
        have _ : sliceWeight raws j < sliceWeight raws i :=
          sliceWeight_lt raws h (by omega)
        elabInlinesFrom ctx raws j acc sb
  else if name == "centering" then

    warnOnce ctx "ctrl:centering" .W0108
      "'\\centering' centres nothing inside an argument; content stays left-aligned" pos
      (help := "move '\\centering' to the start of the group or environment body")
    elabInlinesFrom ctx raws (i + 1) acc sb
  else if (Ir.raggedSideOf? name).isSome then
    warnOnce ctx ("ctrl:" ++ name) .W0108
      s!"'\\{name}' aligns nothing inside an argument; content keeps its alignment" pos
      (help := s!"move '\\{name}' to the start of the group or environment body")
    elabInlinesFrom ctx raws (i + 1) acc sb
  else if name == "footnote" then
    let override : Option Nat := footnoteOverride ctx raws (i + 1) pos
    let (⟨j1, hj1⟩, _, _) ← skipOptArg ctx name raws (i + 1) pos
    let j := skipSpaces raws j1
    have hjge := skipSpaces_ge raws j1
    match hj : raws[j]? with
    | some (.group body _) =>
      have hjlt := getElem?_lt hj
      have hw : rawWeightList body.toList < sliceWeight raws i :=
        body_lt_slice hj (by simp only [rawWeight]; omega) (by omega)
      if hasParRaw body then
        footnoteWarnPar ctx pos
      let acc := flushText acc sb
      -- A note sets on the page's ground; a card face keeps it in the flow.
      let inner ← elabInlinesCore { ctx with ground := if ctx.face then ctx.ground else none } body
      have hadv : sliceWeight raws (j + 1) < sliceWeight raws i :=
        sliceWeight_lt raws h (by omega)
      if ctx.face then
        footnoteWarnFace ctx pos
        elabInlinesFrom ctx raws (j + 1) (acc ++ inner) ""
      else
        let num ← footnoteStepNum override
        elabInlinesFrom ctx raws (j + 1) (acc.push (.footnote num inner)) ""
    | _ =>
      noteNeedsGroup ctx "footnote" pos
      elabInlinesFrom ctx raws (i + 1) acc sb
  else if name == "thanks" then
    thanksWarn ctx pos
    let j := skipSpaces raws (i + 1)
    have hjge := skipSpaces_ge raws (i + 1)
    match hj : raws[j]? with
    | some (.group body _) =>
      have _ : rawWeightList body.toList < sliceWeight raws i :=
        body_lt_slice hj (by simp only [rawWeight]; omega) (by omega)
      let acc := flushText acc sb
      let inner ← elabInlinesCore ctx body
      have _ : sliceWeight raws (j + 1) < sliceWeight raws i :=
        sliceWeight_lt raws h (by omega)
      elabInlinesFrom ctx raws (j + 1) (acc ++ inner) ""
    | _ =>
      noteNeedsGroup ctx "thanks" pos
      elabInlinesFrom ctx raws (i + 1) acc sb
  else if let some code := reservedCtrlAt raws i name pos then
    warnReservedCtrl ctx name code pos
    let jr := skipReservedArgs raws (i + 1) pos
    if let some bpos := jr.2 then
      warnUnclosed ctx s!"'\\{name}'" bpos
    have hge : i + 1 ≤ jr.1 := skipReservedArgs_ge raws (i + 1) pos 1
    have _ : sliceWeight raws jr.1 < sliceWeight raws i :=
      sliceWeight_lt raws h (by omega)
    elabInlinesFrom ctx raws jr.1 acc sb
  else if declCtrl.contains name || runningCtrl.contains name then
    warnMisplacedDecl ctx name pos
    let jr := skipReservedArgs raws (i + 1) pos (maxGroups := 2)
    if let some bpos := jr.2 then
      warnUnclosed ctx s!"'\\{name}'" bpos
    have hge : i + 1 ≤ jr.1 := skipReservedArgs_ge raws (i + 1) pos 2
    have _ : sliceWeight raws jr.1 < sliceWeight raws i :=
      sliceWeight_lt raws h (by omega)
    elabInlinesFrom ctx raws jr.1 acc sb
  else if blockOnly.contains name || bodyDefiner name then
    let ⟨k, hge⟩ ← inlineBlockOnly ctx raws name i pos
    have _ : sliceWeight raws k < sliceWeight raws i := sliceWeight_lt raws h (by omega)
    -- A definer's place keeps the spaces around it apart, as `{}` does.
    if bodyDefiner name then
      elabInlinesFrom ctx raws k (flushText acc sb) ""
    else elabInlinesFrom ctx raws k acc sb
  else if Compat.nativeReadCtrls.contains name ||
      (ctx.pic.tool.isSome && Compat.boundaryCtrls.contains name) then
    -- A picture set line's groups address the picture machinery, not text.
    let jr := skipReservedArgs raws (i + 1) pos
    if let some bpos := jr.2 then
      warnUnclosed ctx s!"'\\{name}'" bpos
    have hge : i + 1 ≤ jr.1 := skipReservedArgs_ge raws (i + 1) pos 1
    have _ : sliceWeight raws jr.1 < sliceWeight raws i :=
      sliceWeight_lt raws h (by omega)
    elabInlinesFrom ctx raws jr.1 acc sb
  else if (unknownCmdDiag name {}).1 == .W0301 && Compat.packageFile ctx.file &&
      Compat.codeInternal name && !ctx.atUse then
    -- premise: packageCodeChecks — a style's spans carry its own file
    let j0 := skipSpaces raws (i + 1)
    have hj0 := skipSpaces_ge raws (i + 1)
    let j1 := skipStar raws j0
    have hj1 := skipStar_ge raws j0
    let jr := skipOptionRuns raws j1 pos
    have hjr : j1 ≤ jr.1 := skipOptionRuns_ge raws j1 pos
    let ⟨j3, hj3⟩ ← recoverPackageCmd ctx name raws jr.1 pos
    if let some bpos := jr.2 then
      warnUnclosed ctx s!"'\\{name}'" bpos
    have _ : sliceWeight raws j3 < sliceWeight raws i :=
      sliceWeight_lt raws h (by omega)
    elabInlinesFrom ctx raws j3 acc sb
  else
    elabUnknownCtrl ctx raws i acc sb name pos h
termination_by (ctx.envLimit, ctx.limit, sliceWeight raws i, 1)
decreasing_by all_goals knot_dec

/-- The unknown-command recovery: the command and its option runs go, its
groups stay as content. -/
private def elabUnknownCtrl (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (acc : Array Inline) (sb : String) (name : String) (pos : Pos)
    (h : i < raws.size) : EM (Array Inline) := do
  let j0 := skipSpaces raws (i + 1)
  have hj0 := skipSpaces_ge raws (i + 1)
  let j1 := skipStar raws j0
  have hj1 := skipStar_ge raws j0
  let jr := skipOptionRuns raws j1 pos
  have hjr : j1 ≤ jr.1 := skipOptionRuns_ge raws j1 pos
  warnUnknownCmd ctx name (jr.1 > j1) pos
  if let some bpos := jr.2 then
    warnUnclosed ctx s!"'\\{name}'" bpos
  let j2 := skipSpaces raws jr.1
  have hj2 := skipSpaces_ge raws jr.1
  have _ : sliceWeight raws j2 < sliceWeight raws i :=
    sliceWeight_lt raws h (by omega)
  let (acc2, sb2, ⟨j3, hj3⟩, kept, sp) ← elabUnknownArgs ctx raws j2 0 acc sb false
  noteSalvage (unknownCmdDiag name (RunShape.one false)).1 name
    (Parse.rawSrc (raws.extract j2 j3))
  -- Restore the space the control word swallowed only when one stood there.
  let sbF := if kept > 0 && sp && j3 < raws.size then " " else sb2
  have _ : sliceWeight raws j3 < sliceWeight raws i :=
    sliceWeight_lt raws h (by omega)
  elabInlinesFrom ctx raws j3 acc2 sbF
termination_by (ctx.envLimit, ctx.limit, sliceWeight raws i, 0)
decreasing_by all_goals knot_dec


end

public def elabInlines (ctx : Ctx) (raws : Array Raw) : EM (Array Inline) :=
  elabInlinesCore ctx raws

unseal footnoteOverride hasParRaw footnoteWarnPar footnoteWarnFace
unseal thanksWarn footnoteStepNum noteNeedsGroup warnUnknownCmd noteSalvage recoverPackageCmd
unseal warnMisplacedDecl warnReservedCtrl optionRunAdvice optionRunClause
unseal warnPaletteMiss warnOverlaySpec warnAltSpec targetInlines
unseal argText skipBracketRun bracketRunSrc
unseal imageArm
unseal warnUnclosed warnDroppedArgs
unseal refCtrlForm? refFormNeedsKind
unseal secFmtOfBody applySecFmt applyCounter counterCtrl counterArm runInHead
unseal splitPictureAlt subsetPicture routePicture inlinePicture
unseal inlineVerbatim
unseal theCounterLevel? sectionLevel
unseal inlineGroup

/-- Whether an inline control word reaches the unknown-command recovery. -/
public def recoversInlineName (ctx : Ctx) (name : String) : Bool :=
  Compat.overlayName name == name &&
  (ctx.args.find? (·.1 == name)).isNone && (lookupUser ctx name).isNone &&
  !["hfill", "qedhere", "ensuremath", "\\", "par", "label", "paragraph",
    "subparagraph", "hyperlink", "hypertarget", "href", "link", "urlstyle", "url",
    "nolinkurl", "hspace", "rule", "includegraphics", "animategraphics", "faIcon",
    "pagenumber", "pagecount", "textcolor", "ifgiven", "alt", "pause", "note",
    "centering", "footnote", "thanks"].contains name &&
  (accentMarkOf name).isNone && (escapeOf name).isNone &&
  (Lex.textSymbols.lookup name).isNone && (modifierStyle? name).isNone &&
  (decorationCtrls.lookup name).isNone && (phantomAxes.lookup name).isNone &&
  (refCtrlForm? name).isNone && (Ir.natbibCites.lookup name).isNone &&
  (FaIcons.byMacro.get[name]?).isNone && (Blueprint.Mark.ofName? name).isNone &&
  (if name.startsWith "insertshort" then
      TitleDatum.ofName? (name.drop "insertshort".length).copy
    else if name.startsWith "insert" then
      TitleDatum.ofName? (name.drop "insert".length).copy
    else none).isNone &&
  (Marker.value? .ink name).isNone && (ctx.palette.resolve name).isNone &&
  (Marker.value? .fontSize name).isNone && (declStyleOf name).isNone &&
  !(overlayCtrls.contains name) && (Ir.raggedSideOf? name).isNone &&
  (reservedCtrl.lookup name).isNone &&
  !(declCtrl.contains name || runningCtrl.contains name) &&
  !(blockOnly.contains name || bodyDefiner name) &&
  !(Compat.nativeReadCtrls.contains name ||
    (ctx.pic.tool.isSome && Compat.boundaryCtrls.contains name)) &&
  !((unknownCmdDiag name {}).1 == .W0301 && Compat.packageFile ctx.file &&
    Compat.codeInternal name && !ctx.atUse)

private theorem elabInlinesCtrl2_unknown (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (acc : Array Inline) (sb name : String) (pos : Pos) (h : i < raws.size)
    (ha : sliceWeight raws (i + 1) < sliceWeight raws i)
    (hn : recoversInlineName ctx name = true) :
    elabInlinesCtrl2 ctx raws i acc sb name pos h ha =
      elabUnknownCtrl ctx raws i acc sb name pos h := by
  simp only [recoversInlineName, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none, List.contains_cons, List.contains_nil,
    Bool.or_eq_false_iff, Bool.or_false] at hn
  rw [elabInlinesCtrl2]
  simp only [hn, reservedCtrlAt, Bool.false_and, Bool.false_eq_true, ↓reduceIte, pure_bind,
    Option.isSome_none, Bool.false_or, Option.getD_none]

private theorem recoversInlineName_title (ctx : Ctx) (name : String)
    (hn : recoversInlineName ctx name = true) (st : ESt) :
    st.titleInsert? name = none := by
  simp only [recoversInlineName, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at hn
  have ht : (if name.startsWith "insertshort" then
      TitleDatum.ofName? (name.drop "insertshort".length).copy
    else if name.startsWith "insert" then
      TitleDatum.ofName? (name.drop "insert".length).copy
    else none) = none := by simp only [hn]
  unfold ESt.titleInsert?
  split
  · rename_i hs
    simp only [hs, ↓reduceIte] at ht
    simp only [ht, bind, Option.bind]
  · rename_i hs
    split
    · rename_i hi
      simp only [hs, hi, Bool.false_eq_true, ↓reduceIte] at ht
      simp only [ht, bind, Option.bind]
    · rfl

private theorem elabInlinesCtrl_unknown (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (acc : Array Inline) (sb name : String) (pos : Pos) (h : i < raws.size)
    (ha : sliceWeight raws (i + 1) < sliceWeight raws i)
    (hn : recoversInlineName ctx name = true) :
    elabInlinesCtrl ctx raws i acc sb name pos h ha =
      elabUnknownCtrl ctx raws i acc sb name pos h := by
  have ht := recoversInlineName_title ctx name hn
  have htail := elabInlinesCtrl2_unknown ctx raws i acc sb name pos h ha hn
  simp only [recoversInlineName, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none, List.contains_cons, List.contains_nil,
    Bool.or_eq_false_iff, Bool.or_false] at hn
  rw [elabInlinesCtrl]
  simp only [hn, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
  funext st
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure]
  rw [ht st, htail]

private theorem elabInlinesFrom_unknown_exact (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (acc : Array Inline) (sb name : String) (pos : Pos) (h : i < raws.size)
    (hr : raws[i] = .ctrl name pos) (hn : recoversInlineName ctx name = true) :
    elabInlinesFrom ctx raws i acc sb =
      let (roles, acc', sb') := inlineMacroAt ctx.macroRoles raws i acc sb
      elabUnknownCtrl {ctx with macroRoles := roles} raws i acc' sb' name pos h := by
  rw [elabInlinesFrom]
  generalize inlineMacroAt ctx.macroRoles raws i acc sb = state
  rcases state with ⟨roles, acc', sb'⟩
  dsimp only
  rw [dite_eq_left h, hr]
  have hn' : recoversInlineName {ctx with macroRoles := roles} name = true := hn
  have htail := elabInlinesCtrl_unknown {ctx with macroRoles := roles}
    raws i acc' sb' name pos h (sliceWeight_lt raws h (Nat.lt_succ_self i)) hn'
  simp only [recoversInlineName, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none, List.contains_cons, List.contains_nil,
    Bool.or_eq_false_iff, Bool.or_false, beq_iff_eq] at hn'
  have haccent : raws[i + 1]?.bind (accentCompose name) = none := by
    have hm : accentMarkOf name = none := by simp only [hn']
    have ha : ∀ raw, accentCompose name raw = none := by
      intro raw
      simp only [accentCompose, hm, bind, Option.bind]
    cases raws[i + 1]? <;> simp only [Option.bind, ha]
  have hu : lookupUser {ctx with macroRoles := roles} name = none := by
    simp only [hn']
  simp only [hn', haccent, Bool.false_eq_true, ↓reduceIte, Bool.false_or,
    Option.isSome_none, htail]
  rw [hu]
  simp only [dite_false]

private theorem elabInlines_unknown_exact (file name : String) (raws : Array Raw)
    (pos : Pos) (h : 0 < raws.size) (hr : raws[0] = .ctrl name pos)
    (hp : pos.origins = []) (hn : recoversInlineName {file} name = true) :
    elabInlines {file} raws = (do
      let out ← elabUnknownCtrl {file} raws 0 #[] "" name pos h
      pure (out.map (mapSmartText none))) := by
  rw [elabInlines, elabInlinesCore]
  simp only [MacroRoles.enter, MacroRoles.empty, List.map_nil, List.append_nil]
  have hn' : recoversInlineName {file, macroRoles := {}} name = true := by
    simpa only [MacroRoles.empty] using hn
  rw [elabInlinesFrom_unknown_exact _ _ _ _ _ _ _ h hr hn']
  have hr' : raws[0]? = some (.ctrl name pos) := by
    rw [Array.getElem?_eq_getElem h, hr]
  simp only [inlineMacroAt, hr', inlineMacroStep, Raw.origins?, hp,
    relativeOrigins, List.map_nil]
  rfl

private theorem elabInlinesFrom_done_exact (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (acc : Array Inline) (sb : String) (h : raws.size ≤ i) :
    elabInlinesFrom ctx raws i acc sb =
      let (_, acc', sb') := inlineMacroAt ctx.macroRoles raws i acc sb
      pure (mergeTexts (flushText acc' sb')) := by
  rw [elabInlinesFrom]
  simp only [show ¬ i < raws.size from Nat.not_lt_of_ge h, dite_false]

private theorem elabInlines_word_exact (file w : String) (p : Pos) (hp : p.origins = []) :
    elabInlines {file} #[.word w p] =
      pure (#[sourceInline {file} p (.text w)].map (mapSmartText none)) := by
  rw [elabInlines, elabInlinesCore, elabInlinesFrom]
  simp [inlineMacroAt, inlineMacroStep, MacroRoles.enter, MacroRoles.empty, Raw.origins?,
    relativeOrigins, hp, flushText]
  rw [elabInlinesFrom_done_exact _ _ _ _ _ (by simp)]
  simp [inlineMacroAt, inlineMacroStep, flushText, mergeTexts]

private theorem elabUnknownArgs_end_exact (ctx : Ctx) (raws : Array Raw)
    (j count : Nat) (acc : Array Inline) (sb : String) (spaceAfter : Bool)
    (h : raws.size ≤ j) :
    elabUnknownArgs ctx raws j count acc sb spaceAfter =
      pure (acc, sb, ⟨j, Nat.le_refl j⟩, count, spaceAfter) := by
  rw [elabUnknownArgs]
  split
  · rfl
  · split
    · rename_i body pos hj
      have hn : raws[j]? = none := Array.getElem?_eq_none h
      rw [hj] at hn
      cases hn
    · rfl

private theorem elabUnknownArgs_last_group_exact (ctx : Ctx) (raws : Array Raw)
    (j : Nat) (body : Array Raw) (pos : Pos) (acc : Array Inline) (sb : String)
    (spaceAfter : Bool) (hg : raws[j]? = some (.group body pos))
    (hend : raws.size ≤ j + 1) :
    elabUnknownArgs ctx raws j 0 acc sb spaceAfter =
      (do
        let inner ← inlineGroup ctx.palette (elabInlines ctx body)
        pure (flushText acc sb ++ inner, "", ⟨j + 1, by omega⟩, 1, false)) := by
  have hs : skipSpaces raws (j + 1) = j + 1 := by
    rw [skipSpaces]
    simp [show ¬ j + 1 < raws.size from by omega]
  rw [elabUnknownArgs]
  simp only [show ¬ 9 ≤ 0 from by omega, ↓reduceIte]
  rw [hg]
  dsimp only
  simp only [show ¬ (0 : Nat) > 0 from by omega, ↓reduceIte,
    show ∀ a : Array Inline, flushText a "" = a from fun _ => rfl]
  simp only [elabUnknownArgs_end_exact _ _ _ _ _ _ _
    (Nat.le_trans hend (skipSpaces_ge raws (j + 1))), pure_bind]
  simp only [elabInlines, hs, bne_self_eq_false]

private theorem elabUnknownCtrl_option_run_exact (file name w kept : String)
    (acc : Array Inline) (sb : String) (st : ESt) :
    ((elabUnknownCtrl {file}
        #[.ctrl name {line := 1, col := 1}, .sym '[' {line := 1, col := 5},
          .word w {line := 1, col := 6}, .sym ']' {line := 1, col := 7},
          .group #[.word kept {line := 1, col := 9}] {line := 1, col := 8}]
        0 acc sb name {line := 1, col := 1} (by simp)).run st).1 =
    ((elabUnknownCtrl {file}
        #[.ctrl name {line := 1, col := 1},
          .group #[.word kept {line := 1, col := 9}] {line := 1, col := 8}]
        0 acc sb name {line := 1, col := 1} (by simp)).run st).1 := by
  let xs : Array Raw :=
    #[.ctrl name {line := 1, col := 1}, .sym '[' {line := 1, col := 5},
      .word w {line := 1, col := 6}, .sym ']' {line := 1, col := 7},
      .group #[.word kept {line := 1, col := 9}] {line := 1, col := 8}]
  let ys : Array Raw :=
    #[.ctrl name {line := 1, col := 1},
      .group #[.word kept {line := 1, col := 9}] {line := 1, col := 8}]
  change ((elabUnknownCtrl {file} xs 0 acc sb name {} _).run st).1 =
    ((elabUnknownCtrl {file} ys 0 acc sb name {} _).run st).1
  have sx1 : skipSpaces xs 1 = 1 := by rw [skipSpaces]; rfl
  have sx4 : skipSpaces xs 4 = 4 := by rw [skipSpaces]; rfl
  have sy1 : skipSpaces ys 1 = 1 := by rw [skipSpaces]; rfl
  have close : closeBracketFrom xs 2 = some 3 := by
    rw [closeBracketFrom]
    change closeBracketFrom xs 3 = some 3
    rw [closeBracketFrom]
    rfl
  have scan1 : scanBracketArg xs 1 {} = .took 4 := by
    unfold scanBracketArg
    rw [sx1]
    change (match closeBracketFrom xs 2 with
      | some c => ArgScan.took (c + 1) | none => .unclosed {col := 5}) = .took 4
    rw [close]
  have scan4 : scanBracketArg xs 4 {} = .content := by
    unfold scanBracketArg
    rw [sx4]
    rfl
  have opt4 : skipOptionRuns xs 4 {} = (4, none) := by
    rw [skipOptionRuns, scan4]
  have opt1 : skipOptionRuns xs 1 {} = (4, none) := by
    rw [skipOptionRuns, scan1]
    exact opt4
  have noopt : skipOptionRuns ys 1 {} = (1, none) := by
    rw [skipOptionRuns]
    have scan : scanBracketArg ys 1 {} = .content := by
      unfold scanBracketArg
      rw [sy1]
      rfl
    rw [scan]
  have starx : skipStar xs 1 = 1 := by rfl
  have stary : skipStar ys 1 = 1 := by rfl
  have ax : elabUnknownArgs {file} xs 4 0 acc sb false =
      pure (flushText acc sb ++ #[sourceInline {file} {col := 9} (.text kept)].map (mapSmartText none),
        "", ⟨5, by omega⟩, 1, false) := by
    rw [elabUnknownArgs_last_group_exact _ _ _ _ _ _ _ _ rfl (by simp [xs]),
      elabInlines_word_exact file kept {col := 9} rfl, inlineGroup_pure]
    simp only [pure_bind]
  have ay : elabUnknownArgs {file} ys 1 0 acc sb false =
      pure (flushText acc sb ++ #[sourceInline {file} {col := 9} (.text kept)].map (mapSmartText none),
        "", ⟨2, by omega⟩, 1, false) := by
    rw [elabUnknownArgs_last_group_exact _ _ _ _ _ _ _ _ rfl (by simp [ys]),
      elabInlines_word_exact file kept {col := 9} rfl, inlineGroup_pure]
    simp only [pure_bind]
  have ax0 : elabUnknownArgs {file} xs
      (skipSpaces xs (skipOptionRuns xs (skipStar xs (skipSpaces xs 1)) {}).1)
      0 acc sb false =
      pure (flushText acc sb ++ #[sourceInline {file} {col := 9} (.text kept)].map (mapSmartText none),
        "", ⟨5, by simp only [sx1, starx, opt1, sx4]; omega⟩, 1, false) := by
    have atIndex (j : Nat) (hj : j = 4) :
        elabUnknownArgs {file} xs j 0 acc sb false =
          pure (flushText acc sb ++ #[sourceInline {file} {col := 9} (.text kept)].map (mapSmartText none),
            "", ⟨5, by omega⟩, 1, false) := by
      subst j
      exact ax
    exact atIndex _ (by simp only [sx1, starx, opt1, sx4])
  have ay0 : elabUnknownArgs {file} ys
      (skipSpaces ys (skipOptionRuns ys (skipStar ys (skipSpaces ys 1)) {}).1)
      0 acc sb false =
      pure (flushText acc sb ++ #[sourceInline {file} {col := 9} (.text kept)].map (mapSmartText none),
        "", ⟨2, by simp only [sy1, stary, noopt]; omega⟩, 1, false) := by
    have atIndex (j : Nat) (hj : j = 1) :
        elabUnknownArgs {file} ys j 0 acc sb false =
          pure (flushText acc sb ++ #[sourceInline {file} {col := 9} (.text kept)].map (mapSmartText none),
            "", ⟨2, by omega⟩, 1, false) := by
      subst j
      exact ay
    exact atIndex _ (by simp only [sy1, stary, noopt])
  rw [elabUnknownCtrl, elabUnknownCtrl]
  simp! only [Nat.reduceAdd, sx1, sy1, starx, stary, opt1, noopt, Prod.fst, Prod.snd, sx4]
  rw [ax0, ay0]
  simp only [pure_bind, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [elabInlinesFrom_done_exact _ xs 5 _ _ (by simp [xs]),
    elabInlinesFrom_done_exact _ ys 2 _ _ (by simp [ys])]
  simp [inlineMacroAt, inlineMacroStep, xs, ys, flushText,
    StateT.run, bind, StateT.bind, pure, StateT.pure]
  split; split; split <;> split <;> rfl

/-- A closed leading option of an unregistered command adds no inline
content. -/
public theorem elabInlines_option_run_exact (file name w kept : String) (st : ESt)
    (hn : recoversInlineName {file} name = true) :
    ((elabInlines {file}
        #[.ctrl name {line := 1, col := 1}, .sym '[' {line := 1, col := 5},
          .word w {line := 1, col := 6}, .sym ']' {line := 1, col := 7},
          .group #[.word kept {line := 1, col := 9}] {line := 1, col := 8}]).run st).1 =
    ((elabInlines {file}
        #[.ctrl name {line := 1, col := 1},
          .group #[.word kept {line := 1, col := 9}] {line := 1, col := 8}]).run st).1 := by
  rw [elabInlines_unknown_exact _ _ _ _ (by simp) rfl rfl hn,
    elabInlines_unknown_exact _ _ _ _ (by simp) rfl rfl hn]
  have heq := elabUnknownCtrl_option_run_exact file name w kept #[] "" st
  simp only [StateT.run] at heq
  simp only [StateT.run, bind, StateT.bind, pure, StateT.pure]
  split
  split
  simp_all only


public theorem unknownCmdDiag_code_exact (name : String) (shape : RunShape) :
    (unknownCmdDiag name shape).1 =
      (if name == "footnotemark" || name == "footnotetext" then .W0370 else .W0301) := by
  unfold unknownCmdDiag
  split <;> rfl

private theorem unknownCmdDiag_shape_id (name : String) (shape : RunShape) :
    (unknownCmdDiag name shape).1 = (unknownCmdDiag name {}).1 := by
  rw [unknownCmdDiag_code_exact, unknownCmdDiag_code_exact]

private theorem warnUnknownCmd_push_exact (ctx : Ctx) (name : String) (optionRun : Bool)
    (pos : Pos) (st : ESt) :
    ∃ d, ((warnUnknownCmd ctx name optionRun pos).run st).2.diags.size
          = st.diags.size + 1 ∧
      ((warnUnknownCmd ctx name optionRun pos).run st).2.diags.back? = some d ∧
      d.kind = (unknownCmdDiag name (RunShape.one optionRun)).1 ∧
      d.subject = some ("ctrl:" ++ name) := by
  have hrun : ((warnUnknownCmd ctx name optionRun pos).run st).2.diags =
      (warnOnceState ctx ("ctrl:" ++ name)
        (unknownCmdDiag name (RunShape.one optionRun)).1
        (unknownCmdDiag name (RunShape.one optionRun)).2.1 pos
        (unknownCmdDiag name (RunShape.one optionRun)).2.2
        ((unknownCmdDiag name (RunShape.one optionRun)).1 == .W0301 &&
          Compat.styInternal ctx.file name)
        (bumpRunShape name ("ctrl:" ++ name) optionRun st)).diags := by rfl
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
    simp [warnOnceKey]

/-- A LaTeX internal in package code records no salvage, pushes exactly one
diagnostic, and consumes only spaces and at most nine argument groups. -/
public theorem recoverPackageCmd_accounts (ctx : Ctx) (name : String) (raws : Array Raw)
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
          (some (unknownCmdHelp name false)) (Compat.styInternal ctx.file name) st) := by rfl
  rw [hrun]
  obtain ⟨h1, h2, h3⟩ := argGroupsEnd_covers raws j 9
  exact ⟨rfl, ⟨_, warnOnceState_diags_exact .., warnOnceDiag_kind_exact ..,
    warnOnceDiag_subject_exact ..⟩, h1, h2, h3⟩

/-- Binds declared parameters from the call site, returning the bindings and
the index past the consumed arguments. -/
private def takeArgs (ctx : Ctx) (params : Array Param) (name : String)
    (raws : Array Raw) (start : Nat) (pos : Pos) :
    EM (Array (String × Option (Array Inline)) × Nat) := do
  let (bs, ⟨j, _⟩) ← takeArgsFrom ctx params 0 name raws start pos #[]
  return (bs, j)

private theorem take_args_consumes_forward
    (ctx : Ctx) (params : Array Param) (name : String)
    (raws : Array Raw) (start : Nat) (pos : Pos) (st : ESt) :
    start ≤ ((takeArgs ctx params name raws start pos).run st).1.2 := by
  unfold takeArgs
  rcases h : (takeArgsFrom ctx params 0 name raws start pos #[]).run st
    with ⟨⟨bs, j, hj⟩, st'⟩
  simp [StateT.run, bind, StateT.bind, pure, StateT.pure] at h ⊢
  rw [h]
  exact hj

/-- Environments whose content is a block sequence. -/
private def blockEnvs : List String :=
  ["itemize", "enumerate", "center", "flushleft", "flushright", "document", "frame",
   "columns", "tabularx", "figure",
   "figure*", "table", "table*", "quote", "quotation", "verse", "description",
   "thebibliography", "abstract", "ifbackend",
   "nav", "minipage", "block", "alertblock", "exampleblock", "appendices"]

private def titledKind? : String → Option Ir.TitledKind
  | "block" => some .block
  | "alertblock" => some .alert
  | "exampleblock" => some .example
  | n => if n == Tcolorbox.boxEnv then some .box else none

/-- Environment names a document cannot redefine. -/
public def builtinEnvNames : List String :=
  blockEnvs ++ (alignEnvs.map (·.1)) ++ (displayMathEnvs.map (·.1)) ++
  ["verbatim", "tabular", "tabular*", "column", "array",
   "algorithm", "algorithm*", "algorithm2e", "algorithmic"] ++
  reservedEnv

/-- The names the engine defines before the document, which a document's `\providecommand` leaves
as they are. -/
private def providedNames : List String :=
  renderedBuiltins ++ structuralNames ++ builtinEnvNames.map Tcolorbox.bindingName

/-- The built-ins whose every definition is ignored whole, environments as their binding name:
an abstract's redefinition is read for its heading and size, a float's for its kernel core. -/
public def ignoredDefNames : List String :=
  structuralNames ++ (builtinEnvNames.filter fun e =>
    e != "abstract" && !Compat.floatRedefEnvs.contains e).map Tcolorbox.bindingName

private def _root_.LeanTex.Core.Ir.PageSpec.textWidth (p : PageSpec) : Sp :=
  p.width - 2 * p.hmargin

private def _root_.LeanTex.Core.Ir.PageSpec.textHeight (p : PageSpec) : Sp :=
  p.height - 2 * p.vmargin

/-- The class's page for a declared spec and options: every value the
document declared is kept, the rest take the class's defaults. -/
private def classPageDefaults (record : Ir.ClassRecord) (opts : List String)
    (page : PageSpec) : PageSpec := Id.run do
  let dflt : PageSpec := {}
  let mut page := page
  if record.model == .flow then
    if page.width == dflt.width && page.height == dflt.height then
      let sized := opts.findSome? fun o =>
        let o := match KeyVal.entry o with
          | ("paper", some v) => v ++ "paper"
          | (k, none) => k
          | _ => o
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
    -- beamer.cls sets `\raggedright` for every frame.
    if page.justify.isNone then
      page := { page with justify := some false }
    page := { page with raggedFil := true }
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

/-- Class options asking for what a page model's class already is, each with why. -/
public def classOptionsInert : List (Ir.PageModel × List (String × String)) :=
  let final := ("final", "the document is rendered in full, as without the option")
  let opensNoPage := "a part or chapter here opens no page of its own, so where one would open \
changes nothing"
  [(.flow, [("oneside", "the page is one-sided, as without the option"),
     ("twoside=false", "the page is one-sided, as without the option"),
     ("onecolumn", "the text is set in one column, as without the option"),
     final,
     ("reqno", "equation numbers stand on the right, as without the option"),
     ("openany", opensNoPage), ("open=any", opensNoPage), ("headings=openany", opensNoPage),
     ("titlepage=false", "the title opens the first page, as without the option"),
     ("version=last", "the layout is KOMA-Script's current one, as without the option"),
     ("footinclude=false", "the foot stands below the text block, as without the option")]),
   (.frame, [final, ("c", "frames are centred vertically, as without the option"),
     ("slidescentered", "frames are centred vertically, as without the option"),
     ("unicode", "the PDF's text strings are Unicode, as without the option"),
     ("presentation", "the slides are set for presenting, as without the option")]),
   (.face, [final])]

/-- The bare class options each page model's readers read beside a body size and a paper size. -/
public def classOptionFlags : List (Ir.PageModel × List String) :=
  [(.flow, ["landscape", "twoside"]), (.frame, ["t", "slidestop", "noamsthm"]),
   (.face, ["us", "jis"])]

/-- The class options the abstract's form reads in the flow model (`abstractFormUnder`). -/
public def abstractFormOptions : List String := ["titlepage", "notitlepage"]

/-- The paper sizes a class option names, each as `<size>paper`. -/
public def classPaperOptions : List String := pageSizes.map (·.1 ++ "paper")

/-- Whether a reader here reads a class option under a page model: a body size; in the flow model
a paper size, `landscape`, `twoside` and the abstract's title-page options; in the frame model the
slide stage, its alignment and `noamsthm`; in the face model a card standard. -/
public def classOptionRead (model : Ir.PageModel) (o : String) : Bool :=
  let sized (v : String) : Bool := v.endsWith "pt" && ((v.dropEnd 2).toString.toNat?.any (0 < ·))
  let paper (v : String) : Bool := (pageSizes.lookup v).isSome
  match KeyVal.entry o, model with
  | ("fontsize", some v), _ => sized v
  | (k, none), .flow =>
    sized k || (k.endsWith "paper" && paper (k.dropEnd "paper".length).toString) ||
      (classOptionFlags.lookup .flow).any (·.contains k) || abstractFormOptions.contains k
  | (k, none), m => sized k || (classOptionFlags.lookup m).any (·.contains k)
  | (k, some v), .flow => (k == "paper" && paper v) || (k == "twoside" && v == "true")
  | (k, some v), .frame => k == "aspectratio" && (Ir.slidesStageNamed v).isSome
  | (_, some _), .face => false

/-- A box's declared width: a length, a fraction of the enclosing measure,
or a parameterless command's body read once; `none` when unreadable. -/
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

/-- Whether one raw makes a body block content, as `elabBlocks`' boundary
rule reads it. -/
private def bodyIsBlockOne : Raw → Bool
  | .ctrl n _ =>
    n == "block" || n == "par" || n == "framefoot" || n == "pagebreak"
      || n == "bibliography" || n == Parse.markdownBibControl || n == "bibliographystyle"
      || n == Parse.citeSetupMark
      -- Definitions and counter commands expand only through the block walk.
      || n == "define" || counterCtrl n
      || (Compat.lengthRestoreKeys? n).isSome
      || (blockHeading? n).isSome
  | .par _ => true
  | .verb env _ _ => env != "verb" && env != "mintinline"
  | .math display _ _ => display
  | .env n body _ =>
    if (Parse.inputEnvFile? n).isSome then bodyIsBlockList body.toList
    else
      blockEnvs.contains n || isMathEnv n || n == Tcolorbox.boxEnv
        || n == "tabular" || n == "tabular*" || Parse.markdownEnv n || n == Parse.linesEnv
        || n == "algorithm" || n == "algorithm*" || n == "algorithm2e"
        || n == "algorithmic"
        || reservedEnv.contains n || bodyIsBlockList body.toList
  | .group body _ => bodyIsBlockList body.toList
  | _ => false

private def bodyIsBlockList : List Raw → Bool
  | [] => false
  | r :: rest => bodyIsBlockOne r || bodyIsBlockList rest

end

public def bodyIsBlock (raws : Array Raw) : Bool :=
  bodyIsBlockList raws.toList

/-- Whether the overlay command at `i` takes the block path: a group by its
shape, the open form only where no paragraph has begun. -/
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

/-- Whether a two-group content wrapper's second group is block-shaped. -/
private def contentWrapperTakesBlocks (n : String) (raws : Array Raw) (i : Nat) : Bool :=
  let j := (linkSelectorHead n raws (i + 1)).2
  let j2 := skipSpaces raws (j + 1)
  match raws[j]?, raws[j2]? with
  | some (.group _ _), some (.group body _) => bodyIsBlock body
  | _, _ => false

/-- The number a heading prints, stepped in flow order; `none` when starred, past `secnumdepth`, in
a class that does not number, or in a deck, which steps every section for `\ref` and prints none. -/
private def sectionNumber (ctx : Ctx) (level : Nat) (starred : Bool) :
    EM (Option String) := do
  let st ← get
  let deck := ctx.slides
  if deck && level == 1 then modify fun st => { st with sectionsSeen := (true, st.sectionsSeen.2) }
  if deck && level == 2 then modify fun st => { st with sectionsSeen := (st.sectionsSeen.1, true) }
  if (starred && !deck) || (!ctx.numberHeadings && !deck) || level == 0 || level > 3 ||
      (level : Int) > st.ctr.secDepth then
    return none
  let (s1, s2, s3) := st.ctr.secNums
  let nums := match level with
    | 1 => (s1 + 1, 0, 0)
    | 2 => (s1, s2 + 1, 0)
    | _ => (s1, s2, s3 + 1)
  -- beamer's `\thesubsection` is `\arabic{subsection}` alone
  let num := if deck && (st.ctr.secFmts.findRev? (·.1 == level)).isNone then
      ListMark.arabicN (counterAt nums level)
    else renderSecLevel st.ctr.secFmts nums st.ctr.inAppendix secFmtFuel level
  modify fun st => { st with ctr := { st.ctr with secNums := nums, runNums := (0, 0) }
                             refTarget := some { kind := some .heading, num := num } }
  return if deck then none else some num

/-- Whether raws open with a `{frame}` group, as an environment's begin half spells `\begin{frame}`. -/
private def opensFrameGroup : List Raw → Bool
  | .group g _ :: _ => g.size == 1 && (g[0]? matches some (Raw.word "frame" _))
  | _ => false

mutual

/-- Whether code sets a page of its own: a frame, a section page outside one, or a command or
environment of the document's that does. -/
private def hookSetsPageOne (cmds envs : String → Bool) : Raw → Bool
  | .ctrl n _ =>
    n == "frame" || n == "againframe" || n == "sectionpage" || n == "subsectionpage" || cmds n
  | .env n body _ => n == "frame" || envs n || hookSetsPageList cmds envs body.toList
  | .group body _ => hookSetsPageList cmds envs body.toList
  | .word .. | .space | .par _ | .sym .. | .math .. | .verb .. => false

private def hookSetsPageList (cmds envs : String → Bool) : List Raw → Bool
  | [] => false
  | r :: rest =>
    hookSetsPageOne cmds envs r || (r matches .ctrl "begin" _ && opensFrameGroup rest) ||
      hookSetsPageList cmds envs rest

end

/-- Whether each command and environment the document defines sets a page of its own, a command
reading only those defined before it. -/
private def pageDefs (ctx : Ctx) : Array Bool × Array Bool := Id.run do
  let mut cmds : Array Bool := #[]
  for h : j in [0:ctx.user.size] do
    let seen := cmds
    let sets := fun n => ((latestNamed (·.name) ctx.user n j).bind fun (k, _) => seen[k]?) == some true
    cmds := cmds.push (hookSetsPageList sets (fun _ => false) ctx.user[j].body.toList)
  let sets := fun n => ((lookupUser ctx n).bind fun (k, _) => cmds[k]?) == some true
  return (cmds, ctx.userEnvs.map fun e =>
    hookSetsPageList sets (fun _ => false) (e.beginBody ++ e.endBody).toList)

/-- A hook's `[starred]` code, its `{code}` group and the index past them, after its control word. -/
private def hookArgsAt (raws : Array Raw) (i : Nat) :
    Option (Array Raw) × Option (Array Raw) × Nat :=
  let j0 := skipSpaces raws i
  let (starred, j1) := if raws[j0]? matches some (.sym '[' _) then
      match closeBracketFrom raws (j0 + 1) with
      | some c => (some (raws.extract (j0 + 1) c), c + 1)
      | none => (some #[], raws.size)
    else (none, j0)
  let j2 := skipSpaces raws j1
  match raws[j2]? with
  | some (.group g _) => (starred, some g, j2 + 1)
  | _ => (starred, none, j1)

/-- Records the document's own `\AtBeginSection` or `\AtBeginSubsection`: whether each section it
opens, and each starred one, stands on a page of its own. -/
private def recordSectionHook (ctx : Ctx) (name : String) (starred : Option (Array Raw))
    (code : Array Raw) (pos : Pos) : EM Unit := do
  let (cmds, envs) := pageDefs ctx
  let sets := hookSetsPageList
    (fun n => ((lookupUser ctx n).bind fun (k, _) => cmds[k]?) == some true)
    (fun n => ((lookupUserEnv ctx n).bind fun (k, _) => envs[k]?) == some true)
  let hook : Ir.SectionHook :=
    { page := sets code.toList, starredPage := sets (starred.getD code).toList }
  if name == "AtBeginSubsection" then
    modify fun st => { st with subsectionHook := some hook }
  else
    modify fun st => { st with sectionHook := some hook }
  if hook.page || hook.starredPage then
    warnOnce ctx ("ctrl:" ++ name) .W0307
      s!"'\\{name}' is not set yet: each section it opens stands on a page showing its title" pos
      (help := "beamer sets the hook's own frame there")

/-- A hook declared in the body: read where no section it opens precedes it, else named and
ignored. -/
private def bodySectionHook (ctx : Ctx) (name : String) (raws : Array Raw) (i : Nat) (pos : Pos) :
    EM Unit := do
  let (starred, code, _) := hookArgsAt raws i
  let sub := name == "AtBeginSubsection"
  let what := if sub then "subsection" else "section"
  let (secs, subs) := (← get).sectionsSeen
  -- premise: sectionPageChecks — one hook decides every section's page
  if (if sub then subs else secs) then
    warnOnce ctx ("ctrl:" ++ name ++ ":body") .W0340
      s!"'\\{name}' after a {what} is ignored: the hook decides every {what}'s page" pos
      (help := s!"declare it before the first '\\{what}', or in the preamble")
  else match code with
    | some c => recordSectionHook ctx name starred c pos
    | none => diag ctx .E0304 s!"'\\{name}' needs a \{...} group" pos

/-- Whether a raw sets a style, size, alignment or colour for its group. -/
private def isDeclaration (ctx : Ctx) : Raw → Bool
  | .ctrl n _ =>
    n == "centering" || (Ir.raggedSideOf? n).isSome
      || (declStyles.lookup n).isSome || (ctx.palette.find? n).isSome
      || (Marker.read? n).any fun (k, _) => k == .fontSize || k == .ink || k == .lang
  | _ => false

/-- False exactly for a palette name followed by a group, its argument. -/
private def argFree (ctx : Ctx) (r : Raw) (rest : List Raw) : Bool :=
  match r with
  | .ctrl n _ =>
    !((ctx.palette.find? n).isSome &&
      (rest.dropWhile (· matches .space)).head? matches some (.group _ _))
  | _ => true

/-- The declaration a named style or a bare palette name makes, if any. -/
private def namedScopeDecl (ctx : Ctx) (n : String) (raws : Array Raw) (i : Nat) :
    Option Ir.Decl :=
  match declStyleOf n with
  | some s => some (.style s)
  | none =>
    (ctx.palette.find? n).bind fun c =>
      match raws[skipSpaces raws (i + 1)]? with
      | some (.group _ _) => none
      | _ => some (.color c (ctx.palette.refOf? n))

/-- The declaration a style or bare palette name makes for the rest of the
scope, when the open paragraph holds only space. -/
private def declBlockOf (ctx : Ctx) (n : String) (raws : Array Raw) (i : Nat)
    (cur : Array Raw) : Option Ir.Decl :=
  -- `\ttfamily`'s literal punctuation lives on the inline context.
  if !cur.all isSpaceOrPar || (Marker.value? .lang n).isSome || n == "ttfamily" then
    none
  else namedScopeDecl ctx n raws i

private def isDeclBlock (ctx : Ctx) (n : String) (raws : Array Raw) (i : Nat)
    (cur : Array Raw) : Bool :=
  (cur.all isSpaceOrPar && (Marker.value? .fontSize n).isSome) ||
    (declBlockOf ctx n raws i cur).isSome

/-- A font size with no `em` or `ex` part, needing no size around it. -/
private def absoluteSize : Dim.Affine Dim.Measure → Bool
  | .lit g => g.width.em == 0 && g.width.ex == 0
  | _ => false

/-- The axis a style sets, where a later style on that axis replaces it;
`\em`, `\normalfont` and a relative `\fontsize` have none. -/
private def styleAxis : Ir.Style → Option Nat
  | .size _ => some 0
  | .fontSize size _ => if absoluteSize size then some 0 else none
  | .mono | .sans | .roman | .family _ => some 1
  | .bold | .medium | .series _ => some 2
  | .italic | .upright => some 3
  | .smallcaps => some 5
  | .lang _ => some 4
  | .emph | .normal => none

private def setsSlant : Ir.Decl → Bool
  | .style .italic | .style .upright | .style .normal => true
  | _ => false

/-- Removes the `\em` turn after the innermost declaration that sets the
slant, if any; the list is innermost first. -/
private def dropEmTurn : List Ir.Decl → Option (List Ir.Decl)
  | [] => none
  | e :: rest =>
    if e == .style .emph then some rest
    else if setsSlant e then none
    else (dropEmTurn rest).map (e :: ·)

/-- Pushes a declaration onto a scope's list, dropping what it overrides. -/
private def pushDecl (decls : List Ir.Decl) (d : Ir.Decl) : List Ir.Decl :=
  if d == .style .emph then
    match dropEmTurn decls.reverse with
    | some rest => rest.reverse
    | none => decls ++ [d]
  else
  let replaced : Ir.Decl → Bool := match d with
    | .style .normal => fun e => match e with
      | .style t => t == .normal || t == .emph || (styleAxis t).any fun a => a != 0 && a != 4
      | .color .. => false
    | .style s => match styleAxis s with
      | some a => fun e => match e with
        | .style t => styleAxis t == some a || (a == 3 && t == .emph)
        | .color .. => false
      | none => fun _ => false
    | .color .. => fun e => e matches .color ..
  decls.filter (!replaced ·) ++ [d]

/-- Opens a declaration's scope and returns the declarations to restore. -/
private def enterBlockDecl (ctx : Ctx) (n : String) (raws : Array Raw) (i : Nat)
    (cur : Array Raw) (pos : Pos) : EM (List Ir.Decl) := do
  let saved := (← get).scope.blockDecls
  if let some spec := Marker.value? .fontSize n then
    if let some style ← readFontSizeStyle ctx spec pos then
      modify fun st => { st with scope := { st.scope with blockDecls := pushDecl saved (.style style) } }
  else
    match declBlockOf ctx n raws i cur with
    | some d =>
      if let .color _ _ := d then noteColorReads n
      modify fun st => { st with scope := { st.scope with blockDecls := pushDecl saved d } }
    | none => pure ()
  return saved

private def leaveBlockDecl (saved : List Ir.Decl) : EM Unit :=
  modify fun st => { st with scope := { st.scope with blockDecls := saved } }

/-- Runs an action under additional declarations, then restores the
caller's declarations, keeping every other effect. -/
public def withBlockDecls (decls : List Ir.Decl) (action : EM α) : EM α :=
  fun st =>
    let (value, done) := action { st with scope := { st.scope with blockDecls := st.scope.blockDecls ++ decls } }
    (value, { done with scope := { done.scope with blockDecls := st.scope.blockDecls } })

public theorem withBlockDecls_exact (decls : List Ir.Decl) (action : EM α) (st : ESt) :
    withBlockDecls decls action st =
      let (value, done) := action { st with scope := { st.scope with blockDecls := st.scope.blockDecls ++ decls } }
      (value, { done with scope := { done.scope with blockDecls := st.scope.blockDecls } }) := by rfl

public theorem withBlockDecls_compose_exact (outer inner : List Ir.Decl) (action : EM α) :
    withBlockDecls outer (withBlockDecls inner action) =
      withBlockDecls (outer ++ inner) action := by
  funext st
  simp only [withBlockDecls, List.append_assoc]
  cases action { st with scope := { st.scope with blockDecls := st.scope.blockDecls ++ (outer ++ inner) } }
  rfl

private def declAlignOf (n : String) : Option Ir.HAlign :=
  if n == "centering" then some .center
  else (Ir.raggedSideOf? n).map Ir.FlushSide.halign

private def wrapDeclAlign (align : Option Ir.HAlign) (inner : Array Block) :
    Array Block :=
  if inner.isEmpty then #[]
  else match align with
    | some .center => #[.center inner]
    | some .left => #[.ragged .left inner]
    | some .right => #[.ragged .right inner]
    | none => inner

private def declScopeWrap (n : String) (inner : Array Block) : Array Block :=
  wrapDeclAlign (declAlignOf n) inner

/-- The declarations between a list's opening and its first item, in
force for every item. -/
private structure ListScope where
  decls : List Ir.Decl := []
  align : Option Ir.HAlign := none

private def listScopeCtrl (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (name : String) (pos : Pos) (scope : ListScope) : EM (Option ListScope) := do
  if let some align := declAlignOf name then
    return some { scope with align := some align }
  if let some spec := Marker.value? .fontSize name then
    let style ← readFontSizeStyle ctx spec pos
    return some { scope with decls := scope.decls ++ style.toList.map Ir.Decl.style }
  if let some source := Marker.value? .ink name then
    match ← readColor ctx ctx.palette none source pos with
    | .resolved c token =>
      return some { scope with decls := scope.decls ++ [.color c token] }
    | .missing => warnPaletteMiss ctx source pos
    | .rejected => pure ()
    return some scope
  let decl := namedScopeDecl ctx name raws i
  if let some (.color _ _) := decl then noteColorReads name
  return decl.map fun d => { scope with decls := scope.decls ++ [d] }

/-- Puts a `\color`'s palette in force, dropping the scope's earlier colour
declarations: the last ink declared wins. -/
private def setInk (pal : Palette) (st : ESt) : ESt :=
  { st with
    scope := { st.scope with
      palette := { st.scope.palette with current := some pal }
      blockDecls := st.scope.blockDecls.filter (!· matches .color ..) }
    flowGen := st.flowGen + 1 }

/-- Declares a block-level `\color`'s ink for the rest of the flow; `none`
when the colour does not resolve. -/
private def inkFlowDecl (ctx : Ctx) (source : String) (pos : Pos) :
    EM (Option Ir.Palette) := do
  if source == Compat.normalInkSource then
    -- `\normalcolor`: the opening ink back.
    let pal := ctx.palette.restore ctx.basePalette (.role .ink)
    modify (setInk pal)
    return some pal
  match ← readColor ctx ctx.palette none source pos with
  | .resolved c _ =>
    let pal := ctx.palette.declare (.role .ink) c
    modify (setInk pal)
    return some pal
  | .missing =>
    warnPaletteMiss ctx source pos
    return none
  | .rejected => return none

private def warnPageColorMiss (ctx : Ctx) (source : String) (pos : Pos) : EM Unit :=
  warnOnce ctx ("pagecolor:" ++ source) .W0304
    s!"'{source}' is not in the palette; the page ground is unchanged" pos
    (help := "declare the colour before using it as a page ground")

/-- `\pagecolor`'s page ground, set globally as xcolor sets it, whatever
group it stands in. -/
private def pageGroundDecl (ctx : Ctx) (source : String) (pos : Pos) :
    EM (Option Ir.Palette) := do
  match ← readColor ctx ctx.palette none source pos with
  | .resolved c _ =>
    logGlobal (.entry (.role .page) (some c) false false)
    noteDocRoles [.page]
    let docRoles := (← get).spans.docRoles
    return some ((ctx.palette.declare (.role .page) c).reseed docRoles.contains)
  | .missing =>
    warnPageColorMiss ctx source pos
    return none
  | .rejected => return none

/-- `\nopagecolor`: the opening page ground back, set globally. -/
private def pageGroundReset (ctx : Ctx) : EM Ir.Palette := do
  logGlobal (.entry (.role .page) (Ir.Design.declared? ctx.basePalette .page)
    (ctx.basePalette.decorative.contains (.role .page)) false)
  return ctx.palette.restore ctx.basePalette (.role .page)

/-- Whether a control is `\pagecolor`'s or `\nopagecolor`'s marker. -/
private def isPageGround (n : String) : Bool :=
  (Marker.read? n).any fun (k, _) => k == .pageColor || k == .pageColorReset

/-- The page ground a page-ground marker sets, globally. -/
private def pageGround (ctx : Ctx) (n : String) (pos : Pos) : EM (Option Ir.Palette) :=
  match Marker.value? .pageColor n with
  | some source => pageGroundDecl ctx source pos
  | none => some <$> pageGroundReset ctx

public def isParRaw : Raw → Bool
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

/-- The pars strictly inside an element, not counting a top-level `\par`. -/
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

/-- Whether a raw makes its brace group a block scope: an alignment, page
ground or beamer colour declaration. -/
private def isCenteringRaw : Raw → Bool
  | .ctrl n _ => n == "centering" || (Ir.raggedSideOf? n).isSome
      || isPageGround n || n == BeamerColor.marker || n == BeamerColor.starMarker
  | _ => false

/-- Whether a group after `cur` is an argument: a control word or an option
precedes it, past spaces and earlier argument groups. -/
private def isArgument (cur : Array Raw) : Bool := Parse.endsInArgument cur

/-- Collects the declarations a split group re-applies after each paragraph
break, `\urlstyle` and its face included. -/
private def carryDecl (ctx : Ctx) (r : Raw) (rest : List Raw) (decls : Array Raw) :
    Array Raw :=
  if isDeclaration ctx r && argFree ctx r rest then decls.push r
  else match r, (rest.dropWhile (· matches .space)).head? with
    | .ctrl "urlstyle" _, some (.group b gp) =>
      if rawParsList b.toList == 0 then (decls.push r).push (.group b gp) else decls
    | _, _ => decls

/-- Splits a scope group at each `\par`, re-applying its declarations to
every later part and dropping parts that set nothing. -/
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
      splitAtParsGo ctx pos rest out (carryDecl ctx r rest decls) (pre.push r)

private def splitAtPars (ctx : Ctx) (body : Array Raw) (pos : Pos) : Array Raw :=
  splitAtParsGo ctx pos body.toList #[] #[] #[]

/-- Whether a group opens with a size declaration and ends with `\par`, so
its paragraph leads at that size's `\baselineskip`. -/
private def sizeParScope (body : Array Raw) : Bool :=
  let ws := body.toList.filter fun r => !(r matches .space)
  match ws.head?, ws.getLast? with
  | some (.ctrl n _), some last =>
    ((declStyleOf n matches some (.size _)) || (Marker.value? .fontSize n).isSome) &&
      isParRaw last
  | _, _ => false

private theorem nestedParsList_push (a : Array Raw) (r : Raw) :
    nestedParsList (a.push r).toList = nestedParsList a.toList + nestedPars r := by
  simp [Array.toList_push, nestedParsList_append, nestedParsList]

private theorem rawParsList_push (a : Array Raw) (r : Raw) :
    rawParsList (a.push r).toList = rawParsList a.toList + rawPars r := by
  simp [Array.toList_push, rawParsList_append, rawParsList]

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
          simp only [nestedPars]; omega
        · rw [nestedParsList_push]; omega
      have h4 : nestedPars r = 0 := by
        cases r <;> simp_all [isParRaw, nestedPars]
      simp only [nestedParsList]
      omega
    · rename_i hpar
      have hd' : rawParsList (carryDecl ctx r rest decls).toList = 0 := by
        unfold carryDecl
        split
        · rename_i hdecl
          rw [rawParsList_push,
            rawPars_decl (by simpa using hpar) ((Bool.and_eq_true _ _).mp hdecl).1]
          omega
        · split
          · rename_i b gp _ _
            split
            · rename_i hb
              rw [rawParsList_push, rawParsList_push]
              simp only [rawPars, beq_iff_eq] at hb ⊢
              simp [hb, hd]
            · exact hd
          · exact hd
      have h1 := ih out (carryDecl ctx r rest decls) (pre.push r) hd'
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

private theorem extract_pars_le (body : Array Raw) (a b : Nat) :
    rawParsList (body.extract a b).toList ≤ rawParsList body.toList := by
  simp only [rawParsList_eq]; exact measList_extract_le ..

private theorem extract_nested_le (body : Array Raw) (a b : Nat) :
    nestedParsList (body.extract a b).toList ≤ nestedParsList body.toList := by
  simp only [nestedParsList_eq]; exact measList_extract_le ..

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

private theorem elem_pars_le {raws : Array Raw} {j : Nat} {r : Raw}
    (h : raws[j]? = some r) {i : Nat} (hij : i ≤ j) :
    nestedPars r ≤ slicePars raws i := by
  simp only [slicePars_eq]; exact sliceMeas_elem_le h hij

private theorem extract_slice_pars_le (raws : Array Raw) (a b : Nat) :
    nestedParsList (raws.extract a b).toList ≤ slicePars raws a := by
  rw [nestedParsList_eq, slicePars_eq]; exact sliceMeas_extract_le ..

private theorem slicePars_splice {raws : Array Raw} {i : Nat}
    (h : i < raws.size) {body : Array Raw} {gpos : Pos}
    (hr : raws[i] = .group body gpos) (hp : body.any isParRaw = true)
    (ctx : Ctx) (pos : Pos) :
    slicePars (raws.extract 0 i
        ++ splitAtPars ctx body pos ++ raws.extract (i + 1) raws.size) i
      < slicePars raws i := by
  simp only [slicePars_eq]
  have hs := sliceMeas_splice (μ := nestedPars) h (splitAtPars ctx body pos)
  have hl := splitAtPars_pars_lt ctx body pos hp
  rw [hr] at hs
  simp only [nestedPars, ← nestedParsList_eq] at hs
  omega

private def visParsGo (user : Array UserCmd) : Nat → Nat :=
  visGo (fun cmd => rawParsList cmd.body.toList) user

private theorem visPars_expand {ctx : Ctx} {name : String} {k : Nat}
    {cmd : UserCmd} (h : lookupUser ctx name = some (k, cmd)) :
    rawParsList cmd.body.toList + visParsGo ctx.user k
      ≤ visParsGo ctx.user ctx.limit := by
  unfold visParsGo
  exact visGo_expand (f := fun cmd => rawParsList cmd.body.toList) h

mutual
/-- Trims a paragraph edge through roles and source locations, which open no
TeX group, but not into styled bodies; the boolean says the edge stays
unclosed. -/
-- conserves: none — trims discarded paragraph-edge space and final breaks.
private def trimParaOne (leading : Bool) : Inline → Array Inline × Bool
  | .text s =>
    let t := if leading then String.ofList (s.toList.dropWhile (· == ' '))
      else if s.trimAscii.isEmpty then ""
      else String.ofList ((s.toList.reverse.dropWhile (· == ' ')).reverse)
    (if t.isEmpty then #[] else #[.text t], t.isEmpty)
  | .role name inner =>
    let (inner, more) := trimParaList leading #[] inner.toList
    (if inner.isEmpty then #[] else #[.role name inner], more)
  | .located source inner =>
    let (inner, more) := trimParaList leading #[] inner.toList
    (if inner.isEmpty then #[] else #[.located source inner], more)
  | .label name => (#[.label name], leading)
  | .linebreak g => if leading then (#[.linebreak g], false) else (#[], true)
  | x@(.math ..) | x@(.formula ..) | x@(.styled ..)
  | x@(.colored ..) | x@(.link ..) | x@(.ref ..) | x@(.decorated ..)
  | x@(.fill) | x@(.hspace ..) | x@(.rule ..) | x@(.pageNumber)
  | x@(.pageCount) | x@(.strut ..) | x@(.italicCorr ..)
  | x@(.onSteps ..) | x@(.altSteps ..) | x@(.image ..)
  | x@(.icon ..) | x@(.cite ..) | x@(.cited ..) | x@(.footnote ..) => (#[x], false)

private def trimParaList (leading : Bool) (acc : Array Inline) :
    List Inline → Array Inline × Bool
  | [] => (acc, true)
  | x :: xs =>
    if leading then
      let (head, more) := trimParaOne leading x
      if more then trimParaList leading (acc ++ head) xs
      else (acc ++ head ++ xs.toArray, false)
    else
      let (tail, more) := trimParaList leading #[] xs
      if more then
        let (head, more) := trimParaOne leading x
        (acc ++ head ++ tail, more)
      else (acc.push x ++ tail, false)
end

private def finishPara (inlines : Array Inline) : EM (Option Block) := do
  let inlines := (trimParaList true #[] inlines.toList).1
  let inlines := (trimParaList false #[] inlines.toList).1
  if inlines.isEmpty then return none
  -- LaTeX reads `\baselineskip` at `\par`: the end's declarations set it.
  return some (paraUnder (← get).scope.lang (Ir.paraAt (← get).scope.blockDecls inlines))

private def mkPara (ctx : Ctx) (cur : Array Raw) : EM (Option Block) := do
  let mut cur := cur
  repeat
    match cur.back? with
    | some .space => cur := cur.pop
    | some (.par _) => cur := cur.pop
    | _ => break
  if cur.isEmpty then
    return none
  finishPara (← elabInlines ctx cur)

private def storeTitlePart (name : String) (content : Array Inline)
    (short : Option (Array Inline)) : EM Unit :=
  modify fun (st : ESt) =>
    let st := match TitleDatum.ofName? name with
      | some datum =>
        let rest := st.shortTitles.filter (fun (entry : TitleDatum × Array Inline) => entry.1 != datum)
        { st with shortTitles := short.elim rest (fun value => (datum, value) :: rest) }
      | none => st
    match name with
    | "title" => { st with title := some content }
    | "subtitle" => { st with subtitle := some content }
    | "author" => { st with author := some content }
    | "institute" => { st with institute := some content }
    | _ => { st with date := some content }

/-- Stores one `\title`-family declaration, returning the index past its
arguments and the run of an unclosed optional argument. -/
private def takeTitleDecl (ctx : Ctx) (name : String) (raws : Array Raw)
    (start : Nat) (pos : Pos) : EM ({ j : Nat // start ≤ j } × Array Raw) := do
  let (⟨j, hj⟩, recovered, junk) ← skipOptArg ctx name raws start pos
  match raws[j]? with
  | some (.group body _) =>
    let short ← (bracketArgRaws? raws start pos).mapM (elabInlines ctx)
    storeTitlePart name (← elabInlines ctx body) short
    return (⟨j + 1, by omega⟩, junk)
  | _ =>
    if recovered then
      warnSkippedDecl ctx name pos
      return (⟨j, hj⟩, junk)
    diag ctx .E0304 s!"'\\{name}' needs a \{...} group" pos
    return (⟨start, Nat.le_refl start⟩, #[])

/-- The blocks `\maketitle` sets from the declared parts under the
`titlepage` style; a declared but empty part sets nothing. -/
private def titleBlocks (ctx : Ctx) (st : ESt) : Array Block := Id.run do
  let tps : ElementStyle := (ctx.styles.find? "titlepage").getD {}
  let part (v : Option (Array Inline)) : Option (Array Inline) :=
    v.bind fun xs => if xs.isEmpty then none else some xs
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
    -- The title is the outline's one level-0 heading, never numbered.
    inner := push inner none (.section 0 true none xs)
  if let some xs := part st.subtitle then
    inner := push inner (ctx.tokens.findSourced? "subtitlegap") (.para #[.styled (.size "large") xs])
  if let some (c, nm) := tps.separator then
    unless inner.isEmpty && (part st.author).isNone && (part st.institute).isNone
        && (part st.date).isNone do
      let c := (nm.bind ctx.palette.lookup).getD c
      -- beamerinnerthememoloch.dtx: titleseparator linewidth=0.5pt
      let th := (ctx.tokens.findSourced? "separatorheight").getD
        (Ir.Sourced.bare { width := Dim.Length.ofSp (Dim.pt 1 / 2) })
      inner := push inner (ctx.tokens.findSourced? "separatorgap") (.rule c nm th)
      pending := ctx.tokens.findSourced? "separatorgap"
  if let some xs := part st.author then
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
  match inner with
  | #[.rule _ _ _] => return #[]
  | _ =>
    let ink := match Ir.Design.declared? ctx.palette .ink with
      | some c => (c, some (ColorRef.role .ink))
      | none => (Ir.Color.black, none)
    let blocks := Ir.titleBars tps ink inner
    return match tps.after with
      | some g => blocks.push (.spaced (Ir.Sourced.bare g) #[])
      | none => blocks

/-- Remembers a document-declared key, so a later `\theme` replacing it is
named. -/
private def noteDeclared (ctx : Ctx) (decl key : String) : EM Unit :=
  modify fun st => applyEvent ctx st (.declared decl key)

/-- Records a setting the document itself declares at `pos`. -/
private def noteSetting (ctx : Ctx) (setting : UnusedSetting.Setting) (pos : Pos) : EM Unit :=
  modify fun st => applyEvent ctx st (.setting setting pos)

/-- The `\leftmargin⟨n⟩` the class fixes as it loads, which a length may name. -/
private def classMarginTokens (l : Ir.ListLineage) : Array (String × Dim.SymGlue) :=
  (List.range 6).toArray.map fun k => (Ir.leftMarginName (k + 1), Ir.leftMarginFor l {} (k + 1))

private def engineLengthTokensOfPage (page : PageSpec) :
    Array (String × Dim.SymGlue) :=
  #[("paperwidth", { width := Dim.Length.ofSp page.width }),
    ("paperheight", { width := Dim.Length.ofSp page.height }),
    ("textwidth", { width := Dim.Length.ofSp page.textWidth }),
    ("textheight", { width := Dim.Length.ofSp page.textHeight }),
    ("columnsep", { width := Ir.columnSep }),
    ("baselineskip", { width := Dim.Length.ofSp (Ir.baselineSkipOf page) }),
    ("parskip", Ir.texParskipOf page)]

/-- A class's abstract form under its options: `titlepage` moves a quotation onto a title page,
`notitlepage` winning as the classes declare it last. -/
private def abstractFormUnder (form : Ir.AbstractForm) (opts : List String) : Ir.AbstractForm :=
  if form == .inset then form
  else if opts.contains "notitlepage" then .quotation
  else if opts.contains "titlepage" then .titlePage
  else form

/-- The engine length tokens the preamble may read: those whose value the
declared page or the class already fixes. -/
private def engineLengthTokens (docClass : Ir.DocClass) (classOptions : String)
    (page : PageSpec) : Array (String × Dim.SymGlue) :=
  let record := docClass.record
  let dflt : PageSpec := {}
  let opts := (KeyVal.items classOptions).toList
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
    | "columnsep" => true
    -- The body size and `\parskip` may still change in the preamble.
    | "baselineskip" | "parskip" => false
    | _ => false
  (engineLengthTokensOfPage (classPageDefaults record opts page)).filter
    (fun kv => offered kv.1) ++ classMarginTokens record.lists

/-- Applies a `\tokens{...}` block entry by entry, so an entry may refer to
an earlier one. -/
private def applyTokens (ctx : Ctx) (toks : Tokens) (src : String) (pos : Pos)
    (engine : Array (String × Dim.SymGlue) := #[]) : EM Tokens := do
  let mut acc : Tokens := toks
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | none =>
      diag ctx .E0320 s!"invalid entry in '\\tokens': {entry.quote}" pos
        (help := "entries look like: name = length")
    | some (key, valueSrc) =>
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
        let detail := if Decl.looksLikeExpr valueSrc then
            match Decl.parseLengthExpr (acc.entries ++ engine) valueSrc with
            | .error e => s!": {e}"
            | .ok _ => ""
          else ""
        diag ctx .E0321 s!"cannot read length for '{key}': {valueSrc.quote}{detail}" pos
          (help := "lengths look like 10pt, 1.5ex, 2em, a + 2b, or 0.6 * other-token")
  return acc


/-- Reads a `\palette` option run as (decorative, seeds, skipBlock); an
unknown option skips the block. -/
private def parsePaletteOpts (ctx : Ctx) (src : String) (pos : Pos) :
    EM (Bool × Bool × Bool) := do
  let mut decorative := false
  let mut seeds := false
  let mut skipBlock := false
  for e in Decl.splitEntries src do
    if e == "decorative" then
      decorative := true
    else if e == "seeds" then
      seeds := true
    else
      diag ctx .W0316 s!"unknown option in '\\palette': {e.quote}; block skipped" pos
        (help := "options: decorative, seeds")
      skipBlock := true
  -- premise: seedRoleChecks — decorative and plain seeded builds agree
  if seeds && decorative then
    warnOnce ctx "palette:seeds:decorative" .W0110 "'decorative' exempts nothing in \
'\\palette[seeds]': a generated palette meets the contrast its sites owe; the option is \
ignored" pos
      (help := "drop 'decorative', or declare a deliberately quiet colour in a \
'\\palette[decorative]{...}' block of its own")
    decorative := false
  return (decorative, seeds, skipBlock)

/-- Resolves named Beamer colours into the palette in force; unresolved
expressions are reported only under `settle`. -/
private def resolveBeamerColors (ctx : Ctx) (pal : Palette)
    (settle : Bool := false) : EM Palette := do
  let (colors, pal, issues) := (← get).scope.palette.resolve pal
  modify fun st => { st with scope := { st.scope with palette := colors } }
  if ← readsOwed then noteColorNames colors.sourceNames
  for (key, c, span) in colors.origins do
    recordColorDeclaration key c span
  if settle then
    for issue in issues do
      let origin := { ctx with file := issue.span.file, callSite := none }
      warnOnce origin ("beamercolor:" ++ issue.message) .W0104
        ("'\\setbeamercolor': " ++ issue.message ++ "; the unresolved value is ignored") issue.span.pos
        (trigger := "\\setbeamercolor")
  let docRoles := (← get).spans.docRoles
  return (pal.reseed docRoles.contains).yieldGrounds docRoles.contains

private def applyBeamerColor (ctx : Ctx) (pal : Palette) (name : String)
    (star : Bool) (src : String) (pos : Pos) : EM Palette := do
  let name := name.trimAscii.toString
  let (colors, unsupported) := (← get).scope.palette.declare name star src (ctx.sourceSpan pos)
  modify fun st => { st with scope := { st.scope with palette := colors } }
  for key in unsupported do
    warnOnce ctx ("beamercolor:key:" ++ name ++ ":" ++ key) .W0104
      s!"'\\setbeamercolor' key '{key}' on '{name}' is unsupported; the key is dropped" pos
      (trigger := "\\setbeamercolor")
  if let some (fg, bg) := BeamerColor.roles.lookup name then
    for entry in KeyVal.items src do
      if let some (key, _) := KeyVal.pair? entry then
        if key == "fg" then noteDocRoles fg.toList
        if key == "bg" then noteDocRoles bg.toList
        if (key == "fg" && fg.isNone) || (key == "bg" && bg.isNone) then
          warnOnce ctx ("beamercolor:channel:" ++ name ++ ":" ++ key) .W0104
            s!"'\\setbeamercolor' {key} on '{name}' has no paint site; that channel is kept only for inheritance" pos
            (trigger := "\\setbeamercolor")
  resolveBeamerColors ctx pal

/-- The `\setbeamercolor{element}{declaration}` arm. -/
private def beamerColorArm (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (star : Bool) (pos : Pos) : EM { t : Option Palette × Nat // i ≤ t.2 } := do
  let j := skipSpaces raws i
  have hj : i ≤ j := skipSpaces_ge raws i
  let j2 := skipSpaces raws (j + 1)
  have hj2 : j + 1 ≤ j2 := skipSpaces_ge raws (j + 1)
  match raws[j]?, raws[j2]? with
  | some (.group elem _), some (.group body _) =>
    let pal ← applyBeamerColor ctx ctx.palette (rawSrc elem) star (rawSrc body) pos
    let pal ← resolveBeamerColors ctx pal true
    modify fun st => { st with scope := { st.scope with palette := { st.scope.palette with current := some pal } },
                               flowGen := st.flowGen + 1 }
    return ⟨(some pal, j2 + 1), by omega⟩
  | _, _ =>
    diag ctx .E0304 "'\\setbeamercolor' needs an element and a colour declaration" pos
    return ⟨(none, i), Nat.le_refl _⟩

/-- Names each declared element that no supported paint site reaches. -/
private def finishBeamerColors (ctx : Ctx) : EM Unit := do
  let colors := (← get).scope.palette
  for e in colors.elements do
    -- premise: beamerReachChecks — named exactly when it changes no paint
    if e.declared && !(colors.reached.contains e.name) then
      let origin := { ctx with file := e.span.file, callSite := none }
      warnOnce origin ("beamercolor:element:" ++ e.name) .W0104
        s!"'\\setbeamercolor' element '{e.name}' has no supported paint site or inheriting element; its colours are unused" e.span.pos
        (help := Compat.beamerNative.lookup "setbeamercolor") (trigger := "\\setbeamercolor")

/-- The palette the seeds generate at their targets, memoised per document. -/
private def generated (seeds : SeedPalette.Seeds) (targets : SeedPalette.Targets) :
    EM (Except SeedPalette.Failure SeedPalette.Colors) := do
  let memo := (← get).spans.seedPalettes
  match memo.find? fun (s, t, _, _) => s == seeds && t == targets with
  | some (_, _, some colors, _) => return .ok colors
  | some (_, _, none, some f) => return .error f
  | _ =>
    let result := (SeedPalette.generate seeds targets).map (·.colors)
    let entry := match result with
      | .ok colors => (seeds, targets, some colors, none)
      | .error f => (seeds, targets, none, some f)
    modify fun st => { st with spans := { st.spans with seedPalettes := memo.push entry } }
    return result

private def seedHelp (f : SeedPalette.Failure) : String :=
  if f.cmyk then "declare the seed in sRGB: #RRGGBB or oklch(L C H)"
  else if [Role.surface, .surfaceStrong, .rule, .accentWash, .accentSoft].contains f.role then
    "move the paper further from the ink, so its tints have room to stand apart: \
\\palette[seeds]{ ink = #1E1B2E, paper = #FFFFFF, accent = #E85D2A }"
  else
    "move the ink and the paper further apart, so every tone derived between them reads: \
\\palette[seeds]{ ink = #1E1B2E, paper = #FFFFFF, accent = #E85D2A }"

/-- The report of seeds that generate no palette, read where `source` asked for it, the palette
standing as `stands` says. -/
private def seedFailure (ctx : Ctx) (pos : Pos) (f : SeedPalette.Failure) (source stands : String) :
    EM Unit := do
  let what := match f.role with
    | .ink => "ink"
    | .page => "paper"
    | .accent => "accent"
    | r => (ColorRef.role r).key
  modify fun st => { st with diags := st.diags.push (diagOf ctx .W0306
    s!"{source} generates no palette: its {what} fails its check; {stands}"
    (some pos) (help := some (seedHelp f))
    (subject := some s!"palette:seeds:{what}") (detail := some f.detail)) }

/-- Each role a generated palette changes from `before`, its colour's source `pos`, a declaration
of the document's where `declared`, and logged. -/
private def noteSeeded (ctx : Ctx) (pos : Pos) (before after : Palette) (declared : Bool := true) :
    EM Unit := do
  for r in Role.all do
    if let some c := Design.declared? after r then
      if Design.declared? before r != some c then
        if declared then noteDeclared ctx "palette" (ColorRef.role r).key
        recordColorDeclaration (ColorRef.role r).key c (ctx.sourceSpan pos)
        modify fun st => { st with scope := { st.scope with
          palette := st.scope.palette.native r c } }
        logGlobal (.entry (.role r) (some c) false true)

/-- A generated palette installed over `pal`, the roles `keep` names left as declared. -/
private def installSeeded (ctx : Ctx) (pos : Pos) (pal : Palette) (keep : Role → Bool)
    (st : SeedPalette.SeedState) : EM Palette := do
  let out := pal.applySeedsUnder st keep
  noteSeeded ctx pos pal out
  logGlobal (.seeded (some st))
  return out

/-- A generated palette, a bundle's or the document's seeds', generated again at a cover share the
preamble declares after it, each role still at its generated colour moving with it. -/
private def reseedCovered (ctx : Ctx) (pos : Pos) (pal : Palette) (depth : GroundDepth) (n : Nat) :
    EM Palette := do
  let some st := pal.seeded | return pal
  let targets := { st.targets with cover := (st.seeds.targetsAt depth (some n)).cover }
  if targets.cover == st.targets.cover then return pal
  match ← generated st.seeds targets with
  | .error f =>
    seedFailure ctx pos f "the seeds at the covered share" "the palette generated before stands"
    return pal
  | .ok colors =>
    let st' := { st with targets, colors }
    let out := pal.replaceGenerated (← get).spans.docRoles.contains st st'
    noteSeeded ctx pos pal out (declared := false)
    logGlobal (.seeded (some st'))
    return out

/-- The report of a cover the body declares, which the deck's covering, set once before the body,
does not take. -/
private def coverInBody (ctx : Ctx) (pos : Pos) : EM Unit :=
  let share := (Design.ofPalette ctx.basePalette).coveredFraction
  let how := if share == 0 then "hiding its pending steps"
    else s!"covering its pending steps at {share}%"
  warnOnce ctx "palette:covered:body" .W0340
    ("a cover declared in the body is ignored; the deck keeps the covering its body opens " ++
      s!"with, {how}") pos
    (help := "a deck's covering is set once, before '\\begin{document}'")

private def applyPaletteEntry (ctx : Ctx) (pal : Palette) (key valueSrc entry : String)
    (pos : Pos) (decorative : Bool := false) (aliasOnly : Bool := false) (inBody : Bool := false)
    (depth : GroundDepth := .documents) : EM Palette := do
  let mut pal := pal
  if !key.toList.all Decl.isIdentChar then
    diag ctx .E0320 s!"invalid key in '\\palette': {entry.quote}" pos
      (help := "entries look like: name = #RRGGBB")
  else if builtinNames.contains key || (escapeOf key).isSome then
    diag ctx .E0303 s!"palette name '{key}' collides with a built-in command" pos
  else if !aliasOnly && key == "covered" &&
      (valueSrc.endsWith "\\%" || valueSrc.endsWith "%") then
    -- beamer's \setbeamercovered{transparent=n}; a bare % opens a comment.
    let digits := if valueSrc.endsWith "\\%" then (valueSrc.dropEnd 2).toString
      else (valueSrc.dropEnd 1).toString
    match (digits.trimAscii.toString).toNat? with
    | some n =>
      if n ≤ 99 then
        pal := { pal with decorative := if decorative && !pal.decorative.contains (.role .covered)
                            then pal.decorative.push (.role .covered) else pal.decorative }
        -- The renderers cover at the share in force when the body opens.
        if inBody then
          if n != (Design.ofPalette ctx.basePalette).coveredFraction then
            coverInBody ctx pos
        else
          pal := { pal with coveredFraction := some n }
          logGlobal (.covered (some n))
          noteDeclared ctx "palette" "covered"
          pal ← reseedCovered ctx pos pal depth n
      else
        diag ctx .E0332 s!"covered fraction must be 0–99 percent, got '{valueSrc}'" pos
          (help := "the fraction of each covered colour kept over the page; 0\\%, the default, hides it")
    | none =>
      diag ctx .E0321 s!"cannot read covered fraction: {valueSrc.quote}" pos
        (help := "a percentage like: covered = 38\\%")
  else if inBody && !aliasOnly && key == "covered" then
    coverInBody ctx pos
  else
    let xcolor := valueSrc.trimAscii.toString.startsWith Decl.xcolorDefinitionPrefix
    let ref : ColorRef := if aliasOnly || xcolor then .color key else ColorRef.ofKey key
    let refs : List ColorRef := if xcolor && !aliasOnly then Palette.xcolorRefs key else [ref]
    let put (pal : Palette) (c : Color) : EM Palette := do
      -- premise: codeRoleChecks — a retired key changes no listing paint
      if let some r := CodeColor.retiredKeys.lookup key then
        warnOnce ctx ("listingkey:" ++ key) .W0387
          s!"palette key '{key}' still names a colour, but listings now colour each token \
by its code role" pos
          (help := if xcolor then
              s!"declare \\definecolor\{{Ir.codeKey r}}\{HTML}\{RRGGBB} to colour the {r.word} role"
            else s!"declare \\palette\{ {Ir.codeKey r} = #RRGGBB } to colour the {r.word} role")
      noteDeclared ctx "palette" key
      recordColorDeclaration key c (ctx.sourceSpan pos)
      if ref == .color key && !aliasOnly && !xcolor && legacyScreenKeys.contains key then
        modify fun st => if st.spans.tokenKeys.any (·.1 == key) then st else
          { st with spans := { st.spans with
            tokenKeys := st.spans.tokenKeys.push (key, ctx.sourceSpan pos) } }
      else if ref == .color key && !aliasOnly && ColorRef.ofKey key == .color key &&
          (CodeColor.retiredKeys.lookup key).isNone then
        noteSetting ctx (.color key) pos
        -- A picture's settings, macros and preamble are read again for the colour now owed.
        modify fun st => { st with spans := { st.spans with pictureContextRead := (0, 0),
                                                            picturePreambleRead := false } }
      unless aliasOnly do
        for k in refs do
          if let .role r := k then
            modify fun st => { st with scope := { st.scope with
              palette := st.scope.palette.native r c } }
            noteDocRoles [r]
          logGlobal (.entry k (some c) decorative true)
      return if xcolor && !aliasOnly then pal.defineXcolor key c decorative
        else pal.declare ref c decorative
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

/-- Names each declared `ink` or `surface` palette key nothing in the
document paints with. -/
private def unreadPaletteKeys (reads : Array String) (keys : Array (String × Span)) :
    Array Diag :=
  -- premise: Tests.ColorNames.unreadKeyFlipChecks — named exactly when inert
  keys.filterMap fun (key, span) =>
    if reads.contains key then none
    else
      let (what, role) := if key == "ink" then ("text", "fg") else ("ground", "bg")
      some (Diag.of .W0387
        s!"'\\palette' entry '{key}' declares a colour nothing in the document paints with; \
the page's {what} colour is the '{role}' key" (span := some span)
        (subject := some s!"palette:{key}")
        (help := some s!"declare \\palette\{ {role} = ... } for the page's {what}, or name \
'{key}' where it is used"))

/-- Whether a frame-title font asks only for what the plain title already sets: its size step
and the bold series. -/
public def restatesPlainTitle (src : String) : Bool :=
  let kept := String.ofList (src.toList.filter fun c => !c.isWhitespace && c != '{' && c != '}')
  let cmds := (kept.splitOn "\\").filter (!·.isEmpty)
  !cmds.isEmpty && cmds.all fun c => c == Ir.plainFrameTitleStep || c == "bfseries"

/-- Names a frame-title font the document declares where no frame carries a frame-title bar, the
one place its font is read. -/
private def unreadFrameTitleFont (doc : Doc) (site restated : Option Span) : Array Diag :=
  let barred (p : Palette) : Bool := (Design.ofPalette p).frametitle.isSome
  let anyBar := barred doc.palette || Ir.foldBlocks (fun a b => a || match b with
    | .setPalette p => barred p
    | _ => false) (fun a _ => a) false doc.body
  -- premise: frameTitleKeyChecks — a frame title without a bar reads no declared font
  if doc.docClass.record.model != .frame || anyBar then #[]
  else match site, restated with
  | some span, _ =>
    #[Diag.of .W0104 "the frame title's declared font is read only under a frame-title bar, \
which no frame here has; the titles keep the bold title" (span := some span)
        (subject := some "param:\\style:frametitle:font")
        (help := some "declare a frame-title bar, as \\setbeamercolor{frametitle}{bg=...} does, \
or a theme with one, such as moloch")]
  | none, some span =>
    #[Diag.of .N0100 "'\\style{frametitle}{ font }' → nothing: the frame title is set at that \
size and in bold already" (span := some span) (subject := some "param:\\style:frametitle:font")]
  | none, none => #[]

private def seedKeys : List String := ["ink", "paper", "accent", "alert", "example", "neutral"]

/-- Installs the palette generated from `\palette[seeds]{…}`; seeds that
generate none stand as the page's text, ground and accent. -/
private def applySeeds (ctx : Ctx) (pal : Palette) (src : String) (pos : Pos)
    (depth : GroundDepth) (inBody : Bool := false) : EM Palette := do
  let mut found : Array (String × Color) := #[]
  let mut blocks := SeedPalette.Blocks.tonal
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | none =>
      diag ctx .E0320 s!"invalid entry in '\\palette[seeds]': {entry.quote}" pos
        (help := "entries look like: ink = #RRGGBB")
    | some (key, valueSrc) =>
      if key == "blocks" then
        match SeedPalette.Blocks.ofName? valueSrc.trimAscii.toString with
        | some b => blocks := b
        | none =>
          diag ctx .E0321 s!"cannot read block style {valueSrc.quote}: the styles are tonal and strong" pos
            (help := "blocks = tonal, or blocks = strong")
      else if seedKeys.contains key then
        match ← readColor ctx pal none valueSrc pos with
        | .resolved c _ => found := Ir.redeclare found key c
        | .rejected => pure ()
        | .missing =>
          diag ctx .E0321 s!"cannot read seed colour for '{key}': {valueSrc.quote}" pos
            (help := "seeds are #RRGGBB, oklch(L C H), a colour name or a mix like accent!50!black")
      else
        diag ctx .E0320 s!"unknown seed '{key}' in '\\palette[seeds]'" pos
          (help := "seeds: ink, paper, accent, alert, example, neutral, and blocks = tonal|strong")
  let seed (k : String) := (found.find? (·.1 == k)).map (·.2)
  let some ink := seed "ink" | missingSeed
  let some paper := seed "paper" | missingSeed
  let some accent := seed "accent" | missingSeed
  let seeds : SeedPalette.Seeds :=
    { ink, paper, accent, alert := seed "alert", exampleColor := seed "example",
      neutral := seed "neutral" }
  -- The renderers cover at the share in force when the body opens.
  let share := if inBody then ctx.basePalette.coveredFraction else pal.coveredFraction
  let targets := seeds.targetsAt depth share
  -- The document's own role colours outrank the generated ones.
  let docRoles := (← get).spans.docRoles
  let keep (r : Role) : Bool := docRoles.contains r
  noteDocRoles [.ink, .page, .accent]
  match ← generated seeds targets with
  | .ok colors => resolveBeamerColors ctx (← installSeeded ctx pos pal keep { seeds, targets, blocks, colors })
  | .error f =>
    seedFailure ctx pos f "'\\palette[seeds]'" "the seeds stand as given"
    let out := [(Role.page, paper), (.ink, ink), (.accent, accent)].foldl
      (fun p (r, c) => p.declare (.role r) c) pal
    noteSeeded ctx pos pal out
    resolveBeamerColors ctx out
where
  missingSeed : EM Palette := do
    diag ctx .E0320 "'\\palette[seeds]' needs an ink, a paper and an accent" pos
      (help := "\\palette[seeds]{ ink = #1E1B2E, paper = #FFFFFF, accent = #E85D2A }")
    return pal


private def applyPalette (ctx : Ctx) (pal : Palette) (src : String)
    (pos : Pos) (decorative : Bool := false) (seeds : Bool := false)
    (depth : GroundDepth := .documents) (inBody : Bool := false) : EM Palette := do
  if seeds then return ← applySeeds ctx pal src pos depth inBody
  let mut pal := pal
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | none =>
      diag ctx .E0320 s!"invalid entry in '\\palette': {entry.quote}" pos
        (help := "entries look like: name = #RRGGBB")
    | some (key, valueSrc) =>
      pal ← applyPaletteEntry ctx pal key valueSrc entry pos decorative (inBody := inBody) (depth := depth)
  resolveBeamerColors ctx pal


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
        | some t => params := params.push { name, type := t, optional }
        | none =>
          diag ctx .E0303 s!"unknown parameter type '{ty}' for '{name}'" pos
            (help := "types: text | content")
    | _ =>
      diag ctx .E0303 s!"malformed parameter '{entry.trimAscii.toString}'" pos
        (help := "expected name: type")
  return params


/-- The outcome of redefining a rendered built-in. -/
private inductive RedefVerdict where
  | wins
  | empty
  | refused (d : Diag)

private def refuseRedef (cmd : UserCmd) (verdict : RedefVerdict) : EM Unit := do
  let (msg, detail) : String × Option String := match verdict with
    | .refused d =>
      let construct := match d.message.splitOn "'" with
        | _ :: q :: _ => s!"'{q}'"
        | _ => "a construct"
      (s!"the redefinition of '\\{cmd.name}' uses {construct}, which the \
engine cannot run; the built-in stands",
        d.span.map fun (sp : Span) => s!"{construct} at {sp.file}:{sp.pos.line}")
    | _ => (s!"the redefinition of '\\{cmd.name}' renders nothing; the built-in stands", none)
  modify fun st => { st with
    diags := st.diags.push (Diag.of .W0361 msg (some cmd.span) (detail := detail)) }

private theorem sliceWeight_end (raws : Array Raw) {j : Nat}
    (h : raws.size ≤ j) : sliceWeight raws j = 0 := by
  rw [sliceWeight_eq]; exact sliceMeas_end rawWeight raws h

private theorem slicePars_end (raws : Array Raw) {j : Nat}
    (h : raws.size ≤ j) : slicePars raws j = 0 := by
  rw [slicePars_eq]; exact sliceMeas_end nestedPars raws h

private theorem sliceWeight_zero (a : Array Raw) :
    sliceWeight a 0 = rawWeightList a.toList := by rfl

private theorem slicePars_zero (a : Array Raw) :
    slicePars a 0 = nestedParsList a.toList := by rfl

/-- The measures the block knot reads at a group `raws[j]` reached from `i`. -/
private theorem group_measures {raws g : Array Raw} {i j : Nat} {p : Pos}
    (hg : raws[j]? = some (.group g p)) (hij : i ≤ j) :
    rawWeightList g.toList + 1 ≤ sliceWeight raws j ∧ nestedParsList g.toList ≤ slicePars raws j ∧
      sliceWeight raws j ≤ sliceWeight raws i ∧ slicePars raws j ≤ slicePars raws i ∧
      sliceWeight g 0 = rawWeightList g.toList ∧ slicePars g 0 = nestedParsList g.toList := by
  have hw := elem_weight_le hg (Nat.le_refl j)
  have hp := elem_pars_le hg (Nat.le_refl j)
  simp only [rawWeight, nestedPars] at hw hp
  exact ⟨by omega, Nat.le_trans (nestedParsList_le g.toList) hp, sliceWeight_le raws hij,
    slicePars_le raws hij, sliceWeight_zero _, slicePars_zero _⟩

/-- The measures the block knot reads at an environment `raws[j]`. -/
private theorem env_measures {raws b : Array Raw} {j : Nat} {n : String} {p : Pos}
    (he : raws[j]? = some (.env n b p)) :
    rawWeightList b.toList + 1 ≤ sliceWeight raws j ∧ rawParsList b.toList ≤ slicePars raws j := by
  have hw := elem_weight_le he (Nat.le_refl j)
  have hp := elem_pars_le he (Nat.le_refl j)
  simp only [rawWeight, nestedPars] at hw hp
  exact ⟨by omega, hp⟩

/-- The measures the block knot reads when it advances from `raws[i]` to `j`. -/
private theorem advance_measures (raws : Array Raw) {i j : Nat} (hi : i < raws.size) (hij : i < j) :
    sliceWeight raws j < sliceWeight raws i ∧ slicePars raws j ≤ slicePars raws i :=
  ⟨sliceWeight_lt raws hi hij, slicePars_le raws (Nat.le_of_lt hij)⟩

/-- The measures the block knot reads at the rest of a scope from `j`. -/
private theorem rest_measures (raws : Array Raw) (j : Nat) :
    rawWeightList (raws.extract j raws.size).toList ≤ sliceWeight raws j ∧
      nestedParsList (raws.extract j raws.size).toList ≤ slicePars raws j ∧
      sliceWeight (raws.extract j raws.size) 0 = rawWeightList (raws.extract j raws.size).toList ∧
      slicePars (raws.extract j raws.size) 0 = nestedParsList (raws.extract j raws.size).toList :=
  ⟨extract_slice_le .., extract_slice_pars_le .., sliceWeight_zero _, slicePars_zero _⟩

/-- The measures the block knot reads at a body's tail from `k`. -/
private theorem tail_measures (body : Array Raw) (k : Nat) :
    rawWeightList (body.extract k body.size).toList ≤ rawWeightList body.toList ∧
      nestedParsList (body.extract k body.size).toList ≤ nestedParsList body.toList ∧
      sliceWeight (body.extract k body.size) 0 = rawWeightList (body.extract k body.size).toList ∧
      slicePars (body.extract k body.size) 0 = nestedParsList (body.extract k body.size).toList :=
  ⟨extract_weight_le .., extract_nested_le .., sliceWeight_zero _, slicePars_zero _⟩

private theorem trimRaws_weight_le (raws : Array Raw) :
    rawWeightList (trimRaws raws).toList ≤ rawWeightList raws.toList := by
  unfold trimRaws trimBy
  exact extract_weight_le ..

private theorem trimRaws_pars_le (raws : Array Raw) :
    rawParsList (trimRaws raws).toList ≤ rawParsList raws.toList := by
  unfold trimRaws trimBy
  exact extract_pars_le ..

/-- The first `{...}` group at or past `k`, with the index just after it. -/
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

/-- A declarative title-styling construct read from a refused `\maketitle`
body. -/
private inductive BarEvent where
  /-- A `\vskip`; its length is not read. -/
  | gap
  /-- An `\hrule`; `none` when its declared height cannot be read. -/
  | bar (w : Option Dim.SymGlue)
  /-- `\@title`, with the size, weight and alignment in force. -/
  | title (size : Option String) (bold : Bool) (align : Option Ir.HAlign)
  /-- `\@author`, with the weight in force and whether a zero-width `\rule`
  strut props its line. -/
  | author (bold : Bool) (strut : Bool)
  /-- Ink that is not the title. -/
  | content

/-- The declarations in force at a point of the scanned body. -/
private structure BarSt where
  size : Option String := none
  bold : Bool := false
  align : Option Ir.HAlign := none
  strut : Bool := false

private def barSkipSp : List Raw → List Raw
  | [] => []
  | .space :: rest => barSkipSp rest
  | r :: rest => r :: rest

/-- A length read at the head of a raw run; `-\parskip` reads as `cancel`. -/
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

/-- An `\hrule`'s declared height, TeX's 0.4 pt default when bare (TeXbook
ch. 21); `none` when a written height cannot be read. -/
private def barRuleWeight (l : List Raw) : Option Dim.SymGlue :=
  match barSkipSp l with
  | .word "height" _ :: rest =>
    match barLength rest with
    | .len g => some g
    | _ => none
  | _ => some { width := Dim.Length.ofSp (Dim.pt 2 / 5) }

/-- A word that is a construct's operand rather than ink: a length, a
number, a sign or a dimension keyword. -/
private def barWordTransparent (w : String) : Bool :=
  ["-", "height", "width", "depth", "to", "plus", "minus"].contains w ||
    (match Decl.parseValue w with
      | some (.dim _) | some (.glue _) | some (.int _) => true
      | _ => false)

private def sizeCtrlNames : List String := Ir.sizeScale.map (·.1)

/-- Beamer's `\insert…` metadata commands, each mapped to the LaTeX internal
a refused body's scans read. -/
public def beamerInsertAlias : List (String × String) :=
  [("inserttitle", "@title"),
   ("insertshorttitle", "@title"),
   ("insertauthor", "@author"),
   ("insertshortauthor", "@author"),
   ("insertdate", "@date"),
   ("insertshortdate", "@date"),
   ("insertsubtitle", "@date"),
   ("insertinstitute", "@date"),
   ("insertshortinstitute", "@date")]

public def barCtrlName (n : String) : String := (beamerInsertAlias.lookup n).getD n

/-- Whether a zero-width `\rule` strut stands in the raws, groups looked
through. -/
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
decreasing_by raws_dec

/-- The size, weight and alignment a refused environment redefinition's
begin body declares, groups looked through. -/
private def envStyleScanList (st : BarSt) : List Raw → BarSt
  | [] => st
  | .group body _ :: rest => envStyleScanList (envStyleScanList st body.toList) rest
  | .ctrl n _ :: rest =>
    if sizeCtrlNames.contains n then envStyleScanList { st with size := some n } rest
    else if n == "bf" || n == "bfseries" then
      envStyleScanList { st with bold := true } rest
    else if n == "centerline" || n == "centering" then
      envStyleScanList { st with align := some .center } rest
    else if let some side := Ir.raggedSideOf? n then
      envStyleScanList { st with align := some side.halign } rest
    else envStyleScanList st rest
  | _ :: rest => envStyleScanList st rest
termination_by l => sizeOf l
decreasing_by raws_dec

/-- The size a refused environment redefinition's body sets at: the last
top-level size switch in the begin body, or in an environment that ends it. -/
private def envBodySizeList (acc : Option String) : List Raw → Option String
  | [] => acc
  | [.env _ body _] => envBodySizeList acc body.toList
  | .ctrl n _ :: rest =>
    envBodySizeList (if sizeCtrlNames.contains n then some n else acc) rest
  | _ :: rest => envBodySizeList acc rest
termination_by l => sizeOf l
decreasing_by raws_dec

/-- Whether a redefined environment's begin body leaves a quotation open for its end body to
close, as `\begin{quote}` or `\quotation` does. -/
private def opensQuotation : List Raw → Bool
  | [] => false
  | .env n _ _ :: rest =>
    ["quote", "quotation"].any (some · == Parse.splitOpen? n) || opensQuotation rest
  | .ctrl n _ :: rest => n == "quote" || n == "quotation" || opensQuotation rest
  | _ :: rest => opensQuotation rest

/-- latex.ltx commands that set no ink, with how many argument groups each
takes. -/
private def inklessArgs : List (String × Nat) :=
  [("addcontentsline", 3), ("addtocontents", 2), ("markboth", 2), ("markright", 1),
   ("label", 1), ("index", 1), ("vspace", 1), ("hspace", 1), ("thispagestyle", 1)]

/-- The words a redefined environment's begin body sets ahead of its body,
skipping lengths, options and inkless commands' arguments; `skip` counts the
groups still owed such a command. -/
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
decreasing_by raws_dec

/-- The font template for a size and a weight; `none` for neither. -/
private def fontFragment (size : Option String) (bold : Bool) :
    Option (Array Ir.Inline) :=
  match size, bold with
  | some s, true => some #[.styled (.size s) #[.styled .bold #[]]]
  | some s, false => some #[.styled (.size s) #[]]
  | none, true => some #[.styled .bold #[]]
  | none, false => none

private def envStyleInterpret (sc : BarSt) : Option Ir.ElementStyle :=
  let font := fontFragment sc.size sc.bold
  if font.isNone && sc.align.isNone then none
  else some { font := font, align := sc.align }

/-- The title-styling events of a refused body, expanding user commands below
`bound` and scoping declarations to their group or environment. -/
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
      barScanList user bound { st with align := some .center } events rest
    else if let some side := Ir.raggedSideOf? n then
      barScanList user bound { st with align := some side.halign } events rest
    else if n == "@title" then
      barScanList user bound st (events.push (.title st.size st.bold st.align)) rest
    else if n == "@author" then
      barScanList user bound st (events.push (.author st.bold st.strut)) rest
    else if n == "@date" then
      barScanList user bound st (events.push .content) rest
    else
      match latestNamed (·.name) user n bound with
      | some (k, cmd) =>
        if _h : k < bound then
          let events := barScanList user k st events cmd.body.toList
          barScanList user bound st events rest
        else
          barScanList user bound st events rest
      | none =>
        barScanList user bound st events rest
termination_by l => (bound, sizeOf l)
decreasing_by raws_dec

private theorem barScan_alias_agree (user : Array UserCmd) (bound : Nat) (st : BarSt)
    (events : Array BarEvent) (post : List Raw) (p q : Pos) (b l : String)
    (hb : barCtrlName b = l) (hl : barCtrlName l = l) :
    barScanList user bound st events (.ctrl b p :: post)
      = barScanList user bound st events (.ctrl l q :: post) := by
  rw [barScanList, barScanList, hb, hl]

public theorem barCtrlName_alias_resolves :
    (beamerInsertAlias.all fun r =>
      barCtrlName r.1 == r.2 && barCtrlName r.2 == r.2) = true := by
  decide +kernel

/-- The element style a refused title body's events declare: the weights of
the bars nearest the title, its font and alignment, and the author's weight
and strut; `none` without a `\@title`. -/
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
  -- The author's strut and trailing gap are the engine's, not the body's.
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

mutual

/-- A refused title body with beamer's inserts resolved to the internals
they alias; math and verbatim stay opaque. -/
public def declarativeTitleRaw : Raw → Raw
  | .ctrl n p => .ctrl (barCtrlName n) p
  | .group body p => .group (declarativeTitleList #[] body.toList) p
  | .env n body p => .env n (declarativeTitleList #[] body.toList) p
  | .word s p => .word s p
  | .space => .space
  | .par p => .par p
  | .sym c p => .sym c p
  | .math d body p => .math d body p
  | .verb n s p => .verb n s p

public def declarativeTitleList (acc : Array Raw) : List Raw → Array Raw
  | [] => acc
  | r :: rest => declarativeTitleList (acc.push (declarativeTitleRaw r)) rest

end

public theorem declarativeTitleList_toList (acc : Array Raw) (rs : List Raw) :
    (declarativeTitleList acc rs).toList =
      acc.toList ++ rs.map declarativeTitleRaw := by
  induction rs generalizing acc with
  | nil => simp [declarativeTitleList]
  | cons r rs ih => simp [declarativeTitleList, ih, List.append_assoc]

/-- The element style a refused `\maketitle` body still declares. -/
public def refusedTitleReadout (user : Array UserCmd) (bound : Nat) (body : Array Raw) :
    Option Ir.ElementStyle :=
  barInterpret (barScanList user bound {} #[]
    (declarativeTitleList #[] body.toList).toList)

private def referencesParam (name : String) : List Raw → Bool
  | [] => false
  | .ctrl n _ :: rest => n == name || referencesParam name rest
  | .group body _ :: rest => referencesParam name body.toList || referencesParam name rest
  | .env _ body _ :: rest => referencesParam name body.toList || referencesParam name rest
  | .math _ body _ :: rest => referencesParam name body.toList || referencesParam name rest
  | _ :: rest => referencesParam name rest
termination_by l => sizeOf l
decreasing_by raws_dec

/-- Reads `\define \name(sig) {body}` after its head, returning the command
and the index after its body. -/
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
        let params := params.map fun p =>
          { p with referenced := referencesParam p.name b.toList, code := referencesParamCode p.name b.toList }
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

/-- Binds a document-defined command at the visibility boundary, which then
advances past it alone. -/
private def bindCmd (ctx : Ctx) (cmd : UserCmd) : Ctx :=
  let b := min ctx.limit ctx.user.size
  { ctx with
    user := (ctx.user.extract 0 b).push cmd ++ ctx.user.extract b ctx.user.size
    limit := b + 1 }

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

private theorem bindCmd_visWeight (ctx : Ctx) (cmd : UserCmd) :
    visWeightGo (bindCmd ctx cmd).user (bindCmd ctx cmd).limit
      ≤ visWeightGo ctx.user ctx.limit + rawWeightList cmd.body.toList := by
  unfold visWeightGo; exact bindCmd_visGo _ ctx cmd

private theorem bindCmd_visPars (ctx : Ctx) (cmd : UserCmd) :
    visParsGo (bindCmd ctx cmd).user (bindCmd ctx cmd).limit
      ≤ visParsGo ctx.user ctx.limit + rawParsList cmd.body.toList := by
  unfold visParsGo; exact bindCmd_visGo _ ctx cmd

/-- The note component of the block knot's measure: `2` outside a note body
and `0` inside one, where draining stashed notes is refused. -/
private def noteFlag (ctx : Ctx) : Nat :=
  match ctx.noteBody with
  | true => 0
  | false => 2


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

/-- Discharges a block-knot termination goal by `lex6_of` and `omega`,
normalising the goal first only when that fails. -/
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

/-- A measure summed over list items, each item's raws measured by `μ`. -/
private def itemsMeas (μ : List Raw → Nat) (l : List (Array Raw)) : Nat :=
  measList (fun it => μ it.toList) l

private theorem itemsMeas_push (μ : List Raw → Nat) (a : Array (Array Raw)) (it : Array Raw) :
    itemsMeas μ (a.push it).toList = itemsMeas μ a.toList + μ it.toList :=
  measList_push ..

private theorem itemsMeas_elem_le (μ : List Raw → Nat) {a : Array (Array Raw)} {m : Nat}
    {it : Array Raw} (h : a[m]? = some it) : μ it.toList ≤ itemsMeas μ a.toList := by
  obtain ⟨hm, hget⟩ := Array.getElem?_eq_some_iff.mp h
  exact measList_mem_le (μ := fun it => μ it.toList) (hget ▸ Array.getElem_mem_toList hm)

/-- A split's bounds: the raws kept so far and the unread slice fit in `bound` by weight and in
`pbound` by nested pars. -/
private def SliceFits (cur body : Array Raw) (j bound pbound : Nat) : Prop :=
  rawWeightList cur.toList + sliceWeight body j ≤ bound ∧
    nestedParsList cur.toList + slicePars body j ≤ pbound

private theorem SliceFits.start (body : Array Raw) (j : Nat) :
    SliceFits #[] body j (sliceWeight body j) (slicePars body j) := by
  simp [SliceFits, rawWeightList, nestedParsList]

private theorem SliceFits.skip {cur body : Array Raw} {j k bound pbound : Nat}
    (hf : SliceFits cur body j bound pbound) (hk : j ≤ k) : SliceFits cur body k bound pbound := by
  have := sliceWeight_le body hk
  have := slicePars_le body hk
  unfold SliceFits at hf ⊢
  omega

private theorem SliceFits.keep {cur body : Array Raw} {j bound pbound : Nat} {r : Raw}
    (hf : SliceFits cur body j bound pbound) (h : j < body.size) (hr : body[j] = r) :
    SliceFits (cur.push r) body (j + 1) bound pbound := by
  have h1 := sliceWeight_here body h
  have h2 := slicePars_here body h
  rw [hr] at h1 h2
  unfold SliceFits at hf ⊢
  rw [rawWeightList_push, nestedParsList_push]
  omega

private theorem SliceFits.flush {cur body : Array Raw} {j k bound pbound : Nat}
    (hf : SliceFits cur body j bound pbound) (hk : j ≤ k) : SliceFits #[] body k bound pbound := by
  have := sliceWeight_le body hk
  have := slicePars_le body hk
  have h0 := SliceFits.start body k
  unfold SliceFits at hf h0 ⊢
  omega

private theorem SliceFits.whole (body : Array Raw) (j : Nat) :
    SliceFits #[] body j (rawWeightList body.toList) (nestedParsList body.toList) := by
  have h := (SliceFits.start body 0).skip (Nat.zero_le j)
  rwa [sliceWeight_zero, slicePars_zero] at h

private theorem SliceFits.bounds {cur body : Array Raw} {j bound pbound : Nat}
    (hf : SliceFits cur body j bound pbound) :
    rawWeightList cur.toList ≤ bound ∧ nestedParsList cur.toList ≤ pbound ∧
      sliceWeight body j ≤ bound ∧ slicePars body j ≤ pbound := by
  unfold SliceFits at hf
  omega

/-- Splits a frame body into its last `\frametitle`, with any subtitle, and
the rest in order. -/
private def frameRestGo (ctx : Ctx) (body : Array Raw) (j : Nat)
    (title subtitle : Array Inline) (rest : Array Raw) (bound pbound : Nat)
    (hf : SliceFits rest body j bound pbound) :
    EM (Array Inline × { rest : Array Raw //
      rawWeightList rest.toList ≤ bound ∧ nestedParsList rest.toList ≤ pbound }) := do
  if h : j < body.size then
    match hj : body[j], body[j + 1]? with
    | .ctrl "frametitle" fpos, some (.group t _) =>
      unless title.isEmpty do
        diag ctx .W0311 "this '\\frametitle' replaces the frame's earlier title"
          (some fpos) (help := "the last one wins; remove the other '\\frametitle'")
      let title ← elabInlines ctx t
      frameRestGo ctx body (j + 2) title subtitle rest bound pbound (hf.skip (by omega))
    | .ctrl "framesubtitle" fpos, some (.group t _) =>
      unless subtitle.isEmpty do
        diag ctx .W0311 "this '\\framesubtitle' replaces the frame's earlier subtitle"
          (some fpos) (help := "the last one wins; remove the other '\\framesubtitle'")
      let subtitle ← elabInlines ctx t
      frameRestGo ctx body (j + 2) title subtitle rest bound pbound (hf.skip (by omega))
    | r', _ =>
      frameRestGo ctx body (j + 1) title subtitle (rest.push r') bound pbound (hf.keep h hj)
  else
    -- Beamer's frame-title template sets the subtitle only under a title.
    let title := if title.isEmpty || subtitle.isEmpty then title else
      title ++ #[.linebreak {}, .colored (Design.ofPalette ctx.palette).framesubtitle
        (some (.role .frameSubtitleInk)) #[.styled (.size "small") subtitle]]
    return (title, ⟨rest, hf.bounds.1, hf.bounds.2.1⟩)
termination_by body.size - j

/-- Splits a subfigure body into its last `\caption`, whether that caption
stands above the content, and the rest; `\centering` is dropped. -/
private def subRestGo (ctx : Ctx) (sn : String) (sbody : Array Raw) (q : Nat)
    (sCaption : Array Inline) (sCapAbove : Bool) (sRest : Array Raw)
    (bound pbound : Nat) (hf : SliceFits sRest sbody q bound pbound) :
    EM (Array Inline × Bool × { sRest : Array Raw //
      rawWeightList sRest.toList ≤ bound ∧ nestedParsList sRest.toList ≤ pbound }) := do
  if h : q < sbody.size then
    match hq : sbody[q] with
    | .ctrl "caption" cpos =>
      let (⟨q2, hq2⟩, _, _) ← skipOptArg ctx "caption" sbody (q + 1) cpos
      let q3 := skipSpaces sbody q2
      have hq3 := skipSpaces_ge sbody q2
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
          (hf.skip (by omega))
      | _ =>
        diag ctx .E0304 "'\\caption' needs a {text} group" cpos
        subRestGo ctx sn sbody q3 sCaption sCapAbove sRest bound pbound (hf.skip (by omega))
    | .ctrl "centering" _ =>
      subRestGo ctx sn sbody (q + 1) sCaption sCapAbove sRest bound pbound (hf.skip (by omega))
    | r' =>
      subRestGo ctx sn sbody (q + 1) sCaption sCapAbove (sRest.push r') bound pbound
        (hf.keep h hq)
  else
    return (sCaption, sCapAbove, ⟨sRest, hf.bounds.1, hf.bounds.2.1⟩)
termination_by sbody.size - q
decreasing_by all_goals omega

/-- A float body with its `center` and `centering` environments spliced in,
so their captions and labels are the float's own. -/
-- conserves: none — drops the grouping wrapper by design
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

/-- An item split's bounds: the items so far, the current item and the unread slice fit in
`bound` by weight and in `pbound` by nested pars. -/
private def ItemSplitFits (items : Array (Array Raw)) (cur body : Array Raw)
    (j bound pbound : Nat) : Prop :=
  itemsMeas rawWeightList items.toList + rawWeightList cur.toList + sliceWeight body j ≤ bound ∧
    itemsMeas nestedParsList items.toList + nestedParsList cur.toList + slicePars body j ≤ pbound

private theorem ItemSplitFits.start (body : Array Raw) (j : Nat) :
    ItemSplitFits #[] #[] body j (sliceWeight body j) (slicePars body j) := by
  simp [ItemSplitFits, itemsMeas, measList, rawWeightList, nestedParsList]

private theorem ItemSplitFits.skip {items : Array (Array Raw)} {cur body : Array Raw}
    {j k bound pbound : Nat} (hf : ItemSplitFits items cur body j bound pbound) (h : j < body.size)
    (hk : j + 1 ≤ k) : ItemSplitFits items cur body k bound pbound := by
  have := sliceWeight_here body h
  have := slicePars_here body h
  have := sliceWeight_le body hk
  have := slicePars_le body hk
  unfold ItemSplitFits at hf ⊢
  omega

private theorem ItemSplitFits.keep {items : Array (Array Raw)} {cur body : Array Raw}
    {j bound pbound : Nat} (hf : ItemSplitFits items cur body j bound pbound) (h : j < body.size) :
    ItemSplitFits items (cur.push body[j]) body (j + 1) bound pbound := by
  have := sliceWeight_here body h
  have := slicePars_here body h
  unfold ItemSplitFits at hf ⊢
  rw [rawWeightList_push, nestedParsList_push]
  omega

private theorem ItemSplitFits.close {items : Array (Array Raw)} {cur body : Array Raw}
    {j bound pbound : Nat} (hf : ItemSplitFits items cur body j bound pbound) (h : j < body.size) :
    ItemSplitFits (items.push cur) #[] body (j + 1) bound pbound := by
  have := sliceWeight_here body h
  have := slicePars_here body h
  unfold ItemSplitFits at hf ⊢
  rw [itemsMeas_push, itemsMeas_push]
  simp only [rawWeightList, nestedParsList]
  omega

private theorem ItemSplitFits.restart {items : Array (Array Raw)} {cur body : Array Raw}
    {j bound pbound : Nat} (hf : ItemSplitFits items cur body j bound pbound) (h : j < body.size) :
    ItemSplitFits items #[] body (j + 1) bound pbound := by
  have := sliceWeight_here body h
  have := slicePars_here body h
  unfold ItemSplitFits at hf ⊢
  simp only [rawWeightList, nestedParsList]
  omega

private theorem ItemSplitFits.done {items : Array (Array Raw)} {cur body : Array Raw}
    {j bound pbound : Nat} (hf : ItemSplitFits items cur body j bound pbound) (h : body.size ≤ j) :
    (itemsMeas rawWeightList (items.push cur).toList ≤ bound ∧
      itemsMeas nestedParsList (items.push cur).toList ≤ pbound) ∧
    (itemsMeas rawWeightList items.toList ≤ bound ∧
      itemsMeas nestedParsList items.toList ≤ pbound) := by
  have := sliceWeight_end body h
  have := slicePars_end body h
  unfold ItemSplitFits at hf
  rw [itemsMeas_push, itemsMeas_push]
  omega

/-- Splits a list body at its `\item`s, each item with its overlay step and
the `\pause` count before it. -/
private def itemSplitGo (ctx : Ctx) (body : Array Raw) (pos : Pos) (desc : Bool) (scope : ListScope) (j : Nat)
    (items : Array (Array Raw)) (steps : Array (Option Ir.OverlaySpec))
    (itemPauses : Array Nat) (pauses : Nat) (curItem : Array Raw)
    (curStep : Option Ir.OverlaySpec) (curPauses : Nat)
    (awaitSpec inOpt seen strayDiagged : Bool) (bound pbound : Nat)
    (hfit : ItemSplitFits items curItem body j bound pbound) :
    EM { r : Array (Array Raw) × Array (Option Ir.OverlaySpec) × Array Nat × ListScope //
      itemsMeas rawWeightList r.1.toList ≤ bound ∧
        itemsMeas nestedParsList r.1.toList ≤ pbound } := do
  if h : j < body.size then
    match body[j] with
    | .ctrl "item" _ =>
      if seen then
        itemSplitGo ctx body pos desc scope (j + 1) (items.push curItem)
          (steps.push curStep) (itemPauses.push curPauses) pauses #[]
          none pauses true inOpt true strayDiagged bound pbound
          (hfit.close h)
      else
        itemSplitGo ctx body pos desc scope (j + 1) items steps itemPauses pauses #[]
          none pauses true inOpt true strayDiagged bound pbound
          (hfit.restart h)
    | .ctrl "pause" _ =>
      -- Also kept in the item, so a mid-item pause steps the item's rest.
      if seen then
        itemSplitGo ctx body pos desc scope (j + 1) items steps itemPauses (pauses + 1)
          (curItem.push body[j]) curStep curPauses awaitSpec inOpt seen
          strayDiagged bound pbound
          (hfit.keep h)
      else
        itemSplitGo ctx body pos desc scope (j + 1) items steps itemPauses (pauses + 1)
          curItem curStep curPauses awaitSpec inOpt seen strayDiagged bound pbound
          (hfit.skip h .refl)
    | item =>
      if inOpt then
        let inOpt := !(item matches .sym ']' _)
        itemSplitGo ctx body pos desc scope (j + 1) items steps itemPauses pauses curItem
          curStep curPauses awaitSpec inOpt seen strayDiagged bound pbound
          (hfit.skip h .refl)
      else
      if seen && awaitSpec && !isSpace item then
        if item matches .sym '[' _ then
          -- A description item's label is content, not a marker override.
          unless desc do
            warnOnce ctx "item:marker" .W0110
              "'\\item' [marker] override is not modelled; the level's marker stands" pos
              (help := "\\style{itemize}{ marker = {...} } declares a level's marker")
          itemSplitGo ctx body pos desc scope (j + 1) items steps itemPauses pauses curItem
            curStep curPauses false true seen strayDiagged bound pbound
            (hfit.skip h .refl)
        else if let some w := specWord? item then
          let curStep ← match Ir.overlayRange w with
            | some s => pure (some s)
            | none => do
              warnOverlaySpec ctx w pos
              pure curStep
          itemSplitGo ctx body pos desc scope (j + 1) items steps itemPauses pauses curItem
            curStep curPauses awaitSpec inOpt seen strayDiagged bound pbound
            (hfit.skip h .refl)
        else
          itemSplitGo ctx body pos desc scope (j + 1) items steps itemPauses pauses
            (curItem.push body[j]) curStep curPauses false inOpt seen strayDiagged
            bound pbound
            (hfit.keep h)
      else if seen then
        itemSplitGo ctx body pos desc scope (j + 1) items steps itemPauses pauses
          (curItem.push body[j]) curStep curPauses awaitSpec inOpt seen strayDiagged
          bound pbound
          (hfit.keep h)
      else do
        if let .ctrl c cpos := item then
          if counterCtrl c then
            -- ltlists.dtx: a counter set before the first `\item` declares.
            let ⟨k, hk⟩ ← counterArm ctx body (j + 1) c pos
            return ← itemSplitGo ctx body pos desc scope k items steps itemPauses pauses curItem
              curStep curPauses awaitSpec inOpt seen strayDiagged bound pbound
              (hfit.skip h hk)
          if let some scope' ← listScopeCtrl ctx body j c cpos scope then
            return ← itemSplitGo ctx body pos desc scope' (j + 1)
              items steps itemPauses pauses curItem curStep curPauses
              awaitSpec inOpt seen strayDiagged bound pbound
              (hfit.skip h .refl)
        if !isSpaceOrPar item && !strayDiagged then
          diag ctx .E0310 s!"content before the first '\\item'" pos
        itemSplitGo ctx body pos desc scope (j + 1) items steps itemPauses pauses curItem
          curStep curPauses awaitSpec inOpt seen
          (strayDiagged || !isSpaceOrPar item) bound pbound
          (hfit.skip h .refl)
  else
    have hend := hfit.done (show body.size ≤ j by omega)
    if seen then
      return ⟨(items.push curItem, steps.push curStep, itemPauses.push curPauses, scope), hend.1⟩
    else
      return ⟨(items, steps, itemPauses, scope), hend.2⟩
termination_by body.size - j

/-- `ctx` with the palette and tokens that body declarations earlier in flow
order set, unchanged while the declaration generation is still `gen`. -/
private def flowCtx (ctx : Ctx) (st : ESt) (gen : Nat) : Ctx :=
  if st.flowGen != gen then
    { ctx with palette := st.scope.palette.current.getD ctx.palette
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

/-- A context sharing `ctx`'s termination-measure components. -/
private def MCtx (ctx : Ctx) := { c : Ctx // c.envLimit = ctx.envLimit
  ∧ noteFlag c = noteFlag ctx
  ∧ visParsGo c.user c.limit = visParsGo ctx.user ctx.limit
  ∧ visWeightGo c.user c.limit = visWeightGo ctx.user ctx.limit }

private def regionCtx (ctx : Ctx) (ground : Option Color) : MCtx ctx :=
  ⟨{ ctx with ground := ground.or ctx.ground }, rfl, rfl, rfl, rfl⟩

private def barCtx (ctx : Ctx) (bar : Role) : Ctx :=
  (regionCtx ctx (Design.declared? ctx.palette bar)).1

private def titledBodyCtx (ctx : Ctx) (kind : TitledKind) : MCtx ctx :=
  regionCtx ctx (Design.declared? ctx.palette (Role.bodyGround kind))

private def flowMCtx (ctx : Ctx) (st : ESt) (gen : Nat) : MCtx ctx :=
  ⟨flowCtx ctx st gen, flowCtx_measure ctx st gen⟩

private theorem flowMCtx_idle (ctx : Ctx) (st : ESt) :
    flowMCtx ctx st st.flowGen = ⟨ctx, rfl, rfl, rfl, rfl⟩ := by
  apply Subtype.ext
  simp [flowMCtx, flowCtx]

/-- The `\multicolumn` at `raws[j]`: its count when a numeral, its one column
spec with the spec reader's warnings, its text, and the index after it;
`none` without the three groups. -/
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

/-- The span a cell-head `\multicolumn` declares when its count is a numeral,
naming each loss its spec and count carry. -/
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

/-- The expansion of the user command at `raws[j]` when its definition
opens on `\multicolumn`, and how many raws the call took. -/
private def expandSpanHead (ctx : Ctx) (raws : Array Raw) (j : Nat) (name : String) :
    Option (Array Raw × Nat) :=
  (lookupUser ctx name).bind fun (k, cmd) =>
    if (trimRaws cmd.body)[0]? matches some (Raw.ctrl "multicolumn" _) then
      let rest := raws.extract (j + 1) raws.size
      let (bindings, rest') := bindMathArgs cmd.params rest
      some (trimRaws (expandMathList ctx.user k bindings cmd.body.toList),
        1 + (rest.size - rest'.size))
    else none

/-- Records a `\multicolumn` span at the cell just pushed and pushes the
`n − 1` empty cells it covers, keeping the grid rectangular. -/
private def closeSpan (spans : Array Ir.ColSpan) (cells : Array (Array Inline))
    (row : Nat) : Option (Nat × Ir.ColSpec) → Array Ir.ColSpan × Array (Array Inline)
  | none => (spans, cells)
  | some (n, spec) =>
    (spans.push { row := row, col := cells.size - 1, n := n, spec := spec },
      cells ++ Array.replicate (n - 1) #[])

private def tabularArm (ctx : Ctx) (n : String) (body : Array Raw)
    (pos : Pos) (blocks : Array Block) : EM (Array Block) := do
  let mut blocks := blocks
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
    -- A markdown table declares no widths, so its natural columns narrow.
    cols := if n == Parse.markdownTableEnv then
        cs.map fun c => { c with narrows := c.width matches .natural }
      else cs
    padL := pl
    padR := pr
    unless warns.isEmpty do noteMentions (Parse.rawSrc spec)
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
  let mut spanHere : Option (Nat × Ir.ColSpec) := none
  let mut j := k
  let ruleNames := ["toprule", "midrule", "bottomrule", "hline",
    "cmidrule", "cline", "addlinespace"]
  for _ in [k:body.size] do
    if h' : j < body.size then
      match body[j] with
      | .ctrl "\\" bpos =>
        cells := cells.push (Ir.paraAt (← get).scope.blockDecls (← elabInlines ctx (trimRawEdges cellRaws)))
        (spans, cells) := closeSpan spans cells rows.size spanHere
        spanHere := none
        cellRaws := #[]
        rows := rows.push cells
        cells := #[]
        j := j + 1
        match scanBracketArg body j bpos with
        | .took j' =>
          let src := bracketSrc body j j'
          match Decl.parseLength src with
          | some l => do
            rules := rules.push (rows.size, .gap { width := l })
            j := j'
          | none =>
            diag ctx .E0331 s!"unreadable length '{src}' in '\\\\[...]'" (some bpos)
            j := j'
        | _ => pure ()
      | .sym '&' _ =>
        cells := cells.push (Ir.paraAt (← get).scope.blockDecls (← elabInlines ctx (trimRawEdges cellRaws)))
        (spans, cells) := closeSpan spans cells rows.size spanHere
        spanHere := none
        cellRaws := #[]
        j := j + 1
      | .ctrl "multicolumn" rpos =>
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
            -- The `(lr)` trim spec lexes as one word.
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
    cells := cells.push (Ir.paraAt (← get).scope.blockDecls (← elabInlines ctx (trimRawEdges cellRaws)))
    (spans, cells) := closeSpan spans cells rows.size spanHere
    rows := rows.push cells
  -- Every walk below trusts `cols.size`.
  let widest := rows.foldl (fun m r => max m r.size) cols.size
  if cols.size < widest then
    warnOnce ctx "tabular:wide" .W0337
      "a row carries more cells than the column spec declares; the grid widens" pos
      (help := "declare one column type per cell: l, c, r, or p{width}")
      (detail := some s!"{widest} cells where the spec declares {cols.size}")
    for _ in [cols.size:widest] do
      cols := cols.push { width := .natural, align := .left }
  if rows.any (·.size < cols.size) then
    warnOnce ctx "tabular:ragged" .W0337
      "a row carries fewer cells than the column spec; it is \
  padded with empty cells" pos
  rows := Ir.padTableRows rows cols.size
  blocks := blocks.push (.table cols padL padR rows rules spans)
  return blocks

/-- Whether a verbatim runs inline: `\verb` and `\mintinline` always, and a
one-line listing environment when text shares its paragraph. -/
private def verbRunsInline (env s : String) (cur raws : Array Raw) (i : Nat) : Bool :=
  let text (r : Raw) : Bool := match r with
    | .word .. => true
    | .math display _ _ => !display
    | .verb e _ _ => e == "verb" || e == "mintinline"
    | _ => false
  let after : Bool := Id.run do
    for k in [i + 1:raws.size] do
      let some r := raws[k]? | break
      if text r then return true
      if bodyIsBlockOne r then return false
    return false
  env == "verb" || env == "mintinline" ||
    ((env == "minted" || env == "lstlisting") && !s.contains '\n' && (cur.any text || after))

/-- A listing block from a lexically blind capture, honouring the supported
listings and minted keys and naming every other key or value. -/
private def listingBlock (ctx : Ctx) (env s : String) (pos : Pos) : EM Block := do
  -- `\mint` is minted's one-line environment (minted.sty v3.7).
  let (env, s, opener) := if env == "mint" then
      let afterOpt := ((Parse.listingOptHead s).map (·.2)).getD 0
      let afterLang := ((Parse.mintedLangHead s afterOpt).map (·.2)).getD afterOpt
      ("minted", (s.take afterLang).toString ++ bindCodeParams ctx (Parse.mintedCode s afterLang) ++
        "\n", "\\mint")
    else (env, s, "\\begin{" ++ env ++ "}")
  if (env == "minted" || env == "lstlisting") && !s.contains '\n' then
    let lang := if env == "minted" then
        (((Parse.mintedLangHead s ((Parse.listingOptHead s).map (·.2) |>.getD 0)).map
          (·.1.trimAscii.toString)).getD "")
      else ""
    warnOnce ctx ("listing-oneline:" ++ env) .W0411
      s!"'\\begin\{{env}}' with its code on the same line does not compile under LaTeX; it \
is set as a display listing" pos
      (help := s!"put the code on lines of its own between '\\begin\{{env}}" ++
        (if lang.isEmpty then "" else "{" ++ lang ++ "}") ++ s!"' and '\\end\{{env}}'")
  -- Verbatim sets at the ambient size: `\verbatim@font` changes no size.
  let base := ctx.surface.listing
  let inherited := (← get).scope.blockDecls.foldl (fun size decl => match decl with
    | .style s@(.size _) | .style s@(.fontSize _ _) => s
    | _ => size) base.fontSize
  let sourceStart := opener.foldl (fun p c => p.next (c == '\n')) pos
  if env == "verbatim" then
    return .verbatim none s
      { base with
        fontSize := inherited, source := some (ctx.sourceSpan sourceStart)
        frame := Ir.ListingFrame.onPage ctx.surface ctx.lists ctx.page.parskip .trivlist }
  let (opts, afterOpt) := (Parse.listingOptHead s).getD ("", 0)
  let mut content := s
  let mut caption : Option String := none
  let mut label : Option String := none
  let mut numbers := false
  let mut language : Option Ir.ListingLang := none
  let mut style : Option Ir.ListingStyle := none
  let mut fontSize := inherited
  let mut tabSize := base.tabSize
  let mut breakLines := base.breakLines
  let mut ground := base.ground
  -- Keyed by its words and its key: listings share a loss when they print the same.
  let unhonoured (item key msg : String) (help : Option String) : EM Unit := do
    noteMentions item
    warnOnce ctx ("lstopt:" ++ msg ++ ":" ++ key) .W0110 msg pos (help := help)
  let langOf (raw : String) : EM (Option Ir.ListingLang) := codeLanguage ctx raw (env == "minted") pos
  for bare in KeyVal.items opts do
    let key := ((KeyVal.pair? bare).map (·.1)).getD bare
    if env == "minted" && ((KeyVal.pair? bare).map (·.1) == some "formatcom" ||
        bare == "formatcom" || bare.startsWith "formatcom=") then
      noteMentions bare
      noteFormatcom ctx pos
      continue
    if env == "minted" && keepsSize bare then
      fontSize := inherited
      continue
    match KeyVal.pair? bare with
    | some ("caption", v) =>
      let v := listingVal v
      caption := if v.isEmpty then none else some v
    | some ("label", v) => label := some (listingVal v)
    | some ("numbers", v) =>
      let v := v.trimAscii.toString
      if v == "left" then numbers := true
      else if v == "none" then numbers := false
      else
        unhonoured bare key s!"'numbers={v}' asks for a numbering the engine \
does not draw; lines keep no numbers" "numbers=left draws them"
    | some ("linenos", v) =>
      numbers := v.trimAscii.toString != "false"
    | some ("language", v) =>
      if env == "minted" then
        unhonoured bare key "minted has no key 'language'; the language argument names the lexer"
          s!"name the language in \\begin\{minted}\{{(listingVal v).trimAscii.toString}}"
      else language ← langOf (listingVal v)
    | some ("style", v) =>
      let v := listingVal v
      if env == "minted" then
        match Ir.ListingStyle.ofName? v with
        | some selected => style := some selected
        | none =>
          unhonoured bare key
            s!"listing style '{v}' is not supported; the current style stands"
            "use style=default or style=friendly"
      else
        unhonoured bare key
          s!"listing named style '{v}' is not supported; the current style stands" none
    | some ("fontsize", v) =>
      let v := listingVal v
      if env == "minted" && (sizeCommand? v).isSome then
        fontSize := .size ((sizeCommand? v).getD "normalsize")
      else
        unhonoured bare key s!"listing fontsize '{v}' is not a supported size command; \
the current size stands" "use a named size command such as fontsize=\\small, or fontsize=auto"
    | some ("tabsize", v) =>
      let v := listingVal v
      -- FancyVerb's upper bound (fancyvrb.sty, the FV/tabsize key).
      match v.toNat? with
      | some n =>
        if 0 < n && n ≤ 100 then tabSize := n
        else unhonoured bare key s!"listing tabsize '{v}' is outside 1..100; \
the current tab stops stand" none
      | none =>
        unhonoured bare key s!"listing tabsize '{v}' is not an integer; \
the current tab stops stand" none
    | some ("bgcolor", v) =>
      let v := listingVal v
      if env != "minted" then
        unhonoured bare key "listing key 'bgcolor' is not honoured; ignored" none
      else if v == "none" || v.isEmpty then ground := none
      else
        noteColorReads v
        match ctx.palette.resolveSource none v with
        | .ok (some c) => ground := some (c, ctx.palette.refOf? v)
        | _ =>
          unhonoured bare key s!"listing bgcolor '{v}' names no colour; the listing keeps the \
ground it stands on" none
    | some ("breaklines", v) =>
      let v := listingVal v
      if v == "true" then breakLines := true
      else if v == "false" then breakLines := false
      else unhonoured bare key s!"listing breaklines '{v}' is not true or false; \
the current wrapping stands" none
    | some ("basicstyle", v) =>
      let v := listingVal v
      let names := v.splitOn "\\"
      let valid := env == "lstlisting" && (names.headD "").trimAscii.isEmpty &&
        names.tail.all (fun name => let name := name.trimAscii.toString
          name == "ttfamily" || Ir.sizeScale.any (·.1 == name))
      if valid then
        fontSize := names.tail.foldl (fun size name =>
          let name := name.trimAscii.toString
          if name == "ttfamily" then size else .size name) inherited
      else
        unhonoured bare key "listing basicstyle supports only \\ttfamily and named \
size commands; the current style stands" none
    | some (k, _) =>
      unhonoured bare key s!"listing key '{k}' is not honoured; ignored" none
    | none =>
      if bare == "linenos" then numbers := true
      else if bare == "breaklines" then breakLines := true
      else unhonoured bare key s!"listing key '{bare}' is not honoured; ignored" none
  if env == "minted" then
    match Parse.mintedLangHead s afterOpt with
    | some (lang, _) => language ← langOf lang
    | none =>
      diag ctx .E0304 s!"'\\begin\{minted}' needs its \{language} argument" (some pos)
    content := (s.drop (listingContentStart env s)).toString
  else
    content := (s.drop afterOpt).toString
  let sourcePrefix := if env == "minted" then listingContentStart env s else afterOpt
  let contentPos := (s.take sourcePrefix).toString.foldl (fun p c => p.next (c == '\n')) sourceStart
  let spec : Ir.ListingSpec := {
    numbers := numbers
    language := language
    style := style
    ground := ground
    fontSize := fontSize
    tabSize := tabSize
    breakLines := breakLines
    lineOverlap := if env == "minted" then Ir.fvextraLineOverlap else 0
    -- fvextra struts each coloured or broken line (`\FV@bgcolorstrut`).
    lineStrut := env == "minted" && (breakLines || ground.isSome)
    -- premise: markdownCodeChecks — lstlisting wraps with its own indent
    breakIndent := if env == "lstlisting" then some Ir.listingBreakIndent else base.breakIndent
    wrapAt := base.wrapAt
    frame := if env == "minted" then Ir.ListingFrame.onPage ctx.surface ctx.lists ctx.page.parskip .list
      else .none
    source := some (ctx.sourceSpan contentPos) }
  let spec ← match caption with
    | some cap => do
      let num := (← get).ctr.lstNum + 1
      modify fun st => { st with ctr := { st.ctr with lstNum := num } }
      match label with
      | some key =>
        -- The anchor rides in the caption so the target ships on the page.
        recordLabel ctx key (some { kind := none, num := toString num }) pos
        pure { spec with caption := some (num, #[.label key, .text cap]) }
      | none =>
        pure { spec with caption := some (num, #[.text cap]) }
    | none => do
      if let some key := label then
        recordLabel ctx key (← get).refTarget pos
      pure spec
  let highlight := match spec.langToken.bind ListingHighlight.language? with
    | some language => ListingHighlight.tokenize language (Ir.verbatimLines content)
    | none => (spec.langToken.bind fun language =>
        ListingReply.lookup ctx.listingReplies language content).getD #[]
  -- premise: codeRoleChecks — unread when the palette colours every role
  if let some declared := style then
    let pal := (← get).scope.palette.current.getD ctx.palette
    if !(ListingHighlight.Role.all.any (CodeColor.styleReads pal)) then
      warnOnce ctx ("lstopt:style:" ++ declared.name) .W0387
        s!"minted's style '{declared.name}' was read and had no effect: the palette names \
or derives a colour for every code role" pos
        (help := "\\allow{W0387} accepts the skip")
  return .verbatim none content { spec with highlight }

/-- amsmath's `\tagform@`: the tag in parentheses, joined to its first and
last text runs. -/
private def tagForm (t : Array Ir.Inline) : Array Ir.Inline :=
  let opened : Array Ir.Inline := match t[0]? with
    | some (Ir.Inline.text s) => t.set! 0 (.text ("(" ++ s))
    | _ => #[Ir.Inline.text "("] ++ t
  match opened.back? with
  | some (Ir.Inline.text s) => opened.pop.push (.text (s ++ ")"))
  | _ => opened.push (.text ")")

private def definedOr (ctx : Ctx) (name : String) (pos : Pos) (dflt : EM (Array Inline)) :
    EM (Array Inline) := do
  if (lookupUser ctx name).isSome then elabInlines ctx #[.ctrl name pos] else dflt

/-- The `\qedsymbol` in force; by default amsthm's box, the math face's □. -/
private def qedMark (ctx : Ctx) (pos : Pos) : EM (Array Inline) :=
  definedOr ctx "qedsymbol" pos (return #[← elabMathInline ctx false #[.ctrl "square" pos] pos])

/-- The display body without its top-level `\qedhere`, and where the first one
stood. -/
private def dropQedHere (body : Array Raw) : Array Raw × Option Pos :=
  body.foldl (fun (out, at?) r => match r with
    | .ctrl "qedhere" p => (out, at?.orElse fun _ => some p)
    | r => (out.push r, at?)) (#[], none)

private def qedHereLost (ctx : Ctx) (env : String) (p : Pos) : EM Unit := do
  if (← get).ctr.thm.proofs == 0 then return
  warnOnce ctx ("qedhere:" ++ env) .W0435
    s!"'\\qedhere' in '\{{env}}' does not set its QED where amsthm sets it; the QED \
stands on a line of its own after the display" p
    (help := "an unnumbered \\[ ... \\] sets it beside the formula")

/-- The QED amsthm's `\displaymath@qed` sets in the number's slot, inside a
proof only; the proof's end then sets none. -/
private def qedHereTag (ctx : Ctx) (p : Pos) : EM (Option (Array Inline)) := do
  if (← get).ctr.thm.proofs == 0 then return none
  let mark ← qedMark ctx p
  modify fun st => { st with ctr := { st.ctr with thm := { st.ctr.thm with qedPlaced := true } } }
  return some (Ir.wrapDecls (← get).scope.blockDecls mark)

/-- The heading numbers a counter within a heading level was stepped under,
as the key whose change restarts it (`\@addtoreset`). -/
private def withinSnap (c : Counters) : Option Nat → String
  | none => ""
  | some lvl =>
    let (s1, s2, s3) := c.secNums
    let levels := match lvl with
      | 1 => s!"{s1}"
      | 2 => s!"{s1}.{s2}"
      | _ => s!"{s1}.{s2}.{s3}"
    (if c.inAppendix then "A" else "") ++ levels

/-- `\the<counter>` for value `v`: `\arabic`, after `\the<within>.` when
numbered within a heading counter. -/
private def withinNumber (c : Counters) (within : Option Nat) (v : Nat) : String :=
  match within with
  | some lvl => s!"{renderSecLevel c.secFmts c.secNums c.inAppendix secFmtFuel lvl}.{v}"
  | none => toString v

/-- Steps the equation counter and renders `\theequation`, restarting within
its heading as amsmath's `\numberwithin` does. -/
private def stepEquation : EM String := do
  let st ← get
  let snap := withinSnap st.ctr st.ctr.eqWithin
  let v := if snap == st.ctr.eqSnap then st.ctr.eqNum + 1 else 1
  modify fun st => { st with ctr := { st.ctr with eqNum := v, eqSnap := snap } }
  return withinNumber st.ctr st.ctr.eqWithin v

private def displayMathArm (ctx : Ctx) (numbered : Bool) (body : Array Raw) (pos : Pos)
    (blocks : Array Block) : EM (Array Block) := do
  let mut blocks := blocks
  let (body, qedAt) := dropQedHere body
  let (cleaned, keys, nonum, tag) ← stripMathMeta ctx body
  if qedAt.isNone && tag.isNone && (!numbered || nonum) then
    if let some pic ← tikzcdNative ctx cleaned pos then
      for key in keys do
        recordLabel ctx key (← get).refTarget pos
      return blocks.push (Ir.displayPictureBlock keys pic)
  let inl ← match ← tikzcdDisplay ctx cleaned pos with
    | some pic => pure pic
    | none => elabMathInline ctx true cleaned pos
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
    -- `\tag{t}` takes the number's place and steps no counter (amsldoc §3.4).
    let t ← elabInlines ctx (trimRaws raws)
    for key in keys do
      recordLabel ctx key (some { kind := some .equation, num := Ir.plainText t }) pos
    let content := keys.map (Ir.Inline.label ·) |>.push inl
    blocks := blocks.push (.equation (if star then t else tagForm t) content)
  else if numbered && !nonum then
    let num ← stepEquation
    for key in keys do
      recordLabel ctx key (some { kind := some .equation, num }) pos
    let content := keys.map (Ir.Inline.label ·) |>.push inl
    blocks := blocks.push (.equation #[.text s!"({num})"] content)
  else
    -- A label here binds to what the flow last numbered (`\@currentlabel`).
    for key in keys do
      recordLabel ctx key (← get).refTarget pos
    let content := keys.map (Ir.Inline.label ·) |>.push inl
    blocks := blocks.push (.center #[.para content])
  return blocks

private def alignEnvArm (ctx : Ctx) (n : String) (kind : Math.GridKind)
    (numbered : Bool) (body : Array Raw) (pos : Pos) (blocks : Array Block) :
    EM (Array Block) := do
  let (body, qedAt) := dropQedHere body
  if let some p := qedAt then qedHereLost ctx n p
  let (cleaned, keys, _, tag) ← stripMathMeta ctx body
  for key in keys do
    recordLabel ctx key none pos
  if !numbered && tag.isNone then
    if let some native ← tikzcdNative ctx cleaned pos then
      return blocks.push (.role ({ align := true } : Ir.DisplayCtx).role
        #[Ir.displayPictureBlock keys native])
  let pic ← if numbered || tag.isSome then pure none else tikzcdDisplay ctx cleaned pos
  let inl ← match pic with
    | some pic => pure pic
    | none => elabMathEnv ctx n kind (numbered || tag.isSome) cleaned pos
  let content := keys.map (Ir.Inline.label ·) |>.push inl
  -- TeX spaces a display alignment with the long skips (tex.web §1206).
  return blocks.push (.role ({ align := true } : Ir.DisplayCtx).role #[.center #[.para content]])

private def sentenceText (r : Raw) : Bool :=
  r matches .word _ _ || r matches .sym _ _ || r matches .math false _ _

/-- Names a `tikzpicture` or `tikzcd` inside a sentence, which the engine sets
as its own block where LaTeX runs the sentence on around it. -/
private def pictureInSentence (ctx : Ctx) (n : String) (cur raws : Array Raw) (i : Nat)
    (pos : Pos) : EM Unit := do
  if n != "tikzpicture" && n != "tikzcd" then return
  let after := (raws.extract (i + 1) raws.size).toList.takeWhile fun r =>
    !(r matches .par _) && (!(r matches .env _ _ _) || Parse.isPlaceKeeper r)
  if cur.any sentenceText || after.any sentenceText then
    warnOnce ctx "picture:inline" .W0334
      "a picture inside a paragraph is set as its own block: the paragraph's text breaks \
at it instead of running on beside it" pos

mutual

private def scopePictureOne (seen : Array Raw) : Raw → Option (String × Pos)
  | .env n _ p => if n == "tikzpicture" || n == "tikzcd" then some (n, p) else none
  | .group b _ =>
    if isArgument seen || b.any sentenceText then none else scopePictureList #[] b.toList
  | _ => none

private def scopePictureList (seen : Array Raw) : List Raw → Option (String × Pos)
  | [] => none
  | r :: rest =>
    match scopePictureOne seen r with
    | some p => some p
    | none => scopePictureList (seen.push r) rest

end

/-- The `tikzpicture` or `tikzcd` a scope group holds beside no text of its
own, through scope groups nested the same way. -/
private def scopePicture? (body : Array Raw) : Option (String × Pos) :=
  if body.any sentenceText then none else scopePictureList #[] body.toList

/-- Names a picture a group at `raws[i]` holds, within the sentence the group
stands in. -/
private def groupPictureInSentence (ctx : Ctx) (body cur raws : Array Raw) (i : Nat) :
    EM Unit :=
  match scopePicture? body with
  | some (n, pos) => pictureInSentence ctx n cur raws i pos
  | none => pure ()

/-- Names a user command whose body is a `tikzpicture` inside a sentence, as a
picture written there is named. -/
private def macroPictureInSentence (ctx : Ctx) (n : String) (cur raws : Array Raw) (i : Nat)
    (pos : Pos) : EM Unit := do
  if let some (_, cmd) := lookupUser ctx n then
    if cmd.body.any (· matches .env "tikzpicture" _ _) then
      pictureInSentence ctx "tikzpicture" cur raws i pos

/-- Marks a colour declaration text stands before in its paragraph as one the unused-setting judge
skips: it ends that paragraph, so deleting it changes the page. -/
private def noteSplitDecl (ctx : Ctx) (n : String) (cur : Array Raw) (pos : Pos) : EM Unit :=
  if n == "palette" && cur.any (!isSpaceOrPar ·) then
    modify fun st => { st with unjudged := st.unjudged.push (ctx.sourceSpan pos) }
  else pure ()

/-- The `{tikzpicture}` arm: the rendered subset's drawing, or a boundary
request for what the subset draws only with a loss, every loss named. -/
private def tikzArm (ctx : Ctx) (body : Array Raw) (pos : Pos)
    (blocks : Array Block) : EM (Array Block) := do
  let mut blocks := blocks
  let (alt, body) := splitPictureAlt body pos
  notePictureReads ctx body
  let (pic, pdiags) := subsetPicture ctx body (← pictureSizeInForce)
  noteLostInks ctx (Parse.rawSrc body) pos pic.gradients
  let pic := { pic with alt := alt }
  let id := Ir.picHash (← pictureSrcAt body).source
  -- premise: pictureRouteChecks — a routed picture's losses are never dropped
  if ctx.pic.tool.isSome && !body.isEmpty &&
      (pic.shapes.isEmpty ||
        (Picture.namesLoss pdiags && !ctx.pic.withdrawn.contains id)) then
    return blocks.push (.para #[← routePicture ctx body pic pos true])
  let declined := ctx.pic.tool.isNone && !pic.shapes.isEmpty && Picture.namesLoss pdiags
  if declined then
    modify fun st => if st.spans.declined.contains id then st
      else { st with spans := { st.spans with declined := st.spans.declined.push id } }
  for (code, msg) in pdiags do
    -- Only a construct outside the subset is helped by the subset's reach.
    let help : Option String := match code with
      | .W0334 => some "write it with paths, nodes, trees, \\foreach and pgfmath values, \
which the rendered subset draws, or let a boundary tool draw it"
      | _ => none
    -- premise: pictureRouteChecks — the driver folds the picture's refusals
    if ctx.pic.withdrawn.contains id || declined then
      warnOnce ctx ("picture:" ++ id ++ ":" ++ msg) code msg pos (help := help)
    else
      warnOnce ctx ("picture:" ++ msg) code msg pos (help := help)
  unless pic.shapes.isEmpty do
    recordNativePictureSpan ctx pos
    blocks := blocks.push (.picture pic)
  -- A refused picture keeps its place, or its float leaves orphan captions.
  if pic.shapes.isEmpty && !pdiags.isEmpty then
    warnOnce ctx "picture:placeholder" .W0362
      "no part of this picture is inside the rendered subset; a \
placeholder box marks its place" pos
      (help := "the box holds the diagram's place; \\allow{W0362} \
accepts the loss")
    recordNativePictureSpan ctx pos
    blocks := blocks.push (.picture (Picture.placeholder DiagCode.W0362.code))
  return blocks


private def pictureEnvArm (ctx : Ctx) (n : String) (body : Array Raw) (pos : Pos)
    (blocks : Array Block) : EM (Array Block) :=
  if n == "tikzcd" then tikzcdArm ctx body pos blocks else tikzArm ctx body pos blocks

/-- The `\maketitle`/`\titlepage` arm: the title is set once, as classes.dtx's
`\maketitle` disables itself. -/
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
    -- The golden split is moloch's `title page` template glue.
    modify fun st => { st with titleDone := true }
    let tps := (ctx.styles.find? "titlepage").getD {}
    -- A slotted title page aligns per slot (`titleBlocks`), never as one.
    let content := if tps.align == some .left || !tps.slots.isEmpty then inner
      else #[.center inner]
    recordFrameSource ctx pos blocks.size
    blocks := blocks.push (.frame #[] false .golden false content)
  else
    -- The flow classes centre the title block, as `\@maketitle` does.
    modify fun st => { st with titleDone := true }
    let tps := (ctx.styles.find? "titlepage").getD {}
    let content := if tps.align == some .left then inner else #[.center inner]
    blocks := blocks ++ content
  return blocks

/-- A frame, flattened into the lone frame it holds when neither carries a
title, so that one frame never contains another. -/
private def flattenFrame (title : Array Inline) (standout : Bool)
    (valign : Ir.VAlign) (breakable : Bool) (inner : Array Block) : Block :=
  match inner with
  | #[.frame it _ ival ibrk ibody] =>
    if title.isEmpty && it.isEmpty then
      .frame title standout ival (breakable || ibrk) ibody
    else .frame title standout valign breakable inner
  | _ => .frame title standout valign breakable inner

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

/-- Whether the raws hold paragraph content beyond spaces, paragraph breaks
and empty groups. -/
private def pendingParaInput : List Raw → Bool
  | [] => false
  | .space :: rest | .par _ :: rest => pendingParaInput rest
  | .group body _ :: rest => pendingParaInput body.toList || pendingParaInput rest
  | _ :: _ => true
termination_by raws => rawWeightList raws
decreasing_by all_goals (simp only [rawWeightList, rawWeight]; omega)

/-- Whether a declaration at a paragraph's top level stays in force after
the paragraph, since a paragraph end closes no group (TeXbook ch. 24). -/
private def carriesPar (ctx : Ctx) (n : String) : Bool :=
  n != "ttfamily" &&
    ((Marker.value? .ink n).isSome || (Marker.value? .fontSize n).isSome || (declStyleOf n).isSome
      || (ctx.palette.resolve n).isSome)

/-- `readFontSizeStyle` without its diagnostics. -/
private def fontSizeStyle? (ctx : Ctx) (spec : String) : Option Style :=
  (Marker.fontSizeParts spec).bind fun (sizeSrc, leadingSrc) =>
    match fontDim ctx sizeSrc, fontDim ctx leadingSrc with
    | .ok size, .ok leading => some (.fontSize size leading)
    | _, _ => none

/-- Applies one carried declaration as its reading between blocks does,
silently, over `pal`, the palette in force. -/
private def carryOne (ctx : Ctx) (pal : Palette) (cur : Array Raw) (i : Nat) (n : String)
    (blocks : Array Block) : EM (Array Block × Palette) := do
  let marker := Marker.read? n
  if let some (.ink, source) := marker then
    unless source == Compat.normalInkSource do noteColorReads source
    let ink := if source == Compat.normalInkSource then
        some (pal.restore ctx.basePalette (.role .ink))
      else match pal.resolveSource none source with
        | .ok (some c) => some (pal.declare (.role .ink) c)
        | _ => none
    match ink with
    | some p =>
      modify (setInk p)
      return (blocks.push (.setPalette p), p)
    | none => return (blocks, pal)
  else if let some (.lang, tag) := marker then
    modify (flowLangUpdate ctx tag)
    return (blocks, pal)
  else
    let decl := match marker with
      | some (.fontSize, spec) => (fontSizeStyle? ctx spec).map Ir.Decl.style
      | _ => namedScopeDecl ctx n cur i
    if let some (.color _ _) := decl then noteColorReads n
    match decl with
    | some d =>
      modify fun st => { st with scope := { st.scope with
        blockDecls := pushDecl st.scope.blockDecls d } }
    | none => pure ()
    return (blocks, pal)

/-- Carries a paragraph's top-level declarations past its end, in order, with
the palette they leave in force. -/
private def carryDeclsGo (ctx : Ctx) (cur : Array Raw) (i : Nat) :
    List Raw → Array Block × Palette → EM (Array Block × Palette)
  | [], acc => pure acc
  | .ctrl n _ :: rest, (blocks, pal) =>
    if carriesPar ctx n then do
      let acc ← carryOne ctx pal cur i n blocks
      carryDeclsGo ctx cur (i + 1) rest acc
    else carryDeclsGo ctx cur (i + 1) rest (blocks, pal)
  | _ :: rest, acc => carryDeclsGo ctx cur (i + 1) rest acc

private def carryDecls (ctx : Ctx) (cur : Array Raw) (blocks : Array Block) :
    EM (Array Block × Palette) :=
  carryDeclsGo ctx cur 0 cur.toList (blocks, ctx.palette)

private def quietRaw (ctx : Ctx) : Raw → Bool
  | .ctrl n _ => !carriesPar ctx n
  | _ => true

private theorem carryDeclsGo_quiet (ctx : Ctx) (cur : Array Raw) :
    ∀ (i : Nat) (rs : List Raw) (blocks : Array Block) (pal : Palette),
      rs.all (quietRaw ctx) = true → carryDeclsGo ctx cur i rs (blocks, pal) = pure (blocks, pal)
  | _, [], _, _, _ => rfl
  | i, r :: rest, blocks, pal, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases r with
    | ctrl n p =>
      have hq : carriesPar ctx n = false := by simpa [quietRaw] using h.1
      simp only [carryDeclsGo, hq, Bool.false_eq_true, ↓reduceIte]
      exact carryDeclsGo_quiet ctx cur (i + 1) rest blocks pal h.2
    | _ =>
      simp only [carryDeclsGo]
      exact carryDeclsGo_quiet ctx cur (i + 1) rest blocks pal h.2

private theorem carryDecls_quiet (ctx : Ctx) (cur : Array Raw)
    (h : cur.toList.all (quietRaw ctx) = true) :
    carryDecls ctx cur = fun blocks => pure (blocks, ctx.palette) :=
  funext fun blocks => carryDeclsGo_quiet ctx cur 0 cur.toList blocks ctx.palette h

private theorem carriesPar_recovers (ctx : Ctx) (name : String)
    (hn : recoversInlineName ctx name = true) : carriesPar ctx name = false := by
  simp only [recoversInlineName, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at hn
  simp only [carriesPar, hn, Option.isSome_none, Bool.or_self, Bool.and_false]

private theorem carryDecls_empty (ctx : Ctx) (blocks : Array Block) :
    carryDecls ctx #[] blocks = pure (blocks, ctx.palette) := rfl

/-- Flushes the open paragraph, carries its declarations past its end, and
settles the owners that began inside it. -/
private def flushPara (ctx : Ctx) (blocks : Array Block) (cur : Array Raw) :
    EM (MCtx ctx × Array Block) := do
  let paraCtx := { ctx with macroRoles := { ctx.macroRoles with
    blocks := ctx.macroRoles.blocks.filter (!·.pendingPara) } }
  let p ← if cur.isEmpty then pure none else mkPara paraCtx cur
  let blocks := match p with
    | some p => blocks.push p
    | none => blocks
  let (blocks, pal) ← carryDecls ctx cur blocks
  let roles := ctx.macroRoles.blocks.map fun run =>
    if run.pendingPara then { run with start := blocks.size, pendingPara := false } else run
  return (⟨{ ctx with palette := pal, macroRoles := { ctx.macroRoles with blocks := roles } },
    rfl, rfl, rfl, rfl⟩, blocks)

/-- Drops the frame sources recorded from the earliest completed role that
`desired` does not continue. -/
private def closeBlockFrameSources (active : Array MacroRun)
    (desired : List MacroOrigin) (size : Nat) : EM Unit := do
  let keep := commonOrigins (active.toList.map (·.origin)) desired
  let retained := (active.toList.drop keep).foldl (init := size) fun retained run =>
    if run.pendingPara then retained else min retained run.start
  if retained < size then keepFrameSourcePrefix retained

private def closeBlockMacros (ctx : Ctx) (blocks : Array Block) :
    EM (MCtx ctx × Array Block) := do
  closeBlockFrameSources ctx.macroRoles.blocks [] blocks.size
  let (_, blocks) := moveMacroRuns Block.role ctx.macroRoles.blocks [] blocks
  return (⟨{ ctx with macroRoles := { ctx.macroRoles with blocks := #[] } },
    rfl, rfl, rfl, rfl⟩, blocks)

/-- Whether the overlay at `raws[i]` is open: its spec resolves and no
content group follows it. -/
private def openBlockOverlay (ctx : Ctx) (n : String) (raws : Array Raw) (i : Nat) : Bool :=
  if !overlayCtrls.contains (Compat.overlayName n) || (lookupUser ctx n).isSome then false
  else
    let j := skipSpaces raws (i + 1)
    match raws[j]?.bind specWord? with
    | none => false
    | some spec =>
      (Ir.overlayRange spec).isSome &&
        !(raws[skipSpaces raws (j + 1)]? matches some (.group ..))

/-- Closes completed macro ownership before an open overlay, which consumes
the stream's tail. -/
private def blockControlContext (ctx : Ctx) (n : String) (raws : Array Raw)
    (i : Nat) (blocks : Array Block) : EM (MCtx ctx × Array Block) :=
  if openBlockOverlay ctx n raws i then closeBlockMacros ctx blocks
  else pure (⟨ctx, rfl, rfl, rfl, rfl⟩, blocks)

/-- Each expansion origin at `raws[i]` with whether its span is block
content, classified once per origin. -/
private def blockMacroKinds (roles : MacroRoles) (raws : Array Raw) (i : Nat) :
    List (MacroOrigin × Bool) :=
  match raws[i]? with
  | none => []
  | some raw => match raw.origins? with
    | none => roles.blockKinds
    | some origins =>
      (relativeOrigins roles.inherited origins).map fun origin =>
        let isBlock := match roles.blockKinds.lookup origin with
          | some isBlock => isBlock
          | none =>
            let span := (raws.extract i raws.size).toList.takeWhile fun raw =>
              raw.origins?.all (·.contains origin)
            bodyIsBlock span.toArray
        (origin, isBlock)

/-- Refreshes flow state and block macro ownership at `raws[i]`, flushing the
pending paragraph at the end of input. -/
private def blockMacroStep (ctx : Ctx) (st : ESt) (gen : Nat)
    (raws : Array Raw) (i : Nat) (blocks : Array Block) (cur : Array Raw) :
    EM (MCtx ctx × Array Block × Array Raw) := do
  let ⟨fresh, hf⟩ := flowMCtx ctx st gen
  let kinds := blockMacroKinds fresh.macroRoles raws i
  let desired := kinds.filterMap fun (origin, isBlock) => if isBlock then some origin else none
  let done := i ≥ raws.size
  let (⟨ready, hm⟩, blocks) ← if done then flushPara fresh blocks cur
    else pure (⟨fresh, rfl, rfl, rfl, rfl⟩, blocks)
  let cur := if done then #[] else cur
  closeBlockFrameSources ready.macroRoles.blocks desired blocks.size
  let (active, blocks) := moveMacroRuns Block.role ready.macroRoles.blocks desired blocks
    (pendingParaInput cur.toList)
  let ctx' := { ready with macroRoles := { ready.macroRoles with
    blocks := active, blockKinds := kinds } }
  return (⟨ctx', hm.1.trans hf.1, hm.2.1.trans hf.2.1,
    hm.2.2.1.trans hf.2.2.1, hm.2.2.2.trans hf.2.2.2⟩, blocks, cur)

/-- Declarations that change the flowing palette or spacing tokens. -/
private def flowStyleCtrl (n : String) : Bool :=
  (Marker.value? .ink n).isSome || isPageGround n || n == BeamerColor.marker ||
    n == BeamerColor.starMarker || n == "palette" || n == "tokens"

/-- Reads a flow declaration after its command, publishing it to the state and
the IR. -/
private def flowStyleArm (ctx : Ctx) (n : String) (raws : Array Raw)
    (start : Nat) (hstart : start ≤ raws.size) (pos : Pos) (blocks : Array Block) (gen : Nat) :
    EM (MCtx ctx × { j : Nat // start ≤ j } × Array Block × Nat) := do
  if n == "tokens" then
    -- `\setlength` mid-document rewrites through this same door.
    let j := skipSpaces raws start
    have hj := skipSpaces_ge raws start
    match raws[j]? with
    | some (.group body _) =>
      -- A list margin stays fixed as the preamble's are, one value per backend.
      let tk := ctx.preamble.fixLengths Ir.leftMarginNamed
        (← applyTokens ctx ctx.tokens (rawSrc body) pos (engine := ctx.engineTokens))
      modify fun st => { st with flowTokens := some tk, flowGen := st.flowGen + 1 }
      return (⟨{ ctx with tokens := tk }, rfl, rfl, rfl, rfl⟩,
        ⟨j + 1, by omega⟩, blocks.push (.setTokens tk), (← get).flowGen)
    | _ =>
      diag ctx .E0304 "'\\tokens' needs a {...} block" pos
      return (⟨ctx, rfl, rfl, rfl, rfl⟩, ⟨start, Nat.le_refl _⟩, blocks, gen)
  let ⟨(pal?, j), hj⟩ : { t : Option Palette × Nat // start ≤ t.2 } ←
    if let some source := Marker.value? .ink n then do
      -- xcolor's `\color` colours the rest of its group (manual §2.6.4).
      pure ⟨(← inkFlowDecl ctx source pos, start), Nat.le_refl _⟩
    else if isPageGround n then do
      pure ⟨(← pageGround ctx n pos, start), Nat.le_refl _⟩
    else if n == BeamerColor.marker || n == BeamerColor.starMarker then
      beamerColorArm ctx raws start (n == BeamerColor.starMarker) pos
    else do
      -- The native palette door, also used by `\colorlet`.
      let j0 := skipSpaces raws start
      have hj0 := skipSpaces_ge raws start
      let ⟨((decorative, seeds), skipBlock, jf), hjf⟩ :
          { t : (Bool × Bool) × Bool × Nat // start ≤ t.2.2 } ←
        if let some (.sym '[' _) := raws[j0]? then do
          let ⟨(opt, k), hk⟩ : { t : Array Raw × Nat // start ≤ t.2 } :=
            match hc : closeBracketFrom raws (j0 + 1) with
            | some c => ⟨(raws.extract (j0 + 1) c, c + 1), by
                have := closeBracketFrom_ge hc; omega⟩
            | none => ⟨(raws.extract (j0 + 1) raws.size, raws.size), by omega⟩
          let (decorative, seeds, skipBlock) ← parsePaletteOpts ctx (rawSrc opt) pos
          pure ⟨((decorative, seeds), skipBlock, skipSpaces raws k), by
            have := skipSpaces_ge raws k
            show start ≤ skipSpaces raws k
            omega⟩
        else pure ⟨((false, false), false, j0), hj0⟩
      have hjf2 : start ≤ jf := hjf
      match raws[jf]? with
      | some (.group body _) =>
        let pal? ← if skipBlock then pure none else
          some <$> applyPalette ctx ctx.palette (rawSrc body) pos (decorative := decorative)
            (seeds := seeds) (depth := ctx.groundDepth) (inBody := true)
        pure ⟨(pal?, jf + 1), by omega⟩
      | _ =>
        diag ctx .E0304 "'\\palette' needs a {...} block" pos
        pure ⟨(none, start), Nat.le_refl _⟩
  -- Ink and Beamer readers publish their own palette.
  if n == "palette" || isPageGround n then
    if let some pal := pal? then
      modify fun st => { st with scope := { st.scope with palette := { st.scope.palette with current := some pal } },
                                 flowGen := st.flowGen + 1 }
  let currentGen := (← get).flowGen
  let nextGen := if n == "palette" && pal?.isNone then gen else currentGen
  let blocks := match pal? with
    | some pal => blocks.push (.setPalette pal)
    | none => blocks
  return (⟨{ ctx with palette := pal?.getD ctx.palette }, rfl, rfl, rfl, rfl⟩,
    ⟨j, hj⟩, blocks, nextGen)

private def parFollows (raws : Array Raw) (i : Nat) : Bool :=
  match (raws.extract i raws.size).toList.dropWhile (· matches .space) with
  | [] => false
  | r :: _ => r matches .par _

private def parPrecedes (raws : Array Raw) (i : Nat) : Bool := Id.run do
  let mut j := i
  for _ in [0:i] do
    j := j - 1
    match raws[j]? with
    | some .space => pure ()
    | some (.par _) | some (.ctrl "par" _) => return true
    | _ => return false
  return false

/-- Whether an environment's `\@endpe` reaches a display at `i`, so TeX sets
no empty line before it (ltlists.dtx `\@doendpe`). -/
private def endPeAt (raws : Array Raw) (i : Nat) (inPar : Bool) (flushed : Array Block) : Bool :=
  !inPar && Ir.lastLeavesEndPe flushed && !parPrecedes raws i

/-- The paragraph state an overlay carrier at `raws[i]` opens in: inside the
paragraph its text ran on from, right after an environment end that left
`\@endpe`, and whether its content opens on a paragraph break. -/
private def carrierOpening (raws : Array Raw) (i : Nat) (blocks : Array Block)
    (body : Array Raw) : Bool × Bool × Bool :=
  let opensOnText := match body.toList.dropWhile (· matches .space) with
    | .par _ :: _ => false
    | _ => true
  let ranOn := match (raws.extract 0 i).toList.reverse.dropWhile (· matches .space) with
    | [] | .par _ :: _ => false
    | _ :: _ => true
  let inPar := opensOnText && ranOn && Ir.flushedText (blocks.size - 1) blocks
  (inPar, endPeAt raws i inPar blocks, !opensOnText)

/-- A braced overlay's carrier, stood in its paragraph and before the break
after its group at `raws[jg]`. -/
private def carrierInGroup (raws : Array Raw) (i jg : Nat) (blocks : Array Block)
    (body : Array Raw) (inner : Array Block) : Array Block :=
  let (inPar, endPe, broken) := carrierOpening raws i blocks body
  Ir.carrierDisplays inPar endPe (parFollows raws (jg + 1)) broken inner

/-- An open overlay's carrier, the rest of the scope from `raws[jg]` on,
stood in its paragraph. -/
private def carrierToEnd (raws : Array Raw) (i jg : Nat) (blocks : Array Block)
    (inner : Array Block) : Array Block :=
  let (inPar, endPe, broken) := carrierOpening raws i blocks (raws.extract jg raws.size)
  Ir.carrierDisplays inPar endPe false broken inner

/-- An alternation's two groups, each stood in the paragraph the
alternation opens in and before the break after its second group. -/
private def altCarriers (raws : Array Raw) (i j3 : Nat) (blocks : Array Block)
    (spec : Ir.OverlaySpec) (ga gb : Array Raw) (ia ib : Array Block) : Block :=
  let after := parFollows raws (j3 + 1)
  let (pa, ea, ba) := carrierOpening raws i blocks ga
  let (pb, eb, bb) := carrierOpening raws i blocks gb
  .alternate spec (Ir.carrierDisplays pa ea after ba ia) (Ir.carrierDisplays pb eb after bb ib)

/-- `\pause`'s carrier: the rest of the scope from `raws[i]` on, revealed at
step `n` and stood in its paragraph. -/
private def pauseCarrier (raws : Array Raw) (i : Nat) (blocks : Array Block) (n : Nat)
    (inner : Array Block) : Array Block :=
  if inner.isEmpty then blocks else
  let (inPar, endPe, broken) := carrierOpening raws i blocks (raws.extract (i + 1) raws.size)
  blocks.push (.step n none (Ir.carrierDisplays inPar endPe false broken inner))

/-- A display formula met between words: the paragraph flushed, and the
display marked with where it stands in its paragraph. -/
private def displayAtBlock (ctx : Ctx) (body : Array Raw) (pos : Pos) (blocks : Array Block)
    (cur : Array Raw) (raws : Array Raw) (i : Nat) : EM (MCtx ctx × Array Block) := do
  let k := blocks.size
  let (next, flushed) ← flushPara ctx blocks cur
  let out ← displayMathArm next.val false body pos flushed
  let inPar := Ir.flushedText k flushed
  return (next, Ir.markDisplay inPar (parFollows raws (i + 1)) (endPeAt raws i inPar flushed)
    flushed.size out)

-- Sealed so the knot's equations never unfold what its arms call.
seal takeArgs mkPara finishPara flushPara stripMathMeta
seal blockMacroStep pauseCarrier carrierInGroup carrierToEnd altCarriers
seal closeBlockMacros blockControlContext
seal splicedFrameScope setFrameSourceBase recordFrameSource keepFrameSourcePrefix
seal declAlignOf
seal flowStyleCtrl flowStyleArm
seal elabMathInline elabMathEnv applyPalette parsePaletteOpts applyTokens parseColSpec
seal titleBlocks
seal skipOptArg takeTitleDecl
seal sectionNumber columnWidth cmidRange trimRawEdges
seal recordLabel refuseRedef dropEnvArgs skipReservedArgs takeDefine
/-- Enters appendix.sty's `{appendices}` scope when `b`, returning the section
counters and mark it saved (`\@resets@pp`). -/
private def enterAppendicesIf (b : Bool) : EM (Option ((Nat × Nat × Nat) × Bool)) := do
  if !b then return none
  let st ← get
  modify fun st => { st with ctr := { st.ctr with inAppendix := true, secNums := (0, 0, 0) } }
  return some (st.ctr.secNums, st.ctr.inAppendix)

/-- Leaves the `{appendices}` scope, restoring what `enterAppendicesIf` saved
(`\@pprestoresec`). -/
private def leaveAppendices (saved : Option ((Nat × Nat × Nat) × Bool)) : EM Unit :=
  match saved with
  | none => pure ()
  | some s =>
    modify fun st => { st with ctr := { st.ctr with inAppendix := s.2, secNums := s.1 } }

/-- The node a block-sequence wrapper environment ships: `{abstract}`'s titled
block, `{appendices}`'s splice, else a quotation. -/
private def wrapScopedEnv (n : String) (blocks inner : Array Block) : Array Block :=
  if n == "abstract" then blocks.push (.abstract inner)
  else if n == "appendices" then blocks ++ inner
  else blocks.push (.quote inner)

private theorem wrapScopedEnv_text (n : String) :
    Ir.Conserves Ir.blocksText (wrapScopedEnv n #[]) := fun inner => by
  unfold wrapScopedEnv
  split
  · rfl
  · split
    · simp
    · rfl

private def thmOf? (thm : ThmDecls) (n : String) : Option ThmDef :=
  thm.defs.find? (·.env == n)

/-- Whether `n` opens a theorem-like scope: a declared theorem, or amsthm's
`proof` once amsthm is loaded. -/
private def thmEnv (thm : ThmDecls) (n : String) : Bool :=
  (thmOf? thm n).isSome || (n == "proof" && thm.ams)

/-- `\labelsep` (article.cls, .5 em) as an en space, which also stands for
amsthm's `\thm@headsep`. -/
private def labelSep : String := "\u2002"

/-- amsthm's `\@addpunct{.}`: a period after a head not already ending in
punctuation. -/
private def addPunct (head : Array Inline) : Array Inline :=
  let t := (Ir.plainText head).trimAscii.toString
  if [".", "?", "!", ":", ";", ","].any (t.endsWith ·) then #[] else #[.text "."]

/-- A theorem-like environment's head with its separator, as the kernel's
`\@begintheorem` or amsthm's `\thmhead@plain` sets it. -/
private def thmHead (style : ThmStyle) (name : Array Inline) (num : Option String)
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

/-- A theorem-like scope's state at its `\begin`, read again at its `\end`. -/
private structure ThmOpen where
  head : Array Inline
  space : Ir.ThmSpace
  qed : Bool
  qedDef : Option (Array Raw)
  /-- The enclosing proof's `qedPlaced`, restored at the `\end`. -/
  outerPlaced : Bool
  target : Option Ir.RefBinding
  decls : List Ir.Decl
  /-- The enclosing statement's blueprint marks, restored at the `\end`. -/
  outer : Blueprint.Scope

/-- The body of the last `\qedsymbol` redefinition at a proof body's top
level. -/
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

/-- Steps a theorem counter and renders its number, restarting within its
heading counter as ltthm.dtx's `\newtheorem` does. -/
private def stepThmCounter (c : String) : EM String := do
  let st ← get
  let within := (st.ctr.thm.counters.find? (·.1 == c)).bind (·.2)
  let snap := withinSnap st.ctr within
  let v := match st.ctr.thm.nums.find? (·.1 == c) with
    | some (_, s, v) => if s == snap then v + 1 else 1
    | none => 1
  modify fun st => { st with ctr := { st.ctr with thm := { st.ctr.thm with
    nums := Ir.redeclare st.ctr.thm.nums c (snap, v) } } }
  return withinNumber st.ctr within v

/-- Opens a theorem-like scope, returning its state and the index where the
body starts. -/
private def thmOpen (ctx : Ctx) (n : String) (body : Array Raw) (pos : Pos) :
    EM (ThmOpen × Nat) := do
  let (note, k) ← match scanOpeningArg body pos fun _ => true with
    | .took k => pure (some (← elabInlines ctx (bracketInner body 0 k)), k)
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
      let heading := Ir.plainText d.heading
      match num with
      | some nm =>
        modify fun st => { st with
          refTarget := some { kind := none, num := nm, statement := some (heading, some nm) } }
      | none =>
        modify fun st => { st with
          refTarget := st.refTarget.map ({ · with statement := some (heading, none) }) }
      pure (thmHead d.style d.heading num note, d.style == .plain || d.style == .kernel, false,
        d.style.space)
    | none =>
      -- amsthm's proof head: `\itshape #1\@addpunct{.}` over `\proofname`.
      let name ← match note with
        | some nt => pure nt
        | none => definedOr ctx "proofname" pos (pure #[.text ctx.locale.proof])
      pure (#[.styled .italic (name ++ addPunct name), .text labelSep], false, true, .proof)
  if italic then
    modify fun s => { s with scope := { s.scope with blockDecls := st.scope.blockDecls ++ [.style .italic] } }
  -- A proof pushes its QED (amsthm.sty `\pushQED{\qed}`).
  if qed then
    modify fun s => { s with ctr := { s.ctr with thm := { s.ctr.thm with
      proofs := s.ctr.thm.proofs + 1, qedPlaced := false } } }
  modify fun s => { s with blueprint := { inside := true } }
  return ({ head := Ir.wrapDecls st.scope.blockDecls head, space, qed,
            qedDef := if qed then bodyQedDef? body else none,
            outerPlaced := st.ctr.thm.qedPlaced, target := st.refTarget,
            decls := st.scope.blockDecls, outer := st.blueprint }, k)

/-- Appends `q` to the last paragraph before any trailing epoch, or sets it as
a paragraph of its own. -/
private def appendLastPara (inner : Array Block) (q : Array Inline) : Array Block :=
  let tail := (inner.toList.reverse.takeWhile fun b => b matches .setPalette _ | .setTokens _).length
  let k := inner.size - tail
  match k, inner[k - 1]? with
  | j + 1, some (.para c) => inner.set! j (.para (c ++ q))
  | _, _ => inner.push (.para q)

/-- Closes a theorem-like scope: its state restored, its first paragraph
opened with the head, a proof ended with its QED, the whole set as its
trivlist. -/
private def thmClose (ctx : Ctx) (n : String) (o : ThmOpen) (inner : Array Block)
    (pos : Pos) : EM (Array Block) := do
  let marks := (← get).blueprint.marks
  modify fun st => { st with refTarget := o.target, scope := { st.scope with blockDecls := o.decls }
                             blueprint := o.outer }
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
      -- No picture label holds the marker: their reader refuses `\qedhere`.
      let inner := if here then
          Ir.mapBlocks (fun x => if x == .label qedHereKey then set else x) inner
        else inner
      -- `\renewcommand{\qedsymbol}{}` is the manual's way to omit it.
      if placed || mark.isEmpty then pure inner else
      let q : Array Inline := #[.strut {}, .fill, .text "\u2003"] ++ shown
      pure (appendLastPara inner q)
    else pure inner
  -- The web page and its twin set the marks after the QED; the PDF, as the print macros, none.
  let lang := (← get).scope.lang.getD ctx.locale.tag
  let line := Blueprint.line ctx.styles ctx.blueprint o.qed (lang.startsWith "en") marks
  let inner := if line.isEmpty then inner
    else inner.push (.only #["html", "md"] #[.para #[.styled (.size "small") line]])
  return #[.role (Ir.thmSpaceRole o.space) #[.role n inner]]

/-- A markdown disclosure's head: whether `[open]` stands first, and where its
summary's group stands. -/
private def disclosureHead (body : Array Raw) : Bool × Nat :=
  match (body[0]? : Option Raw), (body[1]? : Option Raw), (body[2]? : Option Raw) with
  | some (Raw.sym '[' _), some (Raw.word "open" _), some (Raw.sym ']' _) => (true, 3)
  | _, _, _ => (false, 0)

/-- What a scoped environment carries across its body: a theorem-like opening,
or a disclosure's summary and whether it stands open. -/
private inductive ScopeOpen where
  | thm (o : ThmOpen)
  | disclosure (summary : Array Inline) (expanded : Bool)

private def scopedEnv (thm : ThmDecls) (n : String) : Bool :=
  n == Parse.markdownDisclosureEnv || thmEnv thm n

/-- Opens a scoped environment, returning its state and the index where the
body starts. -/
private def scopeOpen (ctx : Ctx) (n : String) (body : Array Raw) (pos : Pos) :
    EM (ScopeOpen × Nat) := do
  if n == Parse.markdownDisclosureEnv then
    let (expanded, k) := disclosureHead body
    match body[k]? with
    | some (.group t _) => return (.disclosure (← elabInlines ctx t) expanded, k + 1)
    | _ => return (.disclosure #[] expanded, k)
  else
    let (o, k) ← thmOpen ctx n body pos
    return (.thm o, k)

private def scopeClose (ctx : Ctx) (n : String) (o : ScopeOpen) (inner : Array Block)
    (pos : Pos) : EM (Array Block) :=
  match o with
  | .thm o => thmClose ctx n o inner pos
  | .disclosure summary expanded => pure #[.disclosure summary expanded inner]

/-- Each top-level `\item`'s `[...]` label run, past an overlay spec, in item
order. -/
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

/-- A description list's items with their labels run in, bold and followed by
`\labelsep`, as latex.ltx's `\descriptionlabel` sets them. -/
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

/-- Applies each item's overlay selector to the whole item, label included, as
beamer's `beamer@parseitem` does. -/
private def coverItems (ctx : Ctx) (steps : Array (Option OverlaySpec))
    (pauses : Array Nat) (items : Array (Array Block)) : Array (Array Block) :=
  items.mapIdx fun i inner =>
    let spec := (steps[i]?).getD none
    let p := (pauses[i]?).getD 0
    match spec with
    | some _ => selectedCover Block.onSteps spec inner
    | none => if p > 0 then #[.step (ctx.stepBase + p + 1) none inner] else inner

/-- A `\bibitem`'s text: paragraph ends as spaces, edge spaces dropped. -/
private def entryRaws (raws : Array Raw) : Array Raw :=
  let rs := raws.map fun r => if r matches .par _ then Raw.space else r
  let a := (rs.findIdx? (· != Raw.space)).getD rs.size
  let b := rs.size - ((rs.reverse.findIdx? (· != Raw.space)).getD rs.size)
  rs.extract a b

/-- `thebibliography` (classes.dtx): an unnumbered References section over its
`\bibitem` entries in source order. -/
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

seal thmOf? thmEnv thmOpen thmClose descItems coverItems ownBibList
seal enterAppendicesIf leaveAppendices wrapScopedEnv
seal secFmtDefine? secFmtOfBody applySecFmt applyCounter counterCtrl counterArm
seal theCounterLevel?
seal declBlockOf isDeclBlock enterBlockDecl leaveBlockDecl declScopeWrap
seal withBlockDecls wrapDeclAlign
seal bodyIsBlock bodyIsBlockList bodyIsBlockOne overlayTakesBlocks
seal renderedBuiltins structuralNames
seal declCtrl runningCtrl titleCtrls overlayCtrls overlaySpecFor blockEnvs reservedEnv
seal displayMathEnvs alignEnvs isMathEnv sectionLevel specWord?
seal lookupUser lookupUserEnv isArgument isCenteringRaw isParRaw splitAtPars sizeParScope
seal isColumnStray
seal parFollows parPrecedes endPeAt displayAtBlock

/-- One parsed pseudocode line, still raw. -/
private structure AlgSeg where
  depth : Nat
  kind : Ir.AlgKind
  content : Array Raw
  comment : Option (Array Raw)

/-- The pseudocode walk's work items: a source raw, or the marker a block form
leaves: `close` ends a body, `mid` is an `\eIf` else, `dedent` closes a
`\uIf`. -/
private inductive AlgTok where
  | raw (r : Raw)
  | close (o : Ir.AlgOpen) (cond : Array Raw)
  | mid (o : Ir.AlgOpen)
  | dedent

/-- algorithm2e's `{cond}{body}` block openers, with their kind and whether
they print an end line. -/
private def algA2eBlocks : List (String × Ir.AlgOpen × Bool) :=
  [("For", (.forLoop, true)), ("ForEach", (.forEach, true)),
   ("ForAll", (.forEach, true)), ("While", (.whileLoop, true)),
   ("If", (.ifThen, true)), ("uIf", (.ifThen, false)),
   ("ElseIf", (.elseIf, true)), ("uElseIf", (.elseIf, false))]

/-- algorithm2e's io-line commands (`\SetKwInput` defaults). -/
private def algA2eIo : List (String × Ir.AlgIo) :=
  [("KwIn", .input), ("KwOut", .output), ("KwData", .data),
   ("KwResult", .result)]

/-- The io line a control at `site` opens: the document's `\SetKwInput` or `\SetKwInOut` keyword
under its declared word, else algorithm2e's own unless the document defines the name another way. -/
private def algIoOf (kws : Array (String × AlgKwDef)) (acx : Bool) (name : String) (site : Span) :
    Option Ir.AlgIo :=
  match ((kws.find? (·.1 == name)).map (·.2) : Option AlgKwDef) with
  | some (.io label) => some (.named label (some site))
  | some _ => none
  | none => if acx then none else algA2eIo.lookup name

/-- algorithm2e display settings the engine does not model, each with the
group count it consumes. -/
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

/-- algorithm2e constructs outside the modeled subset, with their group
counts; their groups' contents are kept as plain lines. -/
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

/-- algorithmicx's end commands, each naming the opener it closes. -/
private def algAcxEnds : List (String × Ir.AlgOpen) :=
  [("EndFor", .forLoop), ("EndWhile", .whileLoop), ("EndIf", .ifThen),
   ("EndFunction", .function), ("EndProcedure", .procedure)]

/-- algorithmicx constructs outside the modeled subset; none carries a
content group. -/
private def algAcxRefused : List String := ["Loop", "EndLoop"]

/-- Rewrites document-defined algorithm keywords in content raws to the
styled text algorithm2e prints. -/
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

/-- Flushes the accumulated line, skipping an empty statement; a
non-statement kind always emits. -/
private def algFlush (segs : Array AlgSeg) (depth : Nat) (kind : Ir.AlgKind)
    (cur : Array Raw) (comment : Option (Array Raw)) : Array AlgSeg :=
  if (kind matches Ir.AlgKind.statement) && cur.all isSpaceOrPar
      && comment.isNone then segs
  else segs.push { depth := depth
                   kind := kind
                   content := trimRawEdges cur
                   comment := comment }

/-- Pops the next `{...}` group off the walk's stack, skipping spaces. -/
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

/-- Pops the next undelimited argument off the walk's stack as TeX reads one, skipping spaces: a
`{...}` group, or one token, a word's first character leaving the rest. -/
private def algPopArg (stack : Array AlgTok) : Option (Array Raw × Pos) × Array AlgTok := Id.run do
  let mut stack := stack
  for _ in [0:stack.size + 1] do
    match stack.back? with
    | some (.raw .space) => stack := stack.pop
    | some (.raw (.par _)) => stack := stack.pop
    | some (.raw (.group g gp)) => return (some (g, gp), stack.pop)
    | some (.raw (.word w wp)) =>
      match w.toList with
      | c :: rest =>
        let rest' := if rest.isEmpty then stack.pop
          else stack.pop.push (.raw (.word (String.ofList rest) wp))
        return (some (#[.word (String.singleton c) wp], wp), rest')
      | [] => stack := stack.pop
    | some (.raw (.ctrl n cp)) => return (some (#[.ctrl n cp], cp), stack.pop)
    | some (.raw (.sym c sp)) => return (some (#[.sym c sp], sp), stack.pop)
    | _ => return (none, stack)
  return (none, stack)

/-- An algorithm's lines with its numbering and semicolon flags, from one
bounded pass over a work stack. -/
private def algorithmLines (ctx : Ctx) (acx : Bool) (body : Array Raw)
    (pos : Pos) : EM (Array Ir.AlgLine × Bool × Bool) := do
  let mut kws : Array (String × AlgKwDef) := (← get).alg.kws
  -- algorithm2e.sty's own `\SetKw{KwTo}{to}`, unless the document's stands.
  unless kws.any (·.1 == "KwTo") do kws := kws.push ("KwTo", .word #[.word "to" pos])
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
        pure ()
      | .raw (.ctrl name p) =>
        let site := ctx.sourceSpan p
        if name == "SetKw" || name == "SetKwInOut" || name == "SetKwInput"
            || name == "SetKwFunction" || name == "SetKwData" then
          let (g1, st1) := algPopGroup stack
          let (g2, st2) := algPopGroup st1
          stack := st2
          match g1, g2 with
          | some (nm, _), some (val, _) =>
            let key := (Parse.rawSrc nm).trimAscii.toString
            -- The lines before a redefinition keep the keywords they were written under.
            segs := segs.map fun s => { s with
              content := algSubstList kws #[] s.content.toList
              comment := s.comment.map fun c => algSubstList kws #[] c.toList }
            cur := algSubstList kws #[] cur.toList
            curComment := curComment.map fun c => algSubstList kws #[] c.toList
            if name == "SetKw" then kws := Ir.redeclare kws key (.word val)
            else if name == "SetKwFunction" then
              kws := Ir.redeclare kws key (.func val)
              -- algorithm2e defines a function keyword with \gdef, so it holds past its algorithm.
              modify fun st => { st with alg := { st.alg with
                kws := Ir.redeclare st.alg.kws key (.func val) } }
            else if name == "SetKwData" then kws := Ir.redeclare kws key (.data val)
            else kws := Ir.redeclare kws key (.io (Ir.plainText (← elabInlines ctx val)))
          | _, _ =>
            diag ctx .E0304 s!"'\\{name}' needs its \{name}\{text} groups" p
        else if let some k := algIoOf kws acx name site then
          let (g1, st1) := algPopArg stack
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
        else if kws.any (·.1 == name) then
          cur := cur.push (Raw.ctrl name p)
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
        else if name == "Return" || name == "KwRet" then
          segs := algFlush segs depth curKind cur curComment
          cur := #[]; curComment := none
          curKind := .ret
        else if !acx && (name == "tcc" || name == "tcp") then
          if let some (.raw (.word "*" _)) := stack.back? then
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

/-- An `{algorithmic}` `[n]` as both packages compare it with the line count: digits alone, or alone
in one group, written as the count is. -/
private def algStep? (inner : Array Raw) : Option Nat :=
  let value := match inner with
    | #[.group g _] => g
    | _ => inner
  match value with
  | #[.word w _] => if w == "0" || (w.all Char.isDigit && !w.startsWith "0") then w.toNat? else none
  | _ => none

/-- An `{algorithmic}` body in the flat dialect: its lines, whether its own numbering or its `[n]`
numbers them (every line for 1, none for 0 or a value no line count equals, as the packages compare
the two), and whether it ends statements with semicolons. -/
private def algorithmicBody (ctx : Ctx) (body : Array Raw) (pos : Pos) :
    EM (Array Ir.AlgLine × Bool × Bool) := do
  let mut k := 0
  let mut numbered := false
  match scanOpeningArg body pos fun _ => true with
  | .took k' =>
    match algStep? (bracketInner body 0 k') with
    | some 0 | none => pure ()
    | some 1 => numbered := true
    | some _ =>
      numbered := true
      warnOnce ctx "algorithmic:step" .N0102
        "a line-number step above 1 is not modelled; every line is numbered" pos
        (detail := some s!"[{bracketSrc body 0 k'}]")
    k := k'
  | .unclosed bpos => warnUnclosed ctx "'\\begin{algorithmic}'" bpos
  | .content => pure ()
  let (lines, n2, semis) ← algorithmLines ctx true (body.extract k body.size) pos
  return (lines, numbered || n2, semis)

/-- A bare `{algorithmic}` environment: an uncaptioned algorithm in the flat
dialect, `[n]` numbering its lines. -/
private def algorithmicArm (ctx : Ctx) (body : Array Raw) (pos : Pos)
    (blocks : Array Block) : EM (Array Block) := do
  let (lines, numbered, semis) ← algorithmicBody ctx body pos
  return blocks.push (.algorithm numbered semis lines)

/-- Whether a float's `[...]` holds only LaTeX's placement letters, an empty one LaTeX's empty spec. -/
private def isPlacement (written : String) : Bool :=
  written.all fun c =>
    c.isWhitespace || c == 'h' || c == 't' || c == 'b' || c == 'p' || c == 'H' || c == '!'

/-- A float's opening `[placement]`, named as ignored: the index past it. -/
private def floatPlacement (ctx : Ctx) (n : String) (body : Array Raw) (pos : Pos) : EM Nat := do
  match scanOpeningArg body pos isPlacement with
  | .took k =>
    warnOnce ctx ("float:placement:" ++ n) .N0102
      s!"'\{{n}}' [placement] is ignored: a single-pass engine has \
nowhere for a float to float" pos
    return k
  | .unclosed bpos =>
    warnUnclosed ctx s!"'\\begin\{{n}}'" bpos
    return 0
  | .content => return 0

/-- An `{algorithm}` or `{algorithm2e}` float, its caption set above the lines
and its placement ignored. -/
private def algorithmArm (ctx : Ctx) (n : String) (body : Array Raw)
    (pos : Pos) (blocks : Array Block) : EM (Array Block) := do
  let k ← floatPlacement ctx n body pos
  let mut caption : Array Inline := #[]
  let mut anchors : Array Inline := #[]
  let mut rest : Array Raw := #[]
  let mut acxBody : Option (Array Raw × Pos) := none
  let mut j := k
  for _ in [k:body.size] do
    if h : j < body.size then
      match body[j] with
      | .ctrl "label" lpos =>
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
    | some (abody, apos) => algorithmicBody ctx abody apos
    | none => algorithmLines ctx false rest pos
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


seal scanBracketArg

/-- Whether a proposed linked row's `\href` and `\hyperlink` keep their
native meaning: no visible definition or parameter owns them. -/
private def nativeLinkedRow (ctx : Ctx) (body : Array Raw) : Bool :=
  match (body[0]? : Option Raw) with
  | some (.group source _) =>
    !source.any fun
      | .ctrl n _ =>
        (n == "href" || n == "hyperlink") &&
          ((lookupUser ctx n).isSome || ctx.args.any (·.1 == n))
      | _ => false
  | _ => false

private theorem nativeLinkedRow_gated {ctx : Ctx} {body source : Array Raw} {pos : Pos}
    (hg : body[0]? = some (.group source pos)) (h : nativeLinkedRow ctx body = true)
    {name : String} {p : Pos} (hm : Raw.ctrl name p ∈ source)
    (hn : name = "href" ∨ name = "hyperlink") :
    lookupUser ctx name = none ∧ ctx.args.any (·.1 == name) = false := by
  simp only [nativeLinkedRow, hg, Bool.not_eq_true', Array.any_eq_false'] at h
  have hc := h (.ctrl name p) hm
  rcases hn with rfl | rfl <;> simpa using hc

/-- Selects a linked row's native or source alternative. -/
private def linkedRowChoice (body : Array Raw) (native : Bool) :
    { rs : Array Raw // rawWeightList rs.toList ≤ rawWeightList body.toList ∧
      nestedParsList rs.toList ≤ rawParsList body.toList } :=
  match h : (body[if native then 1 else 0]? : Option Raw) with
  | some (.group chosen pos) =>
    have hmem : Raw.group chosen pos ∈ body.toList := by
      obtain ⟨hi, heq⟩ := Array.getElem?_eq_some_iff.mp h
      exact heq ▸ Array.getElem_mem_toList hi
    have hw := measList_mem_le (μ := rawWeight) hmem
    have hp := measList_mem_le (μ := rawPars) hmem
    have hn := nestedParsList_le chosen.toList
    ⟨chosen, by
        simp only [rawWeight, ← rawWeightList_eq] at hw
        omega,
      by
        simp only [rawPars, ← rawParsList_eq] at hp
        exact Nat.le_trans hn hp⟩
  | _ => ⟨#[], by simp [rawWeightList, nestedParsList]⟩

/-- Names a minipage row's conversion to a row of boxes and its ignored
options. -/
private def noteLinkedRow (ctx : Ctx) (body : Array Raw) (pos : Pos) : EM Unit := do
  warnOnce ctx "env:minipage-row" .N0100
    "'\\begin{minipage}…\\end{minipage}\\hfill\\begin{minipage}…' → \
one row of boxes, the fill between them" pos
  if body.size > 2 then
    warnOnce ctx "env:minipage-row-options" .N0102
      "'minipage' [height] and [inner-pos] options are ignored in a row of boxes: each \
box is as tall as its content" pos

private theorem linkedRowChoice_splice {raws : Array Raw} {i : Nat}
    (h : i < raws.size) {body : Array Raw} {pos : Pos}
    (hr : raws[i] = .env Compat.linkedBoxRowMark body pos) (native : Bool) :
    let chosen := (linkedRowChoice body native).val
    sliceWeight (raws.extract 0 i ++ chosen ++ raws.extract (i + 1) raws.size) i
        < sliceWeight raws i ∧
      slicePars (raws.extract 0 i ++ chosen ++ raws.extract (i + 1) raws.size) i
        ≤ slicePars raws i := by
  have hb := (linkedRowChoice body native).property
  constructor
  · simp only [sliceWeight_eq]
    have hs := sliceMeas_splice (μ := rawWeight) h (linkedRowChoice body native).val
    rw [hr] at hs
    simp only [rawWeight, ← rawWeightList_eq] at hs
    omega
  · simp only [slicePars_eq]
    have hs := sliceMeas_splice (μ := nestedPars) h (linkedRowChoice body native).val
    rw [hr] at hs
    simp only [nestedPars, ← nestedParsList_eq] at hs
    omega

/-- A group's blocks followed by the epoch its end restores. -/
@[noinline] private def groupBlocks (base : Palette) (act : EM (Array Block)) :
    EM (Array Block) := do
  let (blocks, epoch) ← texGroup base act
  return blocks ++ epoch

/-- A group inside an open paragraph, whose earlier declarations stand again
after the group ends. -/
@[noinline] private def restoringGroup (ctx : Ctx) (cur : Array Raw) (act : EM (Array Block)) :
    EM (Array Block) := do
  let blocks ← groupBlocks ctx.palette act
  let pal := (← get).scope.palette.current.getD ctx.palette
  return (← carryDeclsGo ctx cur 0 cur.toList (blocks, pal)).1

/-- An environment's blocks, grouped unless it wraps an `\input` file, with
their in-paragraph and display marks. -/
@[noinline] private def envGroup (n : String) (base : Palette) (inPar parEnd afterEnv : Bool)
    (k : Nat) (act : EM (Array Block)) : EM (Array Block) := do
  let (blocks, epoch) ←
    if (Parse.inputEnvFile? n).isSome then (·, #[]) <$> act else texGroup base act
  return Ir.markDisplay inPar parEnd afterEnv k (Ir.markInParagraph inPar k blocks) ++ epoch

seal nativeLinkedRow linkedRowChoice noteLinkedRow
seal texGroup groupBlocks restoringGroup envGroup

/-- Whether control `n` at `raws[i]` opens a block rather than continuing the
paragraph `cur`. -/
private def isBlockStart (ctx' : Ctx) (n : String) (raws : Array Raw) (i : Nat)
    (cur : Array Raw) : Bool :=
  let sourceName := n
  let n := Compat.overlayName n
  n == "par" || n == "block" || n == "centering" || n == "pause"
    || (Ir.raggedSideOf? n).isSome
    || n == "framefoot" || n == "pagebreak" || n == "appendix"
    || (ctx'.slides && (n == "AtBeginSection" || n == "AtBeginSubsection"))
    || n == Compat.frameRestartMark || n == Compat.vspaceAnchorMark
    || (Ir.pageOpeningOfRole? n).isSome
    -- `\prevdepth` is vertical mode's: TeX refuses it mid-paragraph.
    || (n == "nointerlineskip" && cur.isEmpty)
    || n == "bibliography" || n == Parse.markdownBibControl || n == "bibliographystyle"
    || n == Parse.citeSetupMark
    || (n == "note" && cur.isEmpty)
    || isDeclBlock ctx' n raws i cur
    -- Mid-paragraph these markers stay inline: splitting there would move text.
    || (cur.isEmpty &&
      ((Marker.read? n).any (fun (k, _) => k == .ink || k == .lang) || isPageGround n))
    || n == BeamerColor.marker || n == BeamerColor.starMarker
    || ((lookupUser ctx' sourceName).isNone && !(ctx'.args.any (·.1 == sourceName)) &&
      (n == "href" || n == "link" || n == "hyperlink" || n == "hypertarget") &&
        contentWrapperTakesBlocks n raws i)
    || (n != "note" &&
      ((blockHeading? n).isSome
        || declCtrl.contains n || runningCtrl.contains n || n == "define"
        || counterCtrl n
        || (match lookupUser ctx' sourceName with
            | some (_, cmd) => bodyIsBlock cmd.body
            | none =>
              ((overlayCtrls.contains n || n == "alt") &&
                overlayTakesBlocks raws i cur.isEmpty (n == "alt")) ||
              titleCtrls.contains n || n == "maketitle"
                || n == "titlepage" || n == "logo")))

/-- The `\begin{frame}` options the frame model reads; a standout frame is
centred whatever its options say. -/
private structure FrameOpts where
  standout : Bool := false
  breakable : Bool := false
  /-- beamer's `[squeeze]` (beamerbaseframesize.sty): the frame's lists set
  tight. -/
  squeeze : Bool := false
  valign : VAlign := .center
  /-- The alignment options the frame names, in order. -/
  aligns : Array String := #[]
  /-- The index past the last bracket group read. -/
  next : Nat := 0

/-- The frame alignment a deck's class options declare. -/
private def classFrameAlign (opts : List String) : VAlign :=
  opts.foldl (fun v o =>
    if o == "t" || o == "slidestop" then .top
    else if o == "c" || o == "slidescentered" then .center
    else v) .center

/-- Whether every item of a bracket's text names a key `\setkeys{beamerframe}` reads: beamer's own
and metropolis's `standout`. -/
private def frameKeysOnly (src : String) : Bool :=
  (KeyVal.items src).all fun opt => #["allowdisplaybreaks", "allowframebreaks", "b", "c",
    "containsverbatim", "environment", "fragile", "label", "noframenumbering", "plain", "relabel",
    "s", "shrink", "squeeze", "standout", "t", "typeset second"].contains (KeyVal.entry opt).1

private def frameOpts (ctx : Ctx) (body : Array Raw) (pos : Pos) : EM FrameOpts := do
  let mut o : FrameOpts := { valign := ctx.frameAlign }
  for _ in [0:body.size] do
    match (if o.next == 0 then scanOpeningArg body pos frameKeysOnly
      else scanBracketArg body o.next pos) with
    | .took k' =>
      let inner := bracketSrc body o.next k'
      for opt in KeyVal.items inner do
        match KeyVal.entry opt with
        -- premise: fragileNoopChecks — these spellings change no artifact
        | ("fragile", none) | ("fragile", some "true") => pure ()
        | ("standout", none) => o := { o with standout := true }
        | ("allowframebreaks", none) => o := { o with breakable := true }
        | ("squeeze", none) => o := { o with squeeze := true }
        | ("t", none) => o := { o with valign := .top, aligns := o.aligns.push "t" }
        | ("c", none) => o := { o with valign := .center, aligns := o.aligns.push "c" }
        | ("b", none) => o := { o with valign := .bottom, aligns := o.aligns.push "b" }
        | _ =>
          warnOnce ctx ("frame:opt:" ++ opt) .N0102
            s!"frame option '{opt}' is not modelled; ignored" pos
      o := { o with next := k' }
    | .unclosed bpos =>
      warnUnclosed ctx "'\\begin{frame}'" bpos
      break
    | .content => break
  if o.standout then
    for a in o.aligns do
      unless a == "c" do
        warnOnce ctx ("frame:opt:standout:" ++ a) .N0102
          s!"frame option '{a}' does not apply to a standout frame, which is centred; ignored" pos
    return { o with valign := .center }
  return o

/-- A box's `[pos][height][inner-pos]` arguments: its position and the index
past them, the last two named and ignored. -/
private def boxOptsArm (ctx : Ctx) (body : Array Raw) (pos : Pos) (what : String) :
    EM (Ir.BoxPos × Nat) := do
  let mut k := 0
  let mut boxPos : Ir.BoxPos := .top
  for arg in [0:3] do
    match (if arg == 0 then scanOpeningArg body pos fun _ => true
      else scanBracketArg body k pos) with
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

/-- A list option's length, as the native length grammar reads it; `none` where it cannot. -/
private def listOptionLength (ctx : Ctx) (src : String) : Option SymGlue :=
  match Decl.parseValue src ctx.tokens.entries with
  | some (.glue g) => some g
  | some (.dim d) => some { width := Dim.Length.ofSp d }
  | _ =>
    match Decl.parseLengthExpr (ctx.tokens.entries ++ ctx.engineTokens)
        (String.join (src.splitOn "\\")) with
    | .ok g => some g
    | .error _ => none

/-- A list's options and the scopes over it: the index past its options, and the spacing it
declares as enumitem sets it, its scopes in order, its own options last, over what it keeps of the
enclosing list's. -/
private def listOptsArm (ctx : Ctx) (n : String) (body : Array Raw) (pos : Pos) :
    EM (Nat × Ir.ListSet) := do
  let mut own : Ir.ListSet := {}
  let mut bodyFrom := 0
  match scanOpeningArg body pos fun _ => true with
  | .took k' =>
    noteMentions (bracketSrc body 0 k')
    for o in KeyVal.items (bracketSrc body 0 k') do
      let (key, value) := KeyVal.entry o
      if key.startsWith "<" then
        warnOnce ctx ("param:" ++ n ++ ":" ++ key) .W0104
          s!"'\{{n}}' default overlay specification '{key}' is not read; its items show as \
their own specifications say" pos
          (help := "give each item a numbered specification, as \\item<1-> and \\item<2->")
      else if Ir.listSetKeys.contains key then
        match listOptionLength ctx (value.getD "") with
        | some g => own := own.put key (some g)
        | none =>
          warnOnce ctx ("param:" ++ n ++ ":" ++ key) .W0104
            s!"'\{{n}}' option '{key}' has a length this engine cannot read; skipped" pos
            (help := "give a length such as 2pt, 0.5em or a token name")
      else unless key.isEmpty do
        warnOnce ctx ("param:" ++ n ++ ":" ++ key) .W0104
          s!"'\{{n}}' option '{key}' is not honoured per list; the declared list style stands" pos
    bodyFrom := k'
  | .unclosed bpos =>
    warnUnclosed ctx s!"'\\begin\{{n}}'" bpos
  | .content => pure ()
  let nest := ctx.listNest
  let depth := nest.depth + 1
  let scopes := (Ir.listSetScopes n depth (nest.kindDepth n + 1)).foldl (fun (acc : Ir.ListSet) e =>
    acc.over (((ctx.styles.find? e).map (·.list)).getD {})) {}
  return (bodyFrom, (Ir.ListSet.within ctx.lists ctx.page.fontSize depth nest.set).over
    (scopes.over own))

/-- Whether every item of a bracket's text names a key beamer's `beamer@col` family reads. -/
private def columnsKeysOnly (src : String) : Bool :=
  (KeyVal.items src).all fun opt =>
    #["b", "c", "height", "onlytextwidth", "t", "T", "totalwidth"].contains (KeyVal.entry opt).1

/-- The index past `\begin{columns}`'s options, naming each that is not a
position. -/
private def columnsOptsArm (ctx : Ctx) (body : Array Raw) (pos : Pos) : EM Nat := do
  let mut k := 0
  for _ in [0:body.size] do
    match (if k == 0 then scanOpeningArg body pos columnsKeysOnly
      else scanBracketArg body k pos) with
    | .took k' =>
      for o in KeyVal.items (bracketSrc body k k') do
        if (boxPosOf o).isNone then
          warnOnce ctx ("columns:option:" ++ o) .N0102
            s!"'columns' option '{o}' is not modelled; ignored" pos
      k := k'
    | .unclosed bpos =>
      warnUnclosed ctx "'\\begin{columns}'" bpos
      break
    | .content => break
  return k

/-- A `\begin{column}[pos]`'s position and the index of its width group. -/
private def columnPosOf (cbody : Array Raw) (cpos : Pos) : Ir.BoxPos × Nat :=
  match scanBracketArg cbody 0 cpos with
  | .took k' => ((boxPosOf (bracketSrc cbody 0 k')).getD .top, skipSpaces cbody k')
  | _ => (.top, skipSpaces cbody 0)

/-- The flow-state update a declaration between blocks makes: a language
switch, a frame-count restart, or `\appendix`. -/
private def flowDecl? (ctx : Ctx) (n : String) (next : Nat) : Option (ESt → ESt) :=
  if let some tag := Marker.value? .lang n then some (flowLangUpdate ctx tag)
  else if n == Compat.frameRestartMark then
    some fun st => { st with frameRestart := st.frameRestart <|> some next }
  -- beamer's `\appendix` opens a part, which numbers no section anew
  else if n == "appendix" then
    if ctx.slides then some id
    else some fun st => { st with ctr := { st.ctr with inAppendix := true, secNums := (0, 0, 0) } }
  else none

/-- The tokens a `\block`'s `before` reads: the document's, then the engine's
page lengths and skip amounts. -/
private def blockSkipTokens (ctx : Ctx) : Array (String × Dim.SymGlue) :=
  ctx.tokens.entries ++ ctx.engineTokens ++
    #["smallskipamount", "medskipamount", "bigskipamount"].map fun n => (n, Ir.skipAmount ctx.tokens n)

/-- A `\block`'s option: its `before` skip, whether it stretches as `\fill`,
and whether it is a primitive `\vskip`. -/
private def blockOptions (ctx : Ctx) (optSrc : Array Raw) (pos : Pos) : EM (SymGlue × Bool) := do
  let (opts, ds) := Decl.parseBlock ctx.file (rawSrc optSrc) pos "block" (blockSkipTokens ctx)
  modify fun st => { st with diags := st.diags ++ ds }
  let mut before : SymGlue := {}
  let mut primitive := false
  let mut fill := false
  for e in opts do
    match e.key, e.value with
    | "before", .glue g => before := g
    | "before", .dim d => before := { width := Dim.Length.ofSp d }
    | "kind", .ident "vskip" => primitive := true
    | "kind", .ident "vspace" => primitive := false
    | "stretch", .glue g =>
      if g == { fil := true } then fill := true
      else
        let d := Decl.wrongType ctx.file "block" "stretch" "fill or unranked" (.glue g) pos
        modify fun st => { st with diags := st.diags.push d }
    | "stretch", .ident "unranked" =>
      warnOnce ctx "skip:stretch:unranked" .W0104
        "a skip's infinite stretch has an order or factor other than \\fill's; \
fills here have one order, so the skip sets at its natural width" pos
        (help := "write \\vfill or \\vspace{\\fill} for the page's leftover")
    | key, v =>
      let d := if key == "before" then Decl.wrongType ctx.file "block" key "a length" v pos
        else if key == "kind" then Decl.wrongType ctx.file "block" key "vspace or vskip" v pos
        else if key == "stretch" then Decl.wrongType ctx.file "block" key "fill or unranked" v pos
        else Decl.unknownKey ctx.file "block" key ["before", "kind", "stretch"] pos
      modify fun st => { st with diags := st.diags.push d }
  return ({ before with fil := before.fil || fill }, primitive)

/-- Pushes a skip block, marked as the last skip when it is an empty
primitive `\vskip`. -/
private def pushSkipBlock (blocks : Array Block) (b : Block) (primitive : Bool) : Array Block :=
  let empty := match b with
    | .spaced _ inner => inner.isEmpty
    | _ => false
  if primitive && empty then (blocks.push b).push (.role Ir.primitiveSkipRole #[]) else blocks.push b

seal blockSkipTokens blockOptions pushSkipBlock

/-- The page-model mark a control word stands for between blocks. -/
private def pageMark? (n : String) : Option Block :=
  if n == "pagebreak" then some .pagebreak
  else if n == Compat.vspaceAnchorMark then some (.role Ir.pageAnchorRole #[])
  else if n == "nointerlineskip" then some (.role Ir.noInterlineRole #[])
  else if (Ir.pageOpeningOfRole? n).isSome then some (.role n #[])
  else none

/-- The length keys Compat's closing mark restores at a scope's end. -/
private def lengthScopeKeys? (raws : Array Raw) : Option (Array String) :=
  match raws[raws.size - 1]? with
  | some (.ctrl n _) => Compat.lengthRestoreKeys? n
  | _ => none

/-- Saves the resolved opening values of a scope's restored lengths and strips
the closing mark. -/
private def openLengthScope (ctx : Ctx) (raws : Array Raw) :
    Array (String × SymGlue) × { body : Array Raw //
      rawWeightList body.toList ≤ rawWeightList raws.toList ∧
      rawParsList body.toList ≤ rawParsList raws.toList ∧
      nestedParsList body.toList ≤ nestedParsList raws.toList } :=
  if let some keys := lengthScopeKeys? raws then
    let saved := keys.filterMap fun key =>
      ((ctx.tokens.find? key).orElse fun _ =>
        (ctx.engineTokens.find? (·.1 == key)).map (·.2)).map (key, ·)
    (saved, ⟨raws.extract 0 (raws.size - 1),
      extract_weight_le .., extract_pars_le .., extract_nested_le ..⟩)
  else
    (#[], ⟨raws, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)

/-- Restores a scope's saved lengths as one token epoch. -/
private def closeLengthScope (ctx : Ctx) (saved : Array (String × SymGlue))
    (blocks : Array Block) : EM (Array Block) := do
  if saved.isEmpty then return blocks
  let st ← get
  let tk := saved.foldl (fun tk (key, value) => tk.declare key value)
    (st.flowTokens.getD ctx.tokens)
  modify fun st => { st with flowTokens := some tk, flowGen := st.flowGen + 1 }
  return blocks.push (.setTokens tk)

/-- Opens a standout frame's palette scope with the theme's standout
aliases. -/
private def openStandoutPalette (ctx : Ctx) (standout : Bool) (blocks : Array Block) :
    EM (MCtx ctx × Array Block × Bool) := do
  let aliases := (← get).scope.palette.standoutAliases
  if !standout then
    return (⟨ctx, rfl, rfl, rfl, rfl⟩, blocks, false)
  -- Only a generated palette re-tones a run against the standout ground.
  let ground (pal : Palette) : Option Color :=
    if pal.seeded.isSome then
      some ((Design.at pal .print .standoutGround).getD (Design.printInk pal))
    else none
  if aliases.isEmpty then
    let inner : Ctx := { ctx with
      ground := ground ctx.palette
      codeGround := some (Design.ofPalette ctx.palette).standout.bg }
    return (⟨inner, rfl, rfl, rfl, rfl⟩, blocks, false)
  let mut pal := ctx.palette
  for alias in aliases do
    let origin := { ctx with file := alias.span.file, callSite := none }
    pal ← applyPaletteEntry origin pal alias.name alias.source alias.name
      alias.span.pos (aliasOnly := true) (inBody := true)
    pal ← resolveBeamerColors origin pal
  modify fun st => { st with scope := { st.scope with palette := { st.scope.palette with current := some pal } },
                             flowGen := st.flowGen + 1 }
  let inner : Ctx := { ctx with
    palette := pal
    ground := ground pal
    codeGround := some (Design.ofPalette pal).standout.bg }
  return (⟨inner, rfl, rfl, rfl, rfl⟩, blocks.push (.setPalette pal), true)

private def closeFramePalette (ctx : Ctx) (pos : Pos) (blocks : Array Block)
    (title : Array Inline) (opts : FrameOpts) (inner : Array Block)
    (aliasScope : Bool) : EM (Array Block) := do
  recordFrameSource ctx pos blocks.size
  let frame := flattenFrame title opts.standout opts.valign opts.breakable inner
  let blocks := blocks.push (if opts.squeeze then frame.markFrame Ir.squeezeRole else frame)
  if !aliasScope then return blocks
  let colors := (← get).scope.palette
  let pal := BeamerColor.restoreAliases ctx.palette (colors.current.getD ctx.palette)
    (colors.standoutAliases.map (·.name))
  let pal ← resolveBeamerColors ctx pal
  modify fun st => { st with scope := { st.scope with palette := { st.scope.palette with current := some pal } },
                             flowGen := st.flowGen + 1 }
  return blocks.push (.setPalette pal)

/-- Opens a block scope: its frame-source base, flow epoch and saved
lengths. -/
private def openBlockScope (ctx : Ctx) (raws : Array Raw) :
    EM ((Option Nat × Nat) × Array (String × SymGlue) × { body : Array Raw //
      rawWeightList body.toList ≤ rawWeightList raws.toList ∧
      rawParsList body.toList ≤ rawParsList raws.toList ∧
      nestedParsList body.toList ≤ nestedParsList raws.toList }) := do
  let st ← get
  set { st with spans := { st.spans with frames :=
    { st.spans.frames with base := st.spans.frames.nextBase, nextBase := none } } }
  return ((st.spans.frames.base, st.flowGen), openLengthScope ctx raws)

private def closeBlockScope (ctx : Ctx) (savedLengths : Array (String × SymGlue))
    (savedBase : Option Nat) (blocks : Array Block) : EM (Array Block) := do
  let blocks ← closeLengthScope ctx savedLengths blocks
  setFrameSourceBase savedBase
  return blocks

seal lengthScopeKeys? openLengthScope closeLengthScope openBlockScope closeBlockScope
  openStandoutPalette closeFramePalette

/-- A laid-out paragraph's line from its raws, onto `out`: none where they hold only space. -/
private def linesFlush (ctx : Ctx) (depth : Nat) (cur : Array Raw) (out : Array LaidLine) :
    EM (Array LaidLine) := do
  let raws := trimRaws cur
  if raws.isEmpty then return out
  return out.push { depth, content := ← elabInlines ctx raws }

/-- A laid-out paragraph's lines from its raws, onto `out`: each run of inline raws one line at
`depth`, each nested lines environment's lines one deeper. -/
private def linesLaid (ctx : Ctx) (depth : Nat) :
    List Raw → Array Raw → Array LaidLine → EM (Array LaidLine)
  | [], cur, out => linesFlush ctx depth cur out
  | .env n inner p :: rest, cur, out => do
    if n == Parse.linesEnv then
      let out ← linesFlush ctx depth cur out
      let out ← linesLaid ctx (depth + 1) inner.toList #[] out
      linesLaid ctx depth rest #[] out
    else linesLaid ctx depth rest (cur.push (.env n inner p)) out
  | r :: rest, cur, out => linesLaid ctx depth rest (cur.push r) out
termination_by l => sizeOf l
decreasing_by raws_dec

mutual

/-- Whether a redefinition of a rendered built-in wins: its body, expanded
under probe arguments, elaborates non-empty with no dropped, pending or
degraded loss. -/
private def gateRedefB (ctx : Ctx) (cmd : UserCmd) : EM Bool := do
  if !renderedBuiltins.contains cmd.name then return true
  let saved ← get
  set saved.freshReport
  let ⟨checkCtx, _⟩ : MCtx ctx ← pure ⟨{ ctx with
    args := cmd.params.map fun p => (p.name, some #[Inline.text "x"])
    atUse := true },
    rfl, rfl, rfl, rfl⟩
  let nonEmpty ←
    if bodyIsBlock cmd.body then do
      have _ : slicePars cmd.body 0 ≤ rawParsList cmd.body.toList := by
        rw [slicePars_zero]; exact nestedParsList_le _
      have _ : sliceWeight cmd.body 0 = rawWeightList cmd.body.toList :=
        sliceWeight_zero _
      let bs ← elabBlockScope checkCtx cmd.body
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

/-- Drains a frame's stashed notes into its blocks. -/
private def drainNotesGo (ctx : Ctx) (stash : List (Array Raw × Pos))
    (inner : Array Block) : EM (Array Block) := do
  match stash with
  | [] => return inner
  | (nb, npos) :: rest =>
    let ⟨noteCtx, _hnf⟩ : { c : Ctx // c.envLimit = ctx.envLimit
        ∧ noteFlag c = 0 } ←
      pure ⟨{ ctx with noteBody := true, notePos := some npos }, rfl, rfl⟩
    let nblocks ← elabBlockScope noteCtx nb
    drainNotesGo ctx rest (inner.push (.note nblocks))
termination_by (ctx.envLimit, 1, 0, 0, 0, stash.length)
decreasing_by all_goals blocks_dec

/-- Elaborates each list item under its accumulated `\pause` base. -/
private def elabItemsGo (ctx : Ctx) (items : Array (Array Raw)) (itemPauses : Array Nat)
    (m : Nat) (acc : Array (Array Block)) (bound pbound : Nat)
    (hb : itemsMeas rawWeightList items.toList < bound)
    (hpb : itemsMeas nestedParsList items.toList ≤ pbound) :
    EM (Array (Array Block)) := do
  if hm : m < items.size then
    let ⟨it, _, _⟩ : { a : Array Raw //
        rawWeightList a.toList ≤ itemsMeas rawWeightList items.toList
          ∧ nestedParsList a.toList ≤ itemsMeas nestedParsList items.toList } ←
      pure ⟨items[m], itemsMeas_elem_le _ (Array.getElem?_eq_getElem hm),
        itemsMeas_elem_le _ (Array.getElem?_eq_getElem hm)⟩
    let p := (itemPauses[m]?).getD 0
    have _ : sliceWeight it 0 = rawWeightList it.toList := sliceWeight_zero _
    have _ : slicePars it 0 = nestedParsList it.toList := slicePars_zero _
    let ⟨stepCtx, hm2⟩ : MCtx ctx ←
      pure ⟨{ ctx with stepBase := ctx.stepBase + p }, rfl, rfl, rfl, rfl⟩
    let inner ← elabBlockScope stepCtx it
    let acc := acc.push inner
    elabItemsGo ctx items itemPauses (m + 1) acc bound pbound hb hpb
  else return acc
termination_by (ctx.envLimit, noteFlag ctx,
  visParsGo ctx.user ctx.limit + pbound,
  visWeightGo ctx.user ctx.limit + bound, 0, items.size + 1 - m)
decreasing_by all_goals blocks_dec

/-- Walks a float body: captions, subfigure columns and their gutters, and
the rest elaborated in place. -/
private def figureGo (ctx : Ctx) (n : String) (kind : Ir.FloatKind)
    (body : Array Raw) (j : Nat) (innerBlocks : Array Block)
    (cols : Array (BoxWidth × Array Block)) (rest : Array Raw)
    (caption : Array Inline) (capAbove : Bool) (blocks : Array Block)
    (hf : SliceFits rest body j (rawWeightList body.toList) (nestedParsList body.toList)) :
    EM (Array Block) := do
  if h : j < body.size then
    match hj : body[j] with
    | .ctrl "caption" cpos =>
      let (⟨j2, hj2⟩, _, _) ← skipOptArg ctx "caption" body (j + 1) cpos
      let j3 := skipSpaces body j2
      have hj3 := skipSpaces_ge body j2
      match body[j3]? with
      | some (.group t _) =>
        unless caption.isEmpty do
          diag ctx .W0311 s!"this '\\caption' replaces the {n}'s earlier caption"
            (some cpos) (help := "the last one wins; remove the other '\\caption'")
        let caption ← elabInlines ctx t
        let capAbove := innerBlocks.isEmpty && cols.isEmpty
          && rest.all isSpaceOrPar
        figureGo ctx n kind body (j3 + 1) innerBlocks cols rest caption
          capAbove blocks (hf.skip (by omega))
      | _ =>
        diag ctx .E0304 "'\\caption' needs a {text} group" cpos
        figureGo ctx n kind body j3 innerBlocks cols rest caption
          capAbove blocks (hf.skip (by omega))
    | .ctrl "centering" _ =>
      -- The float centres already; the declaration is satisfied.
      figureGo ctx n kind body (j + 1) innerBlocks cols rest caption
        capAbove blocks (hf.skip (by omega))
    | .ctrl "hfill" _ =>
      -- Between subfigures the fill is the gutter the columns layout sets.
      if !cols.isEmpty && rest.all isSpaceOrPar then
        figureGo ctx n kind body (j + 1) innerBlocks cols rest caption
          capAbove blocks (hf.skip (by omega))
      else
        figureGo ctx n kind body (j + 1) innerBlocks cols
          (rest.push body[j]) caption capAbove blocks (hf.keep h rfl)
    | .env sn sbody spos =>
      if sn == "subfigure" || sn == "subtable" then do
        have hbe : body[j]? = some (.env sn sbody spos) := by
          rw [Array.getElem?_eq_getElem h]; exact congrArg some hj
        have _ := env_measures hbe
        have _ := hf.bounds
        let (innerBlocks, cols) ←
          if rest.any (!isSpaceOrPar ·) then do
            let innerBlocks :=
              if cols.isEmpty then innerBlocks
              else innerBlocks.push (.columns cols)
            have _ : sliceWeight rest 0 = rawWeightList rest.toList :=
              sliceWeight_zero _
            have _ : slicePars rest 0 = nestedParsList rest.toList :=
              slicePars_zero _
            let rb ← elabBlockScope ctx rest
            pure (innerBlocks ++ rb, (#[] : Array (BoxWidth × Array Block)))
          else pure (innerBlocks, cols)
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
          #[] false #[] (rawWeightList sbody.toList) (nestedParsList sbody.toList)
          (SliceFits.whole sbody m)
        have hsp3 := nestedParsList_le sbody.toList
        have hs0 : sliceWeight sRest 0 = rawWeightList sRest.toList :=
          sliceWeight_zero _
        have hs1 : slicePars sRest 0 = nestedParsList sRest.toList :=
          slicePars_zero _
        let mut sInner ← elabBlockScope ctx sRest
        unless sCaption.isEmpty do
          sInner := Ir.captionAltBlocks sCaption sInner
        figureGo ctx n kind body (j + 1) innerBlocks
          (cols.push ({ width with pos := subPos }, #[.float .sub none sCapAbove sInner sCaption]))
          #[] caption capAbove blocks (hf.flush (by omega))
      else
        figureGo ctx n kind body (j + 1) innerBlocks cols
          (rest.push body[j]) caption capAbove blocks (hf.keep h rfl)
    | _ =>
      figureGo ctx n kind body (j + 1) innerBlocks cols
        (rest.push body[j]) caption capAbove blocks (hf.keep h rfl)
  else do
    let innerBlocks :=
      if cols.isEmpty then innerBlocks else innerBlocks.push (.columns cols)
    have _ : sliceWeight rest 0 = rawWeightList rest.toList :=
      sliceWeight_zero _
    have _ : slicePars rest 0 = nestedParsList rest.toList :=
      slicePars_zero _
    have _ := hf.bounds
    let rb ← elabBlockScope ctx rest
    let mut inner := innerBlocks ++ rb
    unless caption.isEmpty do
      inner := Ir.captionAltBlocks caption inner
    return blocks.push (.float kind none capAbove inner caption)
termination_by (ctx.envLimit, noteFlag ctx,
  visParsGo ctx.user ctx.limit + nestedParsList body.toList,
  visWeightGo ctx.user ctx.limit + rawWeightList body.toList + 1, 0,
  body.size + 1 - j)
decreasing_by all_goals blocks_dec

/-- Walks a `{columns}` body: consecutive `{column}` children form one row,
and other content stays in place. -/
private def columnsGo (ctx : Ctx) (body : Array Raw) (j : Nat)
    (cols : Array (BoxWidth × Array Block)) (strayRaws : Array Raw)
    (blocks : Array Block)
    (hf : SliceFits strayRaws body j (rawWeightList body.toList) (nestedParsList body.toList)) :
    EM (Array Block) := do
  if h : j < body.size then
    match hj : body[j] with
    | .env "column" cbody cpos =>
      have hbe : body[j]? = some (.env "column" cbody cpos) := by
        rw [Array.getElem?_eq_getElem h]; exact congrArg some hj
      have _ := env_measures hbe
      have _ := hf.bounds
      let (cols, blocks) ←
        if strayRaws.any isColumnStray then do
          let blocks := if cols.isEmpty then blocks
            else blocks.push (.columns cols)
          have _ : sliceWeight strayRaws 0
              = rawWeightList strayRaws.toList := sliceWeight_zero _
          have _ : slicePars strayRaws 0
              = nestedParsList strayRaws.toList := slicePars_zero _
          let sb ← splicedFrameScope (some blocks.size) (elabBlockScope ctx strayRaws)
          pure ((#[] : Array (BoxWidth × Array Block)), blocks ++ sb)
        else pure (cols, blocks)
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
      have hcm := tail_measures cbody m2
      have hcp2 := nestedParsList_le cbody.toList
      -- A column is a group: beamer sets each in a minipage of its own.
      let cinner ← groupBlocks ctx.palette (elabBlockScope ctx (cbody.extract m2 cbody.size))
      columnsGo ctx body (j + 1) (cols.push ({ width with pos := colPos }, cinner)) #[]
        blocks (hf.flush (by omega))
    | _ =>
      columnsGo ctx body (j + 1) cols (strayRaws.push body[j]) blocks (hf.keep h rfl)
  else do
    let blocks := if cols.isEmpty then blocks else blocks.push (.columns cols)
    if strayRaws.any isColumnStray then
      have _ : sliceWeight strayRaws 0 = rawWeightList strayRaws.toList :=
        sliceWeight_zero _
      have _ : slicePars strayRaws 0 = nestedParsList strayRaws.toList :=
        slicePars_zero _
      have _ := hf.bounds
      let sb ← splicedFrameScope (some blocks.size) (elabBlockScope ctx strayRaws)
      return blocks ++ sb
    else
      return blocks
termination_by (ctx.envLimit, noteFlag ctx,
  visParsGo ctx.user ctx.limit + nestedParsList body.toList,
  visWeightGo ctx.user ctx.limit + rawWeightList body.toList + 1, 0,
  body.size + 1 - j)
decreasing_by all_goals blocks_dec

private def elabEnvArm (ctx : Ctx) (n : String) (scope : Array Raw)
    (pos : Pos) (blocks : Array Block) : EM (Array Block) := do
  let (savedLengths, ⟨body, _, _, _⟩) := openLengthScope ctx scope
  have _ : sliceWeight body 0 = rawWeightList body.toList := sliceWeight_zero _
  have _ : slicePars body 0 = nestedParsList body.toList := slicePars_zero _
  have _ := nestedParsList_le body.toList
  let mut blocks := blocks
  if n == Parse.scopeEnv then
    blocks := blocks ++ (← splicedFrameScope (some blocks.size) (elabBlockScope ctx body))
  else if n == Parse.linesEnv then
    blocks := blocks.push (.lines (← linesLaid ctx 0 body.toList #[] #[]))
  else if let some f := Parse.inputEnvFile? n then
    let ⟨fileCtx, _⟩ : MCtx ctx ←
      pure ⟨{ ctx with file := f, callSite := none, kept := ctx.kept || Parse.isKeptInput n },
        rfl, rfl, rfl, rfl⟩
    blocks := blocks ++ (← splicedFrameScope (some blocks.size) (elabBlockScope fileCtx body))
  else if let some numbered := displayMathEnvs.lookup n then
    blocks ← displayMathArm ctx numbered body pos blocks
  else if let some (kind, numbered) := alignEnvs.lookup n then
    blocks ← alignEnvArm ctx n kind numbered body pos blocks
  else if Compat.tableEnvs.contains n || n == Parse.markdownTableEnv then
    blocks ← tabularArm ctx n body pos blocks
  else if n == "thebibliography" then
    blocks := blocks ++ (← ownBibList ctx body)
  else if n == "frame" then
    -- A label in a deck's frame binds no section's number, and one after it the section's again.
    let outer := (← get).refTarget
    if ctx.slides then modify fun st => { st with refTarget := none }
    -- A paragraph break before the title group makes it content, as in LaTeX.
    let opts ← frameOpts ctx body pos
    let (⟨frameCtx, _⟩, frameBlocks, aliasScope) ← openStandoutPalette ctx opts.standout blocks
    blocks := frameBlocks
    let mut k := skipSpaces body opts.next
    let mut title : Array Inline := #[]
    if let some (.group t _) := body[k]? then
      title ← elabInlines (barCtx frameCtx .frameTitleBar) t
      k := k + 1
    let (title2, ⟨rest, _⟩) ← frameRestGo (barCtx frameCtx .frameTitleBar) body k title #[] #[]
      (rawWeightList body.toList) (nestedParsList body.toList) (SliceFits.whole body k)
    title := title2
    have _ : sliceWeight rest 0 = rawWeightList rest.toList := sliceWeight_zero _
    have _ : slicePars rest 0 = nestedParsList rest.toList := slicePars_zero _
    -- A note's own frame has no side channel, so its stashed notes are refused.
    modify fun st => { st with pendingNotes := #[] }
    let mut inner ← elabBlockScope frameCtx rest
    let stash := (← get).pendingNotes
    modify fun st => { st with pendingNotes := #[] }
    if hnb : ctx.noteBody then
      unless stash.isEmpty do
        diag ctx .E0359
          "a '\\note' inside this note's frame is dropped: one note cannot carry another"
          ctx.notePos
          (help := "move the inner '\\note' out of the enclosing '\\note', beside its frame")
    else
      have _ : noteFlag ctx = 2 := by simp [noteFlag, hnb]
      inner ← drainNotesGo frameCtx stash.toList inner
    -- A frame nests no frame: an inner title frame flattens into this one.
    blocks ← closeFramePalette ctx pos blocks title opts inner aliasScope
    if ctx.slides then modify fun st => { st with refTarget := outer }
  else if n == "itemize" || n == "enumerate" || n == "description" then
    let (bodyFrom, spacing) ← listOptsArm ctx n body pos
    let ⟨lbody, _, _⟩ : { a : Array Raw //
        rawWeightList a.toList ≤ rawWeightList body.toList
          ∧ nestedParsList a.toList ≤ nestedParsList body.toList } ←
      pure ⟨body.extract bodyFrom body.size, extract_weight_le ..,
        extract_nested_le ..⟩
    -- `\pause` between items steps the rest of the list, not only the item.
    let ⟨(items, steps, itemPauses, scope), hsplit⟩ ← itemSplitGo ctx lbody pos
      (n == "description") {} 0
      #[] #[] #[] 0 #[] none 0 false false false false
      (sliceWeight lbody 0) (slicePars lbody 0)
      (ItemSplitFits.start lbody 0)
    have hiw : itemsMeas rawWeightList items.toList ≤ sliceWeight lbody 0 := hsplit.1
    have hip : itemsMeas nestedParsList items.toList ≤ slicePars lbody 0 := hsplit.2
    have hl0 : sliceWeight lbody 0 = rawWeightList lbody.toList :=
      sliceWeight_zero _
    have hl1 : slicePars lbody 0 = nestedParsList lbody.toList :=
      slicePars_zero _
    -- Literal punctuation must reach the item reader before its text elaborates.
    let literal := ctx.literalText || Ir.Decl.anyStyle (· == .mono) scope.decls
    let ⟨itemCtx, _⟩ : MCtx ctx ← pure ⟨{ ctx with
        literalText := literal, listNest := ctx.listNest.enter n spacing },
      rfl, rfl, rfl, rfl⟩
    let elabItems ← withBlockDecls scope.decls do
      let elabItems ← elabItemsGo itemCtx items itemPauses 0 #[]
        (rawWeightList lbody.toList + 1) (nestedParsList lbody.toList)
        (by omega) (by omega)
      if n == "description" then descItems itemCtx lbody elabItems
      else pure elabItems
    blocks := blocks ++ wrapDeclAlign scope.align
      #[.list (n == "enumerate") spacing (coverItems ctx steps itemPauses elabItems)]
  else if n == "center" || (Ir.raggedSideOf? n).isSome then
    let inner ← elabBlockScope ctx body
    -- The environment is a trivlist and opens `\topsep`; the declaration does not.
    blocks := blocks.push (.role Ir.trivlistRole #[match Ir.raggedSideOf? n with
      | some side => .ragged side inner
      | none => .center inner])
  else if n == "minipage" then
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
    have _ := tail_measures body m2
    blocks := blocks.push
      (.columns #[({ width with pos := boxPos }, ← elabBlockScope ctx (body.extract m2 body.size))])
  else if let some kind := titledKind? n then
    let (head, k) := selectorHead body 0
    let spec ← selectorSpec ctx head pos
    let mut title : Array Inline := #[]
    let mut m := k
    match body[k]? with
    | some (.group t _) =>
      title ← elabInlines (barCtx ctx (Role.titleBar kind)) t
      m := k + 1
    | _ =>
      diag ctx .E0304 s!"'\\begin\{{n}}' needs a \{title} group" pos
        (help := "an empty group is an untitled block")
    have _ := tail_measures body m
    let ⟨bodyCtx, _⟩ := titledBodyCtx ctx kind
    let inner ← elabBlockScope bodyCtx (body.extract m body.size)
    blocks := blocks ++ selectedCover Block.onSteps spec #[.titled kind title inner]
  else if scopedEnv (← get).ctr.thm n then
    let (o, k) ← scopeOpen ctx n body pos
    have _ := tail_measures body k
    let inner ← elabBlockScope ctx (body.extract k body.size)
    blocks := blocks ++ (← scopeClose ctx n o inner pos)
  else if n == "quote" || n == "quotation" || n == "verse" || n == "abstract"
      || n == "appendices" then
    let saved ← enterAppendicesIf (n == "appendices")
    -- A quotation is a list level, which its enclosing lists' spacing reaches as LaTeX's does.
    let ⟨quoteCtx, _⟩ : MCtx ctx ← pure ⟨
      if n == "appendices" || (n == "abstract" && !ctx.abstractNests) then ctx
      else { ctx with listNest := ctx.listNest.quoted ctx.lists ctx.page.fontSize },
      by split <;> rfl, by split <;> rfl, by split <;> rfl, by split <;> rfl⟩
    let inner ← splicedFrameScope (if n == "appendices" then some blocks.size else none)
      (elabBlockScope quoteCtx body)
    leaveAppendices saved
    blocks := wrapScopedEnv n blocks inner
  else if n == "figure" || n == "figure*" || n == "table" || n == "table*" then
    let kind : Ir.FloatKind :=
      if n == "table" || n == "table*" then .table else .figure
    -- The placement is the float's own; a `center` child after it is spliced, so its
    -- `\caption` and `\label` are the float's.
    let k ← floatPlacement ctx n body pos
    have hxm := tail_measures body k
    let ⟨fbody, _, _⟩ ← pure (spliceCenterGo (body.extract k body.size).toList #[]
      (rawWeightList body.toList) (nestedParsList body.toList)
      (by simpa [rawWeightList] using hxm.1) (by simpa [nestedParsList] using hxm.2.1))
    blocks ← figureGo ctx n kind fbody 0 #[] #[] #[] #[] false blocks
      (SliceFits.whole fbody 0)
  else if n == "algorithm" || n == "algorithm*" || n == "algorithm2e" then
    blocks ← algorithmArm ctx n body pos blocks
  else if n == "algorithmic" then
    blocks ← algorithmicArm ctx body pos blocks
  else if n == "columns" then
    let k ← columnsOptsArm ctx body pos
    blocks ← columnsGo ctx body k #[] #[] blocks (SliceFits.whole body k)
  else if n == "ifbackend" then
    let j ← pure (skipSpaces body 0)
    match body[j]? with
    | some (.group g gpos) =>
      diag ctx .N0019
        "content addressed per backend encodes a per-medium decision by hand" pos
        (help := "a construct carries its own medium answer (a nav, a note); \
prefer the construct or the class, and keep '\\begin{ifbackend}' for the true remainder")
      let names := Decl.splitEntries (rawSrc g)
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
      have hxm := tail_measures body (j + 1)
      let inner ← elabBlockScope backCtx (body.extract (j + 1) body.size)
      blocks := blocks.push (.only targets inner)
    | _ =>
      diag ctx .E0304 "'\\begin{ifbackend}' needs a {backends} group" pos
        (help := "write \\begin{ifbackend}{html} ... \\end{ifbackend}")
      blocks := blocks ++ (← splicedFrameScope (some blocks.size) (elabBlockScope ctx body))
  else if n == "nav" then
    match scanBracketArg body 0 pos with
    | .took k =>
      let inner := bracketSrc body 0 k
      let spec ← navSpecOf ctx inner pos
      have _ := tail_measures body k
      blocks := blocks.push (.nav spec (← elabBlockScope ctx (body.extract k body.size)))
    | _ =>
      blocks := blocks.push (.nav {}
        (← elabBlockScope ctx body))
  else if hle : (lookupUserEnv ctx n).isSome then
    -- Halves and content elaborate apart: merging them mixes two argument scopes.
    let ke := (lookupUserEnv ctx n).get hle
    have hle2 : lookupUserEnv ctx n = some ke := (Option.some_get hle).symm
    have _ : ke.1 < ctx.envLimit := lookupUserEnv_lt hle2
    let env := ke.2
    let (bindings, j) ← takeArgs ctx env.params n body 0 pos
    -- An absent optional argument takes its definition's default, read where the halves read.
    let bindings ← match absentDefault? env.params bindings with
      | some (p, d) => do
        let dctx : Ctx := { ctx with limit := env.cmdLimit, envLimit := ke.1, args := bindings }
        pure (bindDefault p d (← elabInlinesCore { dctx with argBody := true } d) bindings)
      | none => pure bindings
    let ⟨envCtx, _⟩ : { c : Ctx // c.envLimit = ke.1 } ←
      pure ⟨{ ctx with
        limit := env.cmdLimit, envLimit := ke.1, args := bindings }, rfl⟩
    blocks := blocks ++ (← splicedFrameScope (some blocks.size) (elabBlockScope envCtx env.beginBody))
    have _ := tail_measures body j
    blocks := blocks ++ (← splicedFrameScope (some blocks.size)
      (elabBlockScope ctx (body.extract j body.size)))
    blocks := blocks ++ (← splicedFrameScope (some blocks.size) (elabBlockScope envCtx env.endBody))
  else if n == "tikzpicture" || n == "tikzcd" then
    blocks ← pictureEnvArm ctx n body pos blocks
  else if reservedEnv.contains n then
    warnOnce ctx ("env:" ++ n) .W0307
      s!"'\{{n}}' is not implemented yet; its content is not rendered" pos
  else
    warnOnce ctx ("env:" ++ n) .W0302 s!"unknown environment '\{{n}}'; its body is kept" pos
      (help := "\\defineenv{name}(...) {begin} {end} declares one")
    let (keptFrom, unclosed, dropped) := dropEnvArgs body pos
    let ⟨kept, _, _⟩ : { a : Array Raw //
        rawWeightList a.toList ≤ rawWeightList body.toList
          ∧ nestedParsList a.toList ≤ nestedParsList body.toList } ←
      pure ⟨body.extract keptFrom body.size, extract_weight_le ..,
        extract_nested_le ..⟩
    if let some bpos := unclosed then
      warnUnclosed ctx s!"'\\begin\{{n}}'" bpos
    warnDroppedArgs ctx n (body.extract 0 keptFrom) dropped pos
    have _ : sliceWeight kept 0 = rawWeightList kept.toList := sliceWeight_zero _
    have _ : slicePars kept 0 = nestedParsList kept.toList := slicePars_zero _
    blocks := blocks ++ (← splicedFrameScope (some blocks.size) (elabBlockScope ctx kept))
  closeLengthScope ctx savedLengths blocks
termination_by (ctx.envLimit, noteFlag ctx,
  visParsGo ctx.user ctx.limit + rawParsList scope.toList,
  visWeightGo ctx.user ctx.limit + 1 + rawWeightList scope.toList, 1, 0)
decreasing_by all_goals blocks_dec

/-- One general control word at block level: misplaced declarations, user
commands, block overlays, title declarations, `\logo`, `\maketitle` and the
headings. -/
private def elabCtrlArm (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (h : i < raws.size) (n : String) (pos : Pos) (blocks : Array Block) :
    EM (Array Block × { j : Nat // i < j }) := do
  let sourceName := n
  let n := Compat.overlayName n
  have hadv := advance_measures raws h (show i < i + 1 by omega)
  let mut blocks := blocks
  if declCtrl.contains n then
    warnOnce ctx ("ctrl:" ++ n) .W0340
      s!"'\\{n}' is a declaration; in the body it is ignored" pos
      (help := "declare it in the preamble, before '\\begin{document}'")
    let ju := skipReservedArgs raws (i + 1) pos (maxGroups := 2)
    have hj : i + 1 ≤ ju.1 := skipReservedArgs_ge raws (i + 1) pos 2
    if let some bpos := ju.2 then
      warnUnclosed ctx s!"'\\{n}'" bpos
    return (blocks, ⟨ju.1, by omega⟩)
  else if runningCtrl.contains n then
    diag ctx .E0347 s!"'\\{n}' in the body is dropped with its content" pos
      (help := "declare it in the preamble, before '\\begin{document}'")
    let ju := skipReservedArgs raws (i + 1) pos
    have hj : i + 1 ≤ ju.1 := skipReservedArgs_ge raws (i + 1) pos 1
    if let some bpos := ju.2 then
      warnUnclosed ctx s!"'\\{n}'" bpos
    return (blocks, ⟨ju.1, by omega⟩)
  -- A document's redefinition shadows the literal link arm.
  else if ["href", "link", "hyperlink", "hypertarget"].contains n
      && (lookupUser ctx sourceName).isNone then
    let head := linkSelectorHead n raws (i + 1)
    let j := head.2
    have hjge : i + 1 ≤ j := linkSelectorHead_monotone n raws (i + 1)
    let spec ← selectorSpec ctx head.1 pos
    let j2 := skipSpaces raws (j + 1)
    have hj2ge := skipSpaces_ge raws (j + 1)
    match hj : raws[j]?, hj2 : raws[j2]? with
    | some (.group targetRaw _), some (.group body _) =>
      have hj2lt := getElem?_lt hj2
      have hbm := group_measures hj2 (show i ≤ j2 by omega)
      let inner ← splicedFrameScope (some (blocks.size + if n == "hypertarget" then 1 else 0))
        (elabBlockScope ctx body)
      let target := argText ctx targetRaw
      let wrapped ←
        if n == "hypertarget" then pure (#[Block.para #[.label target]] ++ inner)
        else
          let anchor := Ir.labelAnchor target
          let url := if n == "hyperlink" then "#".append anchor else target
          let nested := Ir.hasBlockAnchor inner
          if nested then do
            warnOnce ctx "link:nested" .W0104
              "a link wrapper contains another link; the outer link is skipped" pos
              (help := "links cannot nest; move the inner link outside the outer wrapper")
            pure inner
          else
            let kind := if n == "hyperlink" then "link" else "url"
            pure (Ir.linkBlocks url (ctx.styles.linkBodyAfford kind inner))
      let selected := match spec with
        | some spec =>
          let (firstPage, otherPage) := spec.pageOrder wrapped #[]
          #[Block.altSteps spec firstPage otherPage]
        | none => wrapped
      -- Only the nested-anchor recovery and hypertarget splice their bodies.
      if spec.isSome || (n != "hypertarget" && !Ir.hasBlockAnchor inner) then
        keepFrameSourcePrefix blocks.size
      return (blocks ++ selected, ⟨j2 + 1, by omega⟩)
    | _, _ =>
      diag ctx .E0304 s!"'\\{n}' needs a \{target}\{content}" pos
      return (blocks, ⟨i + 1, by omega⟩)
  else
  match hlk : lookupUser ctx sourceName with
  | some (k, cmd) =>
    let (bindings, ⟨j, hj⟩) ← takeArgsFrom ctx cmd.params 0 n raws (i + 1)
      pos #[]
    let ⟨callCtx, _, _, _, _⟩ : { c : Ctx // c.envLimit = ctx.envLimit
        ∧ noteFlag c = noteFlag ctx
        ∧ visParsGo c.user c.limit = visParsGo ctx.user k
        ∧ visWeightGo c.user c.limit = visWeightGo ctx.user k } ←
      pure ⟨{ ctx.atCall sourceName pos with limit := k, args := bindings }, rfl, rfl, rfl, rfl⟩
    have _ := visPars_expand hlk
    have _ := visWeight_expand hlk
    have _ : slicePars cmd.body 0 ≤ rawParsList cmd.body.toList := by
      rw [slicePars_zero]; exact nestedParsList_le _
    have _ : sliceWeight cmd.body 0 = rawWeightList cmd.body.toList :=
      sliceWeight_zero _
    let expanded ← splicedFrameScope (if cmd.params.isEmpty then some blocks.size else none)
      (elabBlockScope callCtx cmd.body)
    if cmd.params.isEmpty then
      blocks := blocks ++ expanded
    else
      blocks := blocks.push (.role cmd.name expanded)
    return (blocks, ⟨j, by omega⟩)
  | none =>
  if overlayCtrls.contains n || n == "alt" then
    let j := skipSpaces raws (i + 1)
    have hjge : i + 1 ≤ j := skipSpaces_ge raws (i + 1)
    let ⟨(spec, jg), hjg⟩ :
        { t : Option Ir.OverlaySpec × Nat // i + 1 ≤ t.2 } ←
      match raws[j]?.bind specWord? with
      | some w => do
        let jg := skipSpaces raws (j + 1)
        have h2 : i + 1 ≤ jg := by
          have := skipSpaces_ge raws (j + 1); omega
        match overlaySpecFor n w with
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
        have _ := group_measures hga (show i ≤ jg by omega)
        have _ := group_measures hgb (show i ≤ j3 by omega)
        match spec with
        | some spec =>
          let ⟨stepCtx, hm⟩ : MCtx ctx ←
            pure ⟨{ ctx with stepBase := max ctx.stepBase (spec.start - 1) },
              rfl, rfl, rfl, rfl⟩
          let ia ← elabBlockScope stepCtx ga
          let ib ← elabBlockScope ctx gb
          blocks := blocks.push (altCarriers raws i j3 blocks spec ga gb ia ib)
          return (blocks, ⟨j3 + 1, by omega⟩)
        | none =>
          warnAltSpec ctx pos
          blocks := blocks ++ (← splicedFrameScope (some blocks.size) (elabBlockScope ctx ga))
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
        have _ := group_measures hgg (show i ≤ jg by omega)
        match spec with
        | some spec =>
          let ⟨stepCtx, hm⟩ : MCtx ctx ←
            pure ⟨{ ctx with stepBase := max ctx.stepBase (spec.start - 1) },
              rfl, rfl, rfl, rfl⟩
          let inner ← elabBlockScope stepCtx gbody
          let inner := carrierInGroup raws i jg blocks gbody inner
          unless inner.isEmpty do
            blocks := blocks.push (.onSteps spec inner)
          return (blocks, ⟨jg + 1, by omega⟩)
        | none =>
          blocks := blocks ++ (← splicedFrameScope (some blocks.size) (elabBlockScope ctx gbody))
          return (blocks, ⟨jg + 1, by omega⟩)
      | _ =>
        -- The open form: the rest of the scope steps; a bare `\onslide` ends stepping.
        match spec with
        | some spec =>
          have _ := rest_measures raws jg
          have _ : sliceWeight raws jg < sliceWeight raws i := by
            have := sliceWeight_le raws (show i + 1 ≤ jg by omega); omega
          have _ : slicePars raws jg ≤ slicePars raws i := by
            have := slicePars_le raws (show i ≤ jg by omega); omega
          let ⟨stepCtx, _⟩ : MCtx ctx ←
            pure ⟨{ ctx with stepBase := max ctx.stepBase (spec.start - 1) },
              rfl, rfl, rfl, rfl⟩
          let inner ← elabBlockScope stepCtx (raws.extract jg raws.size)
          let inner := carrierToEnd raws i jg blocks inner
          unless inner.isEmpty do
            blocks := blocks.push (.onSteps spec inner)
          return (blocks, ⟨raws.size, by omega⟩)
        | none =>
          return (blocks, ⟨jg, by omega⟩)
  else if titleCtrls.contains n then
    let (⟨j, hj⟩, junk) ← takeTitleDecl ctx n raws (i + 1) pos
    -- The malformed run of an unclosed bracket is content here.
    if let some p ← mkPara ctx junk then
      blocks := blocks.push p
    return (blocks, ⟨j, by omega⟩)
  -- premise: sectionPageChecks — outside a deck the hooks are unknown, their arguments kept
  else if ctx.slides && (n == "AtBeginSection" || n == "AtBeginSubsection") then
    let ju := skipReservedArgs raws (i + 1) pos
    have hj : i + 1 ≤ ju.1 := skipReservedArgs_ge raws (i + 1) pos 1
    bodySectionHook ctx n raws (i + 1) pos
    return (blocks, ⟨ju.1, by omega⟩)
  else if n == "logo" then
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
    if let .took _ := scanBracketArg raws i1 pos then
      warnOnce ctx ("section:short:" ++ n) .N0103
        s!"'\\{n}[short]' short title is unused: nothing consumes it yet" pos
    let (⟨j, hj⟩, recovered, junk) ← skipOptArg ctx n raws i1 pos
    if let some p ← mkPara ctx junk then
      blocks := blocks.push p
    match raws[j]? with
    | some (.group title _) =>
      blocks := blocks.push (.section ((blockHeading? n).getD .h2) starred
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

/-- The block spine: a boundary raw flushes the open paragraph and
dispatches, and any other raw joins it. -/
private def elabBlocksGo (ctx : Ctx) (raws : Array Raw) (i : Nat)
    (blocks : Array Block) (cur : Array Raw) (gen : Nat) :
    EM (Array Block) := do
  let stFlow ← get
  let (⟨ctx', _⟩, blocks, cur) ← blockMacroStep ctx stFlow gen raws i blocks cur
  let gen' ← pure stFlow.flowGen
  if h : i < raws.size then
    have _ := advance_measures raws h (show i < i + 1 by omega)
    match hr : raws[i] with
    | .group body gpos =>
      have hre : raws[i]? = some (.group body gpos) := by
        rw [Array.getElem?_eq_getElem h]; exact congrArg some hr
      have hgm := group_measures hre (Nat.le_refl i)
      if hpp : body.any isParRaw && !isArgument cur && (lengthScopeKeys? body).isNone &&
          !sizeParScope body then
        -- A group holding a paragraph end splices open, save a size scope ending one.
        have hpp2 : body.any isParRaw = true := by
          simp only [Bool.and_eq_true] at hpp; exact hpp.1.1.1
        have _ := slicePars_splice h hr hpp2 ctx' gpos
        elabBlocksGo ctx' (raws.extract 0 i
          ++ splitAtPars ctx' body gpos ++ raws.extract (i + 1) raws.size) i
          blocks cur gen'
      else if body.any isParRaw && !isArgument cur then
        -- A restoring scope stays whole so its snapshot predates every assignment.
        let inner ← restoringGroup ctx' cur
          (splicedFrameScope (some blocks.size) (elabBlockScope ctx' body cur))
        elabBlocksGo ctx' raws (i + 1) (blocks ++ inner) #[] gen'
      else if (body.any isCenteringRaw || bodyIsBlock body) && !isArgument cur then
        groupPictureInSentence ctx' body cur raws i
        let (⟨ctx', _⟩, blocks) ← flushPara ctx' blocks cur
        let inner ← groupBlocks ctx'.palette
          (splicedFrameScope (some blocks.size) (elabBlockScope ctx' body))
        elabBlocksGo ctx' raws (i + 1) (blocks ++ inner) #[] gen'
      else
        elabBlocksGo ctx' raws (i + 1) blocks (cur.push raws[i]) gen'
    | .par _ =>
      let (⟨ctx', hm⟩, blocks) ← flushPara ctx' blocks cur
      elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
    | .verb env s vpos =>
      if verbRunsInline env s cur raws i then
        elabBlocksGo ctx' raws (i + 1) blocks (cur.push raws[i]) gen'
      else
      let (⟨ctx', hm⟩, blocks) ← flushPara ctx' blocks cur
      let b ← listingBlock ctx' env s vpos
      elabBlocksGo ctx' raws (i + 1) (blocks.push b) #[] gen'
    | .math display body mpos =>
      if display then
        -- `\[` is amsmath's `equation*`.
        let (⟨ctx', hm⟩, blocks) ←
          displayAtBlock ctx' body mpos blocks cur raws i
        elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else
        elabBlocksGo ctx' raws (i + 1) blocks (cur.push raws[i]) gen'
    | .env n body epos =>
      if hn : n = Compat.linkedBoxRowMark then
        -- premise: nativeLinkedRow_gated — macros and parameters own their arguments
        if nativeLinkedRow ctx' body then noteLinkedRow ctx' body epos
        let chosen := (linkedRowChoice body (nativeLinkedRow ctx' body)).val
        have _ := linkedRowChoice_splice h (body := body) (pos := epos)
          (by simpa only [hn] using hr) (nativeLinkedRow ctx' body)
        return ← elabBlocksGo ctx'
          (raws.extract 0 i ++ chosen ++ raws.extract (i + 1) raws.size)
          i blocks cur gen'
      have hre : raws[i]? = some (.env n body epos) := by
        rw [Array.getElem?_eq_getElem h]; exact congrArg some hr
      have hem := env_measures hre
      let thmS := (← get).ctr.thm
      let isB : Bool :=
        if (Parse.inputEnvFile? n).isSome then bodyIsBlock body
        else
          blockEnvs.contains n || isMathEnv n || n == Tcolorbox.boxEnv
            || n == "tabular" || n == "tabular*" || Parse.markdownEnv n || n == Parse.linesEnv
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
        let (⟨ctx', hm⟩, flushed) ← flushPara ctx' blocks cur
        let inPar := Ir.flushedText k flushed
        let afterEnv := endPeAt raws i inPar flushed
        let blocks ← envGroup n ctx'.palette inPar (parFollows raws (i + 1)) afterEnv
          flushed.size (elabEnvArm ctx' n body epos flushed)
        elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else
        elabBlocksGo ctx' raws (i + 1) blocks (cur.push raws[i]) gen'
    | .ctrl n cpos =>
      -- A page-ground command mid-paragraph changes shipout state, not structure.
      if !cur.isEmpty && isPageGround n then
        let pal? ← pageGround ctx' n cpos
        match pal? with
        | some pal => modify fun st =>
          { st with scope := { st.scope with palette := { st.scope.palette with current := some pal } },
                    flowGen := st.flowGen + 1 }
        | none => pure ()
        let ⟨palCtx, _⟩ : MCtx ctx' ←
          pure ⟨{ ctx' with palette := pal?.getD ctx'.palette }, rfl, rfl, rfl, rfl⟩
        return ← elabBlocksGo palCtx raws (i + 1)
          (match pal? with
            | some pal => blocks.push (.setPalette pal)
            | none => blocks) cur ((← get).flowGen)
      let isB : Bool := isBlockStart ctx' n raws i cur
      if !isB then
        elabBlocksGo ctx' raws (i + 1) blocks (cur.push raws[i]) gen'
      else
      macroPictureInSentence ctx' n cur raws i cpos
      noteSplitDecl ctx' n cur cpos
      let (⟨ctx', _⟩, blocks) ← flushPara ctx' blocks cur
      if n == "par" then
        elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else if n == "centering" || (Ir.raggedSideOf? n).isSome
          || isDeclBlock ctx' n raws i cur then
        -- The declaration forms of center and flushleft align the rest of the scope.
        have _ := rest_measures raws (i + 1)
        let (⟨ctx', _⟩, blocks) ← closeBlockMacros ctx' blocks
        let saved ← enterBlockDecl ctx' n raws i cur cpos
        let inner ← splicedFrameScope (if (declAlignOf n).isNone then some blocks.size else none)
          (elabBlockScope ctx' (raws.extract (i + 1) raws.size))
        leaveBlockDecl saved
        let blocks := blocks ++ declScopeWrap n inner
        have _ : sliceWeight raws raws.size = 0 :=
          sliceWeight_end raws (Nat.le_refl _)
        have _ : slicePars raws raws.size = 0 :=
          slicePars_end raws (Nat.le_refl _)
        elabBlocksGo ctx' raws raws.size blocks #[] gen'
      else if let some f := flowDecl? ctx' n blocks.size then
        modify f
        elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else if n == "pause" then
        have _ := rest_measures raws (i + 1)
        let (⟨ctx', _⟩, blocks) ← closeBlockMacros ctx' blocks
        let ⟨stepCtx, hm⟩ : MCtx ctx' ←
          pure ⟨{ ctx' with stepBase := ctx'.stepBase + 1 }, rfl, rfl, rfl, rfl⟩
        let inner ← elabBlockScope stepCtx (raws.extract (i + 1) raws.size)
        let blocks := pauseCarrier raws i blocks (ctx'.stepBase + 2) inner
        have _ : sliceWeight raws raws.size = 0 :=
          sliceWeight_end raws (Nat.le_refl _)
        have _ : slicePars raws raws.size = 0 :=
          slicePars_end raws (Nat.le_refl _)
        elabBlocksGo ctx' raws raws.size blocks #[] gen'
      else if n == "note" then
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
          have _ := group_measures hg2 (show i ≤ j2 by omega)
          let ⟨noteCtx, hnc⟩ : { c : Ctx // c.envLimit = ctx'.envLimit
              ∧ noteFlag c = 0
              ∧ visParsGo c.user c.limit = visParsGo ctx'.user ctx'.limit
              ∧ visWeightGo c.user c.limit = visWeightGo ctx'.user ctx'.limit } ←
            pure ⟨{ ctx' with noteBody := true, notePos := some cpos },
              rfl, rfl, rfl, rfl⟩
          let inner ← elabBlockScope noteCtx nbody
          have hadv := advance_measures raws h (show i < j2 + 1 by omega)
          elabBlocksGo ctx' raws (j2 + 1)
            (blocks.push (.note inner)) #[] gen'
        | _ =>
          warnSkippedDecl ctx' "note" cpos
          have _ := advance_measures raws h (show i < i2 by omega)
          elabBlocksGo ctx' raws i2 blocks #[] gen'
      else if n == "framefoot" then
        -- beamer's `frame footer`: the footer's left slot from here on; empty clears it.
        let ⟨j, hjge⟩ : { x : Nat // i + 1 ≤ x } ←
          pure ⟨skipSpaces raws (i + 1), skipSpaces_ge raws (i + 1)⟩
        match raws[j]? with
        | some (.group fbody _) =>
          let blocks := blocks.push (.framefoot (← elabInlines ctx' fbody))
          have hadv := advance_measures raws h (show i < j + 1 by omega)
          elabBlocksGo ctx' raws (j + 1) blocks #[] gen'
        | _ =>
          diag ctx' .E0304 "'\\framefoot' needs one group of inline content" cpos
          elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else if flowStyleCtrl n then
        let (⟨styleCtx, _⟩, ⟨j, hj⟩, blocks, nextGen) ←
          flowStyleArm ctx' n raws (i + 1) (by omega) cpos blocks gen'
        have _ := advance_measures raws h (show i < j by omega)
        elabBlocksGo styleCtx raws j blocks #[] nextGen
      else if n == "define" then
        let ⟨(cmd?, k), hdef⟩ ← takeDefine ctx' raws (i + 1) cpos
        have hk : i + 1 ≤ k := hdef.1
        have _ : sliceWeight raws k ≤ sliceWeight raws (i + 1) :=
          sliceWeight_le raws hk
        have _ : slicePars raws k ≤ slicePars raws (i + 1) :=
          slicePars_le raws hk
        match hcm : cmd? with
        | some cmd =>
          if let some (lvl, parts) := secFmtDefine? cmd then
            -- Not a macro: a heading-number format declaration.
            applySecFmt lvl parts
            elabBlocksGo ctx' raws k blocks #[] gen'
          else
            have _ : rawWeightList cmd.body.toList + sliceWeight raws k + 2
                ≤ sliceWeight raws (i + 1) := (hdef.2 cmd hcm).1
            have _ : rawParsList cmd.body.toList + slicePars raws k
                ≤ slicePars raws (i + 1) := (hdef.2 cmd hcm).2
            let keep ← gateRedefB ctx' cmd
            if keep then
              -- Binding at the visibility boundary keeps expansion terminating.
              have _ := bindCmd_visPars ctx' cmd
              have _ := bindCmd_visWeight ctx' cmd
              have _ : (bindCmd ctx' cmd).envLimit = ctx'.envLimit
                  ∧ noteFlag (bindCmd ctx' cmd) = noteFlag ctx' := ⟨rfl, rfl⟩
              elabBlocksGo (bindCmd ctx' cmd) raws k blocks #[] gen'
            else
              elabBlocksGo ctx' raws k blocks #[] gen'
        | none =>
          elabBlocksGo ctx' raws k blocks #[] gen'
      else if counterCtrl n then
        let ⟨j2, hj2⟩ ← counterArm ctx' raws (i + 1) n cpos
        have _ := advance_measures raws h (show i < j2 by omega)
        elabBlocksGo ctx' raws j2 blocks #[] gen'
      else if n == "bibliographystyle" || n == Parse.citeSetupMark then
        let ⟨j, hjge⟩ : { x : Nat // i + 1 ≤ x } ←
          pure ⟨skipSpaces raws (i + 1), skipSpaces_ge raws (i + 1)⟩
        match raws[j]? with
        | some (.group body _) =>
          modify fun st => if n == Parse.citeSetupMark then
              { st with citeSetup := some ((st.citeSetup.getD #[]) ++ Parse.citeSetupOf body) }
            else { st with bibStyle := some (rawSrc body).trimAscii.toString }
          have hadv := advance_measures raws h (show i < j + 1 by omega)
          elabBlocksGo ctx' raws (j + 1) blocks #[] gen'
        | some (.word w _) =>
          modify fun st => { st with bibStyle := some w }
          have hadv := advance_measures raws h (show i < j + 1 by omega)
          elabBlocksGo ctx' raws (j + 1) blocks #[] gen'
        | _ =>
          diag ctx' .E0304 "'\\bibliographystyle' needs a {style} group" cpos
          elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else if n == Parse.markdownBibControl then
        let ⟨(j, list), hj⟩ ← markdownBibArm ctx' raws i cpos
        have hij : i < j := hj
        have _ := advance_measures raws h hij
        elabBlocksGo ctx' raws j ((list.map blocks.push).getD blocks) #[] gen'
      else if n == "bibliography" then
        -- classes.dtx: the list opens with an unnumbered `\refname` section.
        let ⟨j, hjge⟩ : { x : Nat // i + 1 ≤ x } ←
          pure ⟨skipSpaces raws (i + 1), skipSpaces_ge raws (i + 1)⟩
        match raws[j]? with
        | some (.group body _) =>
          let src := (rawSrc body).trimAscii.toString
          let style := (← get).bibStyle
          recordBibSpan ctx' src cpos
          let blocks := blocks.push
            (.section 1 true none #[.text ctx'.locale.references])
          let blocks := blocks.push (.bibliography src style #[])
          have hadv := advance_measures raws h (show i < j + 1 by omega)
          elabBlocksGo ctx' raws (j + 1) blocks #[] gen'
        | _ =>
          diag ctx' .E0304 "'\\bibliography' needs a {file} group" cpos
          elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else if let some mark := pageMark? n then
        elabBlocksGo ctx' raws (i + 1) (blocks.push mark) #[] gen'
      else if n == "block" then
        let j0 := skipSpaces raws (i + 1)
        have hj0 : i + 1 ≤ j0 := skipSpaces_ge raws (i + 1)
        let ⟨((before, primitive), jf), hjf⟩ : { t : (SymGlue × Bool) × Nat // i + 1 ≤ t.2 } ←
          if let some (.sym '[' _) := raws[j0]? then do
            let ⟨(optSrc, k), hk⟩ : { t : Array Raw × Nat // i + 1 ≤ t.2 } :=
              match hc : closeBracketFrom raws (j0 + 1) with
              | some c => ⟨(raws.extract (j0 + 1) c, c + 1), by
                  have := closeBracketFrom_ge hc; omega⟩
              | none => ⟨(raws.extract (j0 + 1) raws.size, raws.size), by omega⟩
            let opt ← blockOptions ctx' optSrc cpos
            pure ⟨(opt, skipSpaces raws k), by
              have := skipSpaces_ge raws k
              show i + 1 ≤ skipSpaces raws k
              omega⟩
          else
            pure ⟨(({}, false), j0), hj0⟩
        match hgf : raws[jf]? with
        | some (.group body _) =>
          have hbm := group_measures hgf (show i ≤ jf by omega)
          let inner ← elabBlockScope ctx' body
          have hadv := advance_measures raws h (show i < jf + 1 by omega)
          elabBlocksGo ctx' raws (jf + 1)
            (pushSkipBlock blocks (.spaced (Ir.Sourced.bare before) inner) primitive) #[] gen'
        | _ =>
          diag ctx' .E0304 "'\\block' needs a {body}" cpos
          elabBlocksGo ctx' raws (i + 1) blocks #[] gen'
      else
        let (⟨ctx', _⟩, blocks) ← blockControlContext ctx' n raws i blocks
        let (blocks, ⟨j, hij⟩) ← elabCtrlArm ctx' raws i h n cpos blocks
        have _ := advance_measures raws h hij
        elabBlocksGo ctx' raws j blocks #[] gen'
    | _ =>
      if cur.isEmpty && isSpaceOrPar raws[i] then
        elabBlocksGo ctx' raws (i + 1) blocks cur gen'
      else
        elabBlocksGo ctx' raws (i + 1) blocks (cur.push raws[i]) gen'
  else
    return (← flushPara ctx' blocks cur).2
termination_by (ctx.envLimit, noteFlag ctx,
  visParsGo ctx.user ctx.limit + slicePars raws i,
  visWeightGo ctx.user ctx.limit + sliceWeight raws i, 2, 0)
decreasing_by all_goals blocks_dec

/-- Elaborates a nested block scope, carrying the caller's pending text `cur`. -/
private def elabBlockScope (ctx : Ctx) (raws : Array Raw) (cur : Array Raw := #[]) :
    EM (Array Block) := do
  let ((savedBase, gen), savedLengths, ⟨body, _hsw, _hsp, _hsn⟩) ← openBlockScope ctx raws
  have _hw := sliceWeight_zero body
  have _hp := slicePars_zero body
  have _hw0 := sliceWeight_zero raws
  have _hp0 := slicePars_zero raws
  let ⟨innerCtx, _hm⟩ : MCtx ctx ←
    pure ⟨{ ctx with macroRoles := ctx.macroRoles.enter }, rfl, rfl, rfl, rfl⟩
  let blocks ← elabBlocksGo innerCtx body 0 #[] cur gen
  closeBlockScope ctx savedLengths savedBase blocks
termination_by (ctx.envLimit, noteFlag ctx,
  visParsGo ctx.user ctx.limit + slicePars raws 0,
  visWeightGo ctx.user ctx.limit + sliceWeight raws 0, 3, 0)
decreasing_by all_goals blocks_dec

end

public def elabBlocks (ctx : Ctx) (raws : Array Raw) : EM (Array Block) := do
  modify fun st => { st with spans := { st.spans with frames :=
    { st.spans.frames with nextBase := some 0 } } }
  elabBlockScope ctx raws

/-- Elaboration terminates: `elabBlocks` is a total function, so every run
has a result. -/
public theorem elaboration_total (ctx : Ctx) (raws : Array Raw) (st : ESt) :
    ∃ r, (elabBlocks ctx raws).run st = r :=
  ⟨_, rfl⟩

unseal blockMacroStep pauseCarrier carrierInGroup carrierToEnd altCarriers
unseal blockSkipTokens blockOptions pushSkipBlock
unseal lengthScopeKeys? openLengthScope closeLengthScope openBlockScope closeBlockScope
unseal closeBlockMacros blockControlContext
unseal splicedFrameScope setFrameSourceBase recordFrameSource keepFrameSourcePrefix
unseal declAlignOf
unseal flowStyleCtrl flowStyleArm
unseal takeArgs mkPara finishPara flushPara stripMathMeta
unseal elabMathInline elabMathEnv applyPalette parsePaletteOpts applyTokens parseColSpec
unseal titleBlocks
unseal skipOptArg takeTitleDecl
unseal sectionNumber columnWidth cmidRange trimRawEdges
unseal recordLabel refuseRedef dropEnvArgs skipReservedArgs takeDefine
unseal secFmtDefine? secFmtOfBody applySecFmt applyCounter counterCtrl counterArm
unseal theCounterLevel?
unseal declBlockOf isDeclBlock enterBlockDecl leaveBlockDecl declScopeWrap
unseal withBlockDecls wrapDeclAlign
unseal bodyIsBlock bodyIsBlockList bodyIsBlockOne overlayTakesBlocks
unseal renderedBuiltins structuralNames
unseal declCtrl runningCtrl titleCtrls overlayCtrls overlaySpecFor blockEnvs reservedEnv
unseal displayMathEnvs alignEnvs isMathEnv sectionLevel specWord? blockHeading?
unseal lookupUser lookupUserEnv isArgument isCenteringRaw isParRaw splitAtPars sizeParScope
unseal isColumnStray
unseal parFollows parPrecedes endPeAt displayAtBlock
unseal scanBracketArg
unseal nativeLinkedRow linkedRowChoice noteLinkedRow
unseal texGroup groupBlocks restoringGroup envGroup
unseal enterAppendicesIf leaveAppendices wrapScopedEnv
unseal thmOf? thmEnv thmOpen thmClose descItems coverItems ownBibList

private theorem elabInlines_word (ctx : Ctx) (w : String) (p : Pos)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : p.origins = []) :
    elabInlines ctx #[.word w p] =
      pure (if ctx.literalText then #[sourceInline ctx p (.text w)]
        else #[sourceInline ctx p (.text w)].map (mapSmartText ctx.literalWhen)) := by
  rw [elabInlines, elabInlinesCore, elabInlinesFrom]
  simp [inlineMacroAt, inlineMacroStep, MacroRoles.enter, MacroRoles.empty, Raw.origins?,
    relativeOrigins, hp, hm, flushText]
  rw [elabInlinesFrom_done_exact _ _ _ _ _ (by simp)]
  simp [inlineMacroAt, inlineMacroStep, flushText, mergeTexts, sourceInline, Ctx.sourceSpan]

private theorem elabInlines_recovered_head (ctx : Ctx) (name : String) (raws : Array Raw)
    (pos : Pos) (h : 0 < raws.size) (hr : raws[0] = .ctrl name pos)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hp : pos.origins = []) (hn : recoversInlineName ctx name = true) :
    elabInlines ctx raws = (do
      let out ← elabUnknownCtrl ctx raws 0 #[] "" name pos h
      pure (if ctx.literalText then out else out.map (mapSmartText ctx.literalWhen))) := by
  have he : ctx.macroRoles.enter = ctx.macroRoles := by rw [hm]; rfl
  have hr' : raws[0]? = some (.ctrl name pos) := by
    rw [Array.getElem?_eq_getElem h, hr]
  have hi : inlineMacroAt ctx.macroRoles raws 0 #[] "" = (ctx.macroRoles, #[], "") := by
    simp only [inlineMacroAt, hr', inlineMacroStep, Raw.origins?, hp, hm,
      MacroRoles.empty, relativeOrigins, List.map_nil]
    rfl
  rw [elabInlines, elabInlinesCore, he, elabInlinesFrom_unknown_exact _ _ _ _ _ _ _ h hr hn, hi]

private theorem elabInlines_group (ctx : Ctx) (body : Array Raw) (p : Pos)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : p.origins = []) :
    elabInlines ctx #[.group body p] = (do
      let inner ← inlineGroup ctx.palette (elabInlines ctx body)
      pure (if ctx.literalText then mergeTexts inner
        else (mergeTexts inner).map (mapSmartText ctx.literalWhen))) := by
  have he : ctx.macroRoles.enter = ctx.macroRoles := by rw [hm]; rfl
  have hi : inlineMacroAt ctx.macroRoles #[.group body p] 0 #[] "" =
      (ctx.macroRoles, #[], "") := by
    simp only [inlineMacroAt, show (#[Raw.group body p])[0]? =
      some (.group body p) from rfl, inlineMacroStep, Raw.origins?, hp, hm,
      MacroRoles.empty, relativeOrigins, List.map_nil]
    rfl
  have hd (inner : Array Inline) :
      elabInlinesFrom ctx #[.group body p] 1 inner "" = pure (mergeTexts inner) := by
    rw [elabInlinesFrom_done_exact _ _ _ _ _ (by simp)]
    simp [inlineMacroAt, inlineMacroStep, flushText, hm, MacroRoles.empty]
  rw [elabInlines, elabInlinesCore, he, elabInlinesFrom]
  simp only [hi]
  simp [flushText, hd, elabInlines]

private theorem elabInlines_recovered_args (ctx : Ctx) (name : String) (body : Array Raw)
    (p gp : Pos) (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hp : p.origins = []) (hn : recoversInlineName ctx name = true) :
    elabInlines ctx #[.ctrl name p, .group body gp] = (do
      warnUnknownCmd ctx name false p
      let inner ← inlineGroup ctx.palette (elabInlines ctx body)
      noteSalvage (unknownCmdDiag name (RunShape.one false)).1 name (rawSrc #[.group body gp])
      pure (if ctx.literalText then mergeTexts inner
        else (mergeTexts inner).map (mapSmartText ctx.literalWhen))) := by
  let xs : Array Raw := #[.ctrl name p, .group body gp]
  change elabInlines ctx xs = _
  rw [elabInlines_recovered_head ctx name xs p (by simp [xs]) rfl hm hp hn]
  have hs : skipSpaces xs 1 = 1 := by rw [skipSpaces]; rfl
  have hstar : skipStar xs 1 = 1 := by rfl
  have ho : skipOptionRuns xs 1 p = (1, none) := by
    rw [skipOptionRuns]
    have hc : scanBracketArg xs 1 p = .content := by
      unfold scanBracketArg
      rw [hs]
      rfl
    rw [hc]
  have ha : elabUnknownArgs ctx xs
      (skipSpaces xs (skipOptionRuns xs (skipStar xs (skipSpaces xs 1)) p).1)
      0 #[] "" false = (do
        let inner ← inlineGroup ctx.palette (elabInlines ctx body)
        pure (inner, "", ⟨2, by simp only [hs, hstar, ho]; omega⟩, 1, false)) := by
    have hi (j : Nat) (hj : j = 1) :
        elabUnknownArgs ctx xs j 0 #[] "" false = (do
          let inner ← inlineGroup ctx.palette (elabInlines ctx body)
          pure (inner, "", ⟨2, by omega⟩, 1, false)) := by
      subst j
      rw [elabUnknownArgs_last_group_exact _ _ _ _ _ _ _ _ rfl (by simp [xs])]
      simp [flushText]
    exact hi _ (by simp only [hs, hstar, ho])
  rw [elabUnknownCtrl]
  simp! only [Nat.reduceAdd, hs, hstar, ho, Prod.fst, Prod.snd]
  rw [ha]
  simp only [bind_assoc, pure_bind, Bool.and_false, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte]
  have hd (inner : Array Inline) :
      elabInlinesFrom ctx xs 2 inner "" = pure (mergeTexts inner) := by
    rw [elabInlinesFrom_done_exact _ _ _ _ _ (by simp [xs])]
    simp [inlineMacroAt, inlineMacroStep, xs, flushText, hm, MacroRoles.empty]
  simp [hd, xs, Parse.rawSrc, Parse.rawSrcList, Parse.rawSrcOne]

private theorem elabInlines_recovery_group (ctx : Ctx) (name : String)
    (body : Array Raw) (p gp : Pos)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hp : p.origins = []) (hgp : gp.origins = [])
    (hn : recoversInlineName ctx name = true) :
    elabInlines ctx #[.ctrl name p, .group body gp] = (do
      warnUnknownCmd ctx name false p
      let inner ← elabInlines ctx #[.group body gp]
      noteSalvage (unknownCmdDiag name {}).1 name (rawSrc #[.group body gp])
      pure inner) := by
  rw [elabInlines_recovered_args ctx name body p gp hm hp hn, elabInlines_group ctx body gp hm hgp]
  simp [unknownCmdDiag_shape_id]

private theorem elabInlines_recovered_group (ctx : Ctx) (name w : String) (p gp wp : Pos)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hp : p.origins = []) (hwp : wp.origins = [])
    (hn : recoversInlineName ctx name = true) :
    elabInlines ctx #[.ctrl name p, .group #[.word w wp] gp] = (do
      warnUnknownCmd ctx name false p
      noteSalvage (unknownCmdDiag name {}).1 name (rawSrc #[.group #[.word w wp] gp])
      let inner := if ctx.literalText then #[sourceInline ctx wp (.text w)]
        else #[sourceInline ctx wp (.text w)].map (mapSmartText ctx.literalWhen)
      pure (if ctx.literalText then inner
        else inner.map (mapSmartText ctx.literalWhen))) := by
  rw [elabInlines_recovered_args ctx name _ p gp hm hp hn, elabInlines_word ctx w wp hm hwp,
    inlineGroup_pure]
  have ms (x : Inline) : mergeTexts #[x] = #[x] := by cases x <;> rfl
  cases hl : ctx.literalText <;> simp [ms, unknownCmdDiag_shape_id]

private theorem mapSmartText_literal (ctx : Ctx) (p : Pos) (w : String)
    (hs : smartPunct w = w) :
    mapSmartText ctx.literalWhen (sourceInline ctx p (.text w)) =
      sourceInline ctx p (.text w) := by
  simp [sourceInline, mapSmartText, mapSmartTextList, punctuationInline, hs]

private theorem elabInlines_recovered_word (ctx : Ctx) (name w : String) (p gp wp : Pos)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hp : p.origins = []) (hwp : wp.origins = [])
    (hn : recoversInlineName ctx name = true) (hs : smartPunct w = w) :
    elabInlines ctx #[.ctrl name p, .group #[.word w wp] gp] = (do
      warnUnknownCmd ctx name false p
      noteSalvage (unknownCmdDiag name {}).1 name (rawSrc #[.group #[.word w wp] gp])
      pure #[sourceInline ctx wp (.text w)]) := by
  rw [elabInlines_recovered_group ctx name w p gp wp hm hp hwp hn]
  cases ctx.literalText <;> simp [mapSmartText_literal ctx wp w hs]

private theorem trimParaList_word (ctx : Ctx) (p : Pos) (w : String)
    (he : w.isEmpty = false)
    (hl : String.ofList (w.toList.dropWhile (· == ' ')) = w)
    (ht : w.trimAscii.isEmpty = false)
    (hr : String.ofList ((w.toList.reverse.dropWhile (· == ' ')).reverse) = w) :
    (trimParaList false #[]
      (trimParaList true #[] [sourceInline ctx p (.text w)]).1.toList).1 =
        #[sourceInline ctx p (.text w)] := by
  simp [trimParaList, trimParaOne, sourceInline, he, hl, ht, hr]

private theorem finishPara_note (code : DiagCode) (name text : String)
    (inner : Array Inline) :
    (do noteSalvage code name text; finishPara inner) =
    (do let para ← finishPara inner; noteSalvage code name text; pure para) := by
  by_cases ht : text.trimAscii.isEmpty = true <;>
    by_cases hi : (trimParaList false #[]
      (trimParaList true #[] inner.toList).1.toList).1.isEmpty = true <;>
    simp [noteSalvage, finishPara, ht, hi]; rfl

private theorem mkPara_group (ctx : Ctx) (body : Array Raw) (gp : Pos) :
    mkPara ctx #[.group body gp] = (do
      let inner ← elabInlines ctx #[.group body gp]
      finishPara inner) := by
  rw [mkPara]
  simp only [ForIn.forIn]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  rfl

private theorem mkPara_recovery_group (ctx : Ctx) (name : String)
    (body : Array Raw) (p gp : Pos)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hp : p.origins = []) (hgp : gp.origins = [])
    (hn : recoversInlineName ctx name = true) :
    mkPara ctx #[.ctrl name p, .group body gp] = (do
      warnUnknownCmd ctx name false p
      let para ← mkPara ctx #[.group body gp]
      noteSalvage (unknownCmdDiag name {}).1 name (rawSrc #[.group body gp])
      pure para) := by
  rw [mkPara]
  simp only [ForIn.forIn]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [
    show (#[Raw.ctrl name p, Raw.group body gp]).back? =
      some (Raw.group body gp) from rfl, pure_bind,
    show (#[Raw.ctrl name p, Raw.group body gp]).isEmpty = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  rw [elabInlines_recovery_group ctx name body p gp hm hp hgp hn, mkPara_group]
  simp only [bind_assoc, pure_bind, finishPara_note]

private theorem mkPara_recovered_word (ctx : Ctx) (name w : String) (p gp wp : Pos)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hp : p.origins = []) (hwp : wp.origins = [])
    (hn : recoversInlineName ctx name = true) (hs : smartPunct w = w)
    (he : w.isEmpty = false)
    (hl : String.ofList (w.toList.dropWhile (· == ' ')) = w)
    (ht : w.trimAscii.isEmpty = false)
    (hr : String.ofList ((w.toList.reverse.dropWhile (· == ' ')).reverse) = w) :
    mkPara ctx #[.ctrl name p, .group #[.word w wp] gp] = (do
      warnUnknownCmd ctx name false p
      noteSalvage (unknownCmdDiag name {}).1 name (rawSrc #[.group #[.word w wp] gp])
      return some (paraUnder (← get).scope.lang
        (Ir.paraAt (← get).scope.blockDecls #[sourceInline ctx wp (.text w)]))) := by
  rw [mkPara]
  simp only [ForIn.forIn]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [
    show (#[Raw.ctrl name p, Raw.group #[Raw.word w wp] gp]).back? =
      some (Raw.group #[Raw.word w wp] gp) from rfl, pure_bind]
  simp only [show (#[Raw.ctrl name p, Raw.group #[Raw.word w wp] gp]).isEmpty = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  rw [elabInlines_recovered_word ctx name w p gp wp hm hp hwp hn hs]
  simp only [bind_assoc, pure_bind]
  rw [finishPara]
  rw [trimParaList_word ctx wp w he hl ht hr]
  rfl

private theorem blockMacroStep_idle (ctx : Ctx) (st : ESt) (raws : Array Raw)
    (i : Nat) (blocks : Array Block) (cur : Array Raw)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hi : i < raws.size) (hp : (raws[i]).origins? = some []) :
    blockMacroStep ctx st st.flowGen raws i blocks cur =
      pure (⟨ctx, rfl, rfl, rfl, rfl⟩, blocks, cur) := by
  simp only [blockMacroStep, flowMCtx_idle,
    blockMacroKinds, Array.getElem?_eq_getElem hi, hp, hm, MacroRoles.empty]
  simp [relativeOrigins, show ¬ i ≥ raws.size by omega,
    closeBlockFrameSources, commonOrigins, moveMacroRuns, closeMacroRuns, hm, MacroRoles.empty]
  cases ctx
  cases hm
  rfl

private theorem flushPara_empty (ctx : Ctx) (blocks : Array Block)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) :
    flushPara ctx blocks #[] = pure (⟨ctx, rfl, rfl, rfl, rfl⟩, blocks) := by
  simp [flushPara, hm, MacroRoles.empty, carryDecls_empty]
  cases ctx
  cases hm
  rfl

private theorem flushPara_pending (ctx : Ctx) (blocks : Array Block) (cur : Array Raw)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (he : cur.isEmpty = false) :
    flushPara ctx blocks cur = (do
      let para ← mkPara ctx cur
      let (bs, pal) ← carryDecls ctx cur (match para with | some b => blocks.push b | none => blocks)
      pure (⟨{ ctx with palette := pal }, rfl, rfl, rfl, rfl⟩, bs)) := by
  cases ctx
  cases hm
  simp only [flushPara, he, Bool.false_eq_true, ↓reduceIte, Array.filter_empty,
    Array.map_empty]

private theorem blockMacroStep_done (ctx : Ctx) (st : ESt) (raws : Array Raw)
    (i : Nat) (blocks : Array Block) (cur : Array Raw)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hi : raws.size ≤ i) :
    blockMacroStep ctx st st.flowGen raws i blocks cur = (do
      let (ready, bs) ← flushPara ctx blocks cur
      pure (ready, bs, #[])) := by
  rw [blockMacroStep, flowMCtx_idle]
  simp only [↓reduceIte, blockMacroKinds,
    Array.getElem?_eq_none hi, hi]
  by_cases he : cur.isEmpty = true
  · have hz : cur = #[] := Array.isEmpty_iff.mp he
    subst cur
    rw [flushPara_empty ctx blocks hm]
    simp [hm, MacroRoles.empty, closeBlockFrameSources, commonOrigins,
      moveMacroRuns, closeMacroRuns]
    cases ctx
    cases hm
    rfl
  · have hf : cur.isEmpty = false := Bool.eq_false_iff.mpr he
    rw [flushPara_pending ctx blocks cur hm hf]
    simp only [bind_assoc, pure_bind]
    simp [hm, MacroRoles.empty, closeBlockFrameSources, commonOrigins,
      moveMacroRuns, closeMacroRuns]

private theorem elabBlocksGo_done (ctx : Ctx) (st : ESt) (raws : Array Raw) (i : Nat)
    (blocks : Array Block) (cur : Array Raw)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hi : raws.size ≤ i) :
    (elabBlocksGo ctx raws i blocks cur st.flowGen).run st =
      ((do
        let (_, bs) ← flushPara ctx blocks cur
        pure bs) : EM (Array Block)).run st := by
  rw [elabBlocksGo]
  simp only [show ¬ i < raws.size from Nat.not_lt.mpr hi, ↓reduceDIte, pure_bind]
  change ((do
    let (⟨next, _⟩, bs, cs) ← blockMacroStep ctx st st.flowGen raws i blocks cur
    return (← flushPara next bs cs).2) : EM _).run st = _
  rw [blockMacroStep_done ctx st raws i blocks cur hm hi]
  simp only [bind_assoc, pure_bind]
  by_cases he : cur.isEmpty = true
  · have hz : cur = #[] := Array.isEmpty_iff.mp he
    subst cur
    rw [flushPara_empty ctx blocks hm]
    simp only [pure_bind]
    rw [flushPara_empty ctx blocks hm]
    rfl
  · rw [flushPara_pending ctx blocks cur hm (Bool.eq_false_iff.mpr he)]
    simp only [bind_assoc, pure_bind]
    simp only [flushPara_empty, hm, pure_bind]

private theorem run_get (k : ESt → EM α) (st : ESt) :
    ((do let x ← get; k x) : EM α).run st = (k st).run st := by rfl

private theorem elabBlocksGo_recovery_ctrl (ctx : Ctx) (st : ESt) (name : String)
    (body : Array Raw) (p gp : Pos) (blocks : Array Block)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : p.origins = [])
    (hb : isBlockStart ctx name #[.ctrl name p, .group body gp] 0 #[] = false) :
    (elabBlocksGo ctx #[.ctrl name p, .group body gp]
      0 blocks #[] st.flowGen).run st =
    (elabBlocksGo ctx #[.ctrl name p, .group body gp]
      1 blocks #[.ctrl name p] st.flowGen).run st := by
  rw [elabBlocksGo, run_get]
  rw [blockMacroStep_idle ctx st _ 0 blocks #[] hm (by simp)
    (by simpa [Raw.origins?] using hp)]
  simp only [pure_bind]
  simp [hb]

private theorem elabBlocksGo_recovery_group (ctx : Ctx) (st : ESt) (name : String)
    (body : Array Raw) (p gp : Pos) (blocks : Array Block)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hp : gp.origins = []) :
    (elabBlocksGo ctx #[.ctrl name p, .group body gp]
      1 blocks #[.ctrl name p] st.flowGen).run st =
    (elabBlocksGo ctx #[.ctrl name p, .group body gp]
      2 blocks #[.ctrl name p, .group body gp] st.flowGen).run st := by
  rw [elabBlocksGo, run_get]
  rw [blockMacroStep_idle ctx st _ 1 blocks #[.ctrl name p] hm (by simp)
    (by simpa [Raw.origins?] using hp)]
  have ha : isArgument #[.ctrl name p] = true := by
    rw [isArgument, Parse.endsInArgument]
    simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    simp [Std.Legacy.Range.size, List.forIn_cons]
  simp [ha]

private theorem elabBlocksGo_plain_group (ctx : Ctx) (st : ESt)
    (body : Array Raw) (gp : Pos) (blocks : Array Block)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hp : gp.origins = []) (hpar : body.any isParRaw = false)
    (hblock : (body.any isCenteringRaw || bodyIsBlock body) = false) :
    (elabBlocksGo ctx #[.group body gp] 0 blocks #[] st.flowGen).run st =
      ((do
        let para ← mkPara ctx #[.group body gp]
        pure (match para with | some b => blocks.push b | none => blocks)) :
        EM (Array Block)).run st := by
  rw [elabBlocksGo, run_get]
  rw [blockMacroStep_idle ctx st _ 0 blocks #[] hm (by simp)
    (by simpa [Raw.origins?] using hp)]
  simp only [pure_bind]
  simp [hpar, hblock]
  rw [elabBlocksGo_done ctx st _ 1 blocks _ hm (by simp)]
  rw [flushPara_pending ctx blocks _ hm rfl, carryDecls_quiet ctx _ (by simp [quietRaw])]
  simp only [bind_assoc, pure_bind]
  rfl

private theorem elabBlocksGo_recovery (ctx : Ctx) (st : ESt) (name : String)
    (body : Array Raw) (p gp : Pos) (blocks : Array Block)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hp : p.origins = []) (hgp : gp.origins = [])
    (hn : recoversInlineName ctx name = true)
    (hb : isBlockStart ctx name #[.ctrl name p, .group body gp] 0 #[] = false) :
    (elabBlocksGo ctx #[.ctrl name p, .group body gp]
      0 blocks #[] st.flowGen).run st =
      ((do
        warnUnknownCmd ctx name false p
        let para ← mkPara ctx #[.group body gp]
        noteSalvage (unknownCmdDiag name {}).1 name (rawSrc #[.group body gp])
        pure (match para with | some b => blocks.push b | none => blocks)) :
        EM (Array Block)).run st := by
  rw [elabBlocksGo_recovery_ctrl ctx st name body p gp blocks hm hp hb,
    elabBlocksGo_recovery_group ctx st name body p gp blocks hm hgp,
    elabBlocksGo_done ctx st _ 2 blocks _ hm (by simp),
    flushPara_pending ctx blocks _ hm rfl,
    carryDecls_quiet ctx _ (by simp [quietRaw, carriesPar_recovers ctx name hn]),
    mkPara_recovery_group ctx name body p gp hm hp hgp hn]
  simp only [bind_assoc, pure_bind]

private def enterBodyScope (st : ESt) : ESt :=
  {st with spans := {st.spans with frames :=
    {st.spans.frames with base := some 0, nextBase := none}}}

private theorem elabBlocks_scope (ctx : Ctx) (st : ESt) (raws : Array Raw)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hlen : openLengthScope ctx raws =
      (#[], ⟨raws, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)) :
    (elabBlocks ctx raws).run st =
      ((do
        let bs ← elabBlocksGo ctx raws 0 #[] #[] st.flowGen
        closeBlockScope ctx #[] st.spans.frames.base bs) :
        EM (Array Block)).run (enterBodyScope st) := by
  have henter : {ctx with macroRoles := ctx.macroRoles.enter} = ctx := by
    cases ctx
    cases hm
    rfl
  rw [elabBlocks, elabBlockScope]
  simp only [henter, openBlockScope, hlen, bind_assoc, pure_bind]
  rfl

private theorem warnUnknownCmd_scope (ctx : Ctx) (name : String) (p : Pos) (st : ESt) :
    ((warnUnknownCmd ctx name false p).run (enterBodyScope st)).2 =
      enterBodyScope ((warnUnknownCmd ctx name false p).run st).2 := by
  cases he : st.runShapes.find? (·.1 == "ctrl:" ++ name) with
  | none =>
    simp [warnUnknownCmd, enterBodyScope, bumpRunShape, warnOnceState, he]
    rfl
  | some entry =>
    rcases entry with ⟨key, old, idx⟩
    simp [warnUnknownCmd, enterBodyScope, bumpRunShape, warnOnceState, he]
    rfl

private theorem warnUnknownCmd_flowGen (ctx : Ctx) (name : String) (p : Pos) (st : ESt) :
    ((warnUnknownCmd ctx name false p).run st).2.flowGen = st.flowGen := by
  change (warnOnceState ctx ("ctrl:" ++ name) (unknownCmdDiag name (RunShape.one false)).1
    (unknownCmdDiag name (RunShape.one false)).2.1 p
    (unknownCmdDiag name (RunShape.one false)).2.2
    ((unknownCmdDiag name (RunShape.one false)).1 == .W0301 &&
      Compat.styInternal ctx.file name) (bumpRunShape name ("ctrl:" ++ name) false st)).flowGen =
    st.flowGen
  unfold warnOnceState bumpRunShape
  split <;> rfl

private theorem warnUnknownCmd_frameBase (ctx : Ctx) (name : String) (p : Pos) (st : ESt) :
    ((warnUnknownCmd ctx name false p).run st).2.spans.frames.base = st.spans.frames.base := by
  change (warnOnceState ctx ("ctrl:" ++ name) (unknownCmdDiag name (RunShape.one false)).1
    (unknownCmdDiag name (RunShape.one false)).2.1 p
    (unknownCmdDiag name (RunShape.one false)).2.2
    ((unknownCmdDiag name (RunShape.one false)).1 == .W0301 &&
      Compat.styInternal ctx.file name) (bumpRunShape name ("ctrl:" ++ name) false st)).spans.frames.base =
    st.spans.frames.base
  unfold warnOnceState bumpRunShape
  split <;> rfl

private theorem closeBlockScope_note (ctx : Ctx) (base : Option Nat) (blocks : Array Block)
    (code : DiagCode) (name text : String) :
    (do noteSalvage code name text; closeBlockScope ctx #[] base blocks) =
    (do let bs ← closeBlockScope ctx #[] base blocks; noteSalvage code name text; pure bs) := by
  by_cases ht : text.trimAscii.isEmpty = true <;>
    simp [noteSalvage, closeBlockScope, closeLengthScope, setFrameSourceBase, ht]; rfl

/-- Runs `content` between an unhandled control's warning and its recovery
record. -/
public def withControlRecovery (ctx : Ctx) (name : String) (pos : Pos) (operands : Array Raw)
    (content : EM α) : EM α := do
  warnUnknownCmd ctx name false pos
  let value ← content
  noteSalvage (unknownCmdDiag name {}).1 name (rawSrc operands)
  pure value

attribute [local irreducible] elabBlocks mkPara closeBlockScope
  warnUnknownCmd noteSalvage in
private theorem elabBlocks_recovery_group_exact (ctx : Ctx) (name : String)
    (body : Array Raw) (pos groupPos : Pos)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hp : pos.origins = []) (hgp : groupPos.origins = [])
    (hn : recoversInlineName ctx name = true)
    (hb : isBlockStart ctx name #[.ctrl name pos, .group body groupPos] 0 #[] = false)
    (hpar : body.any isParRaw = false)
    (hblock : (body.any isCenteringRaw || bodyIsBlock body) = false) :
    elabBlocks ctx #[.ctrl name pos, .group body groupPos] =
      withControlRecovery ctx name pos #[.group body groupPos]
        (elabBlocks ctx #[.group body groupPos]) := by
  funext st
  change (elabBlocks ctx _).run st = _
  have hlen : openLengthScope ctx #[.ctrl name pos, .group body groupPos] =
      (#[], ⟨#[.ctrl name pos, .group body groupPos],
        Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩) := by
    rw [openLengthScope, lengthScopeKeys?]
    rfl
  have hplain : openLengthScope ctx #[.group body groupPos] =
      (#[], ⟨#[.group body groupPos], Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩) := by
    rw [openLengthScope, lengthScopeKeys?]
    rfl
  rw [elabBlocks_scope ctx st _ hm hlen]
  change (closeBlockScope ctx #[] st.spans.frames.base
      ((elabBlocksGo ctx _ 0 #[] #[] (enterBodyScope st).flowGen).run (enterBodyScope st)).1).run
        ((elabBlocksGo ctx _ 0 #[] #[] (enterBodyScope st).flowGen).run (enterBodyScope st)).2 = _
  rw [elabBlocksGo_recovery ctx (enterBodyScope st) name body pos groupPos #[] hm hp hgp hn hb]
  change ((do
    warnUnknownCmd ctx name false pos
    let para ← mkPara ctx #[.group body groupPos]
    noteSalvage (unknownCmdDiag name {}).1 name (rawSrc #[.group body groupPos])
    closeBlockScope ctx #[] st.spans.frames.base
      (match para with | some b => #[b] | none => #[])) :
    EM (Array Block)).run (enterBodyScope st) = _
  simp only [closeBlockScope_note]
  unfold withControlRecovery
  change _ = ((do
    let bs ← elabBlocks ctx #[.group body groupPos]
    noteSalvage (unknownCmdDiag name {}).1 name (rawSrc #[.group body groupPos])
    pure bs) : EM (Array Block)).run ((warnUnknownCmd ctx name false pos).run st).2
  change _ = ((do
    noteSalvage (unknownCmdDiag name {}).1 name (rawSrc #[.group body groupPos])
    pure ((elabBlocks ctx #[.group body groupPos]).run
      ((warnUnknownCmd ctx name false pos).run st).2).1) : EM (Array Block)).run
      ((elabBlocks ctx #[.group body groupPos]).run
        ((warnUnknownCmd ctx name false pos).run st).2).2
  rw [elabBlocks_scope ctx _ _ hm hplain, warnUnknownCmd_flowGen,
    warnUnknownCmd_frameBase]
  change _ = ((do
    let bs ← closeBlockScope ctx #[] st.spans.frames.base
      ((elabBlocksGo ctx #[.group body groupPos] 0 #[] #[]
        st.flowGen).run (enterBodyScope ((warnUnknownCmd ctx name false pos).run st).2)).1
    noteSalvage (unknownCmdDiag name {}).1 name (rawSrc #[.group body groupPos])
    pure bs) : EM (Array Block)).run
      ((elabBlocksGo ctx #[.group body groupPos] 0 #[] #[]
        st.flowGen).run (enterBodyScope ((warnUnknownCmd ctx name false pos).run st).2)).2
  rw [← warnUnknownCmd_scope]
  have hflow : ((warnUnknownCmd ctx name false pos).run (enterBodyScope st)).2.flowGen =
      st.flowGen := warnUnknownCmd_flowGen ctx name pos (enterBodyScope st)
  rw [← hflow]
  rw [elabBlocksGo_plain_group ctx _ body groupPos #[] hm hgp hpar hblock]
  rfl

private theorem elabBlocksGo_recovered_ctrl (ctx : Ctx) (st : ESt) (name w : String) (p gp wp : Pos)
    (blocks : Array Block)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hp : p.origins = [])
    (hb : isBlockStart ctx name #[.ctrl name p, .group #[.word w wp] gp] 0 #[] = false) :
    (elabBlocksGo ctx #[.ctrl name p, .group #[.word w wp] gp]
      0 blocks #[] st.flowGen).run st =
    (elabBlocksGo ctx #[.ctrl name p, .group #[.word w wp] gp]
      1 blocks #[.ctrl name p] st.flowGen).run st := by
  rw [elabBlocksGo, run_get]
  rw [blockMacroStep_idle ctx st _ 0 blocks #[] hm (by simp) (by simpa [Raw.origins?] using hp)]
  simp only [pure_bind]
  simp [hb]

private theorem elabBlocksGo_recovered_group (ctx : Ctx) (st : ESt) (name w : String) (p gp wp : Pos)
    (blocks : Array Block)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hp : gp.origins = []) :
    (elabBlocksGo ctx #[.ctrl name p, .group #[.word w wp] gp]
      1 blocks #[.ctrl name p] st.flowGen).run st =
    (elabBlocksGo ctx #[.ctrl name p, .group #[.word w wp] gp]
      2 blocks #[.ctrl name p, .group #[.word w wp] gp] st.flowGen).run st := by
  rw [elabBlocksGo, run_get]
  rw [blockMacroStep_idle ctx st _ 1 blocks #[.ctrl name p] hm (by simp)
    (by simpa [Raw.origins?] using hp)]
  have ha : isArgument #[.ctrl name p] = true := by
    rw [isArgument, Parse.endsInArgument]
    simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    simp [Std.Legacy.Range.size, List.forIn_cons]
  simp [ha]

private theorem elabBlocksGo_recovered_word (ctx : Ctx) (st : ESt) (name w : String) (p gp wp : Pos)
    (blocks : Array Block)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hp : p.origins = []) (hgp : gp.origins = []) (hwp : wp.origins = [])
    (hn : recoversInlineName ctx name = true) (hs : smartPunct w = w)
    (he : w.isEmpty = false)
    (hl : String.ofList (w.toList.dropWhile (· == ' ')) = w)
    (ht : w.trimAscii.isEmpty = false)
    (hr : String.ofList ((w.toList.reverse.dropWhile (· == ' ')).reverse) = w)
    (hb : isBlockStart ctx name #[.ctrl name p, .group #[.word w wp] gp] 0 #[] = false) :
    (elabBlocksGo ctx #[.ctrl name p, .group #[.word w wp] gp]
      0 blocks #[] st.flowGen).run st =
    ((do
      warnUnknownCmd ctx name false p
      noteSalvage (unknownCmdDiag name {}).1 name (rawSrc #[.group #[.word w wp] gp])
      return blocks.push (paraUnder (← get).scope.lang
        (Ir.paraAt (← get).scope.blockDecls #[sourceInline ctx wp (.text w)]))) :
      EM (Array Block)).run st := by
  rw [elabBlocksGo_recovered_ctrl ctx st name w p gp wp blocks hm hp hb,
    elabBlocksGo_recovered_group ctx st name w p gp wp blocks hm hgp,
    elabBlocksGo_done ctx st _ 2 blocks _ hm (by simp),
    flushPara_pending ctx blocks _ hm rfl,
    carryDecls_quiet ctx _ (by simp [quietRaw, carriesPar_recovers ctx name hn]),
    mkPara_recovered_word ctx name w p gp wp hm hp hwp hn hs he hl ht hr]
  simp only [bind_assoc, pure_bind]

private theorem elabBlocksGo_recovered_shape (ctx : Ctx) (st : ESt) (name w : String) (p gp wp : Pos)
    (blocks : Array Block)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hp : p.origins = []) (hgp : gp.origins = []) (hwp : wp.origins = [])
    (hn : recoversInlineName ctx name = true) (hs : smartPunct w = w)
    (he : w.isEmpty = false)
    (hl : String.ofList (w.toList.dropWhile (· == ' ')) = w)
    (ht : w.trimAscii.isEmpty = false)
    (hr : String.ofList ((w.toList.reverse.dropWhile (· == ' ')).reverse) = w)
    (hb : isBlockStart ctx name #[.ctrl name p, .group #[.word w wp] gp] 0 #[] = false) :
    ∃ lang decls, ((elabBlocksGo ctx #[.ctrl name p, .group #[.word w wp] gp]
      0 blocks #[] st.flowGen).run st).1 =
      blocks.push (paraUnder lang (Ir.paraAt decls #[sourceInline ctx wp (.text w)])) := by
  rw [elabBlocksGo_recovered_word ctx st name w p gp wp blocks hm hp hgp hwp hn hs he hl ht hr hb]
  exact ⟨_, _, rfl⟩

private theorem closeBlockScope_value (ctx : Ctx) (st : ESt) (base : Option Nat)
    (bs : Array Block) :
    ((closeBlockScope ctx #[] base bs).run st).1 = bs := by
  rw [closeBlockScope, closeLengthScope]
  rfl

private theorem elabBlocks_recovered_shape (ctx : Ctx) (st : ESt) (name w : String) (p gp wp : Pos)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles)
    (hp : p.origins = []) (hgp : gp.origins = []) (hwp : wp.origins = [])
    (hn : recoversInlineName ctx name = true) (hs : smartPunct w = w)
    (he : w.isEmpty = false)
    (hl : String.ofList (w.toList.dropWhile (· == ' ')) = w)
    (ht : w.trimAscii.isEmpty = false)
    (hr : String.ofList ((w.toList.reverse.dropWhile (· == ' ')).reverse) = w)
    (hb : isBlockStart ctx name #[.ctrl name p, .group #[.word w wp] gp] 0 #[] = false) :
    ∃ lang decls, ((elabBlocks ctx #[.ctrl name p, .group #[.word w wp] gp]).run st).1 =
      #[paraUnder lang (Ir.paraAt decls #[sourceInline ctx wp (.text w)])] := by
  let xs : Array Raw := #[.ctrl name p, .group #[.word w wp] gp]
  have henter : {ctx with macroRoles := ctx.macroRoles.enter} = ctx := by
    cases ctx
    cases hm
    rfl
  have hopen : openLengthScope ctx xs =
      (#[], ⟨xs, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩) := by
    rw [openLengthScope, lengthScopeKeys?]
    rfl
  change ∃ lang decls, ((elabBlocks ctx xs).run st).1 = _
  rw [elabBlocks, elabBlockScope]
  simp only [henter, openBlockScope, hopen, bind_assoc, pure_bind]
  let entered : ESt := {st with spans := {st.spans with frames :=
    {st.spans.frames with base := some 0, nextBase := none}}}
  change ∃ lang decls, (((do
    let bs ← elabBlocksGo ctx xs 0 #[] #[] entered.flowGen
    closeBlockScope ctx #[] st.spans.frames.base bs) : EM (Array Block)).run entered).1 = _
  change ∃ lang decls, ((closeBlockScope ctx #[] st.spans.frames.base
    ((elabBlocksGo ctx xs 0 #[] #[] entered.flowGen).run entered).1).run
      ((elabBlocksGo ctx xs 0 #[] #[] entered.flowGen).run entered).2).1 = _
  rw [closeBlockScope_value]
  exact elabBlocksGo_recovered_shape ctx entered name w p gp wp #[] hm hp hgp hwp hn hs he hl ht hr hb

private theorem mapInlines_wrapDecls (f : Inline → Inline) (ds : List Ir.Decl)
    (xs : Array Inline) (h : Ir.mapInlines f xs = xs) :
    Ir.mapInlines f (Ir.wrapDecls ds xs) = Ir.wrapDecls ds xs := by
  induction ds with
  | nil => simpa only [Ir.wrapDecls_exact] using h
  | cons d ds ih =>
    rw [Ir.wrapDecls_exact]
    change Ir.mapInlines f (d.wrap (Ir.wrapDecls ds xs)) = d.wrap (Ir.wrapDecls ds xs)
    cases d with
    | style st =>
      rw [Ir.Decl.wrap_exact]
      change #[Inline.styled st (Ir.mapInlines f (Ir.wrapDecls ds xs))] = _
      rw [ih]
    | color c name =>
      rw [Ir.Decl.wrap_exact]
      change #[Inline.colored c name (Ir.mapInlines f (Ir.wrapDecls ds xs))] = _
      rw [ih]

private theorem mapInlines_paraAt (f : Inline → Inline) (ds : List Ir.Decl)
    (xs : Array Inline) (h : Ir.mapInlines f xs = xs) :
    Ir.mapInlines f (Ir.paraAt ds xs) = Ir.paraAt ds xs := by
  unfold Ir.paraAt
  dsimp only
  split
  · change #[Inline.styled (.size "normalsize")
      (Ir.mapInlines f (Ir.wrapDecls (Ir.dropShadowedSizes ds) xs))] = _
    rw [mapInlines_wrapDecls f _ xs h]
  · exact mapInlines_wrapDecls f _ xs h

private theorem mapBlocks_paraUnder (f : Inline → Inline) (lang : Option String)
    (xs : Array Inline) (h : Ir.mapInlines f xs = xs) :
    Ir.mapBlocks f #[paraUnder lang xs] = #[paraUnder lang xs] := by
  cases lang with
  | none => change #[Block.para (Ir.mapInlines f xs)] = _; rw [h]; rfl
  | some tag =>
    simp only [paraUnder, Ir.langWrap_exact]
    change #[Block.para #[.styled (.lang tag) (Ir.mapInlines f xs)]] = _
    rw [h]

private theorem resolve_recovered_para (ctx : Ctx) (wp : Pos) (w : String)
    (lang : Option String) (ds : List Ir.Decl) (loc : Locale) (table : Ir.RefTable) :
    Ir.resolveRefs loc table
      #[paraUnder lang (Ir.paraAt ds #[sourceInline ctx wp (.text w)])] =
      #[paraUnder lang (Ir.paraAt ds #[sourceInline ctx wp (.text w)])] := by
  rw [Ir.resolveRefs_agree]
  apply mapBlocks_paraUnder
  apply mapInlines_paraAt
  rfl

private theorem recovered_para_census (ctx : Ctx) (wp : Pos) (w : String)
    (lang : Option String) (ds : List Ir.Decl) :
    Ir.blocksText #[paraUnder lang (Ir.paraAt ds #[sourceInline ctx wp (.text w)])] = w := by
  have hw : Ir.plainText #[sourceInline ctx wp (.text w)] = w := by
    simp [sourceInline, Ir.plainText, Ir.plainTextList, Ir.plainTextOne]
  cases lang with
  | none =>
    change "" ++ Ir.plainText (Ir.paraAt ds #[sourceInline ctx wp (.text w)]) = w
    rw [String.empty_append, Ir.paraAt_text ds _, hw]
  | some tag =>
    change "" ++ Ir.plainText (Ir.langWrap tag
      (Ir.paraAt ds #[sourceInline ctx wp (.text w)])) = w
    rw [String.empty_append, Ir.langWrap_text tag _, Ir.paraAt_text ds _, hw]

private theorem numbered_recovered_para (lang : Option String) (xs : Array Inline) :
    Ir.numberFloats #[paraUnder lang xs] = #[paraUnder lang xs] := by
  cases lang <;> exact Ir.numberFloats_para_exact _

private theorem referent_recovered_para (keys : Ir.ReferentKeys) (lang : Option String)
    (xs : Array Inline) : Ir.anchorReferents keys #[paraUnder lang xs] = #[paraUnder lang xs] := by
  cases lang <;> exact Ir.anchorReferents_para_exact keys _

/-- A declared value as its author would write it. -/
private def renderValue : Decl.Value → String
  | .str s => s
  | .dim sp => s!"{sp.toPtString}pt"
  | .int n => toString n
  | .ident s => s
  | .block src => "{" ++ src ++ "}"
  | .color r g b => ({ r, g, b } : Color).hex
  | .cmyk c m y k => s!"cmyk({c}, {m}, {y}, {k})"
  | .glue g => Ir.dumpGlue g

/-- The page's leading factor: the body's declared skip stretched by
`\linespread`, composed at the end of each `\page` block. -/
private def composeLeading (spec : PageSpec) : PageSpec :=
  match spec.bodySkip with
  | none => { spec with leading := spec.spread }
  | some d =>
    let body := spec.fontSize
    let ld := (d * 1000 + Dim.pt 1 / 2) / Dim.pt 1
    let sz := max 1 ((body * 1000 + Dim.pt 1 / 2) / Dim.pt 1)
    { spec with
      leading := ((ld * (spec.spread : Int) * 1000 + sz * 600) / (sz * 1200)).toNat
      skips := some (Ir.setSkip spec.skipScale "normalsize" (Ir.skipRowOf (d * 1000) body)) }

/-- A page box from four numbers in PDF points, its lower-left corner first however written. -/
private def pageBoxOf (kind : BoxKind) (s : String) (span : Option Span) : Option PageBox := do
  let toSp (m : Int) (sc : Nat) : Int :=
    let v := ((m.natAbs * 65536 * 2 + sc) / (2 * max 1 sc) : Nat)
    if m < 0 then -(v : Int) else v
  let nums ← ((s.splitOn " ").filter (!·.isEmpty)).mapM Decl.parseDecimal
  let [a, b, c, d] := nums.map fun (m, sc) => toSp m sc | none
  some { kind, x0 := min a c, y0 := min b d, x1 := max a c, y1 := max b d, span }

private def applyPage (ctx : Ctx) (spec : PageSpec) (entries : Array Decl.Entry)
    (pos : Pos) (tokens : Array (String × SymGlue) := #[]) : PageSpec × Array PEvent := Id.run do
  -- A page dimension may be glue over tokens with nothing font-relative in it.
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
    -- geometry's `textwidth` and `textheight` centre the block (§5.2).
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
    -- `leading` is `\linespread`'s stretch, composed when the block ends.
    | "leading", .int n => spec := { spec with spread := n.toNat * 1000 }
    | "leading", .dim d =>
      -- A bare decimal like 1.15 reads as points; the factor is meant.
      spec := { spec with spread := (d * 1000 / pt 1).toNat }
    | "leading", .ident f =>
      -- A decimal without a unit arrives as a name.
      match Decl.parseDecimal f with
      | some (m, s) => spec := { spec with spread := (m * 1000 / s).toNat }
      | none => evs := say evs .E0323 s!"'leading' in '\\page' expects a factor like 1.15, got '{f}'"
    | "baselineskip", v =>
      if let some d := asDim v then
        if 0 < d then spec := { spec with bodySkip := some d }
        else
          evs := say evs .E0323 "'baselineskip' in '\\page' expects a positive dimension"
      else evs := evs.push (.say (Decl.wrongType ctx.file "page" "baselineskip" "a dimension" v pos))
    | "parskip", .glue g => spec := { spec with parskip := some g }
    | "parskip", .dim d => spec := { spec with parskip := some { width := Dim.Length.ofSp d } }
    | "fontsize", .dim d =>
      -- From 1pt the default ladder's headings stand in order (`Layout.heading_hierarchy`).
      if d ≥ Dim.pt 1 then
        spec := { spec with fontSize := d }
      else
        evs := say evs .E0323 "'fontsize' in '\\page' expects a dimension of at least 1pt"
    | "measure", .ident v =>
      match v with
      | "free" => spec := { spec with measureChecked := false }
      | "checked" => spec := { spec with measureChecked := true }
      | _ =>
        evs := say evs .E0323 s!"'measure' in '\\page' expects 'checked' or 'free', got '{v}'"
    | "bleed", .int 0 => spec := { spec with bleed := 0 }
    | "bleed", v =>
      if let some d := asDim v then spec := { spec with bleed := d }
      else evs := evs.push (.say (Decl.wrongType ctx.file "page" "bleed" "a dimension" v pos))
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
    -- `rule` reads y up from the page's top-left; it is stored y down.
    | "rule", .str s | "front-rule", .str s =>
      match s.splitOn ";" |>.map (·.trimAscii.toString) with
      | [x, y, w, h, c] =>
        match [x, y, w, h].map fun p => (Decl.parseValue p tokens).bind asDim with
        | [some x, some y, some w, some h] =>
          spec := { spec with drawn := spec.drawn.push ⟨x, -(y + h), w, h, c, e.key == "front-rule"⟩ }
        | _ => evs := say evs .E0323 s!"'{e.key}' in '\\page' expects four dimensions, got '{s}'"
      | _ =>
        let msg := s!"'{e.key}' in '\\page' expects \"x; y; width; height; colour\", got '{s}'"
        evs := say evs .E0323 msg
    | "cropbox", v | "bleedbox", v | "trimbox", v | "artbox", v =>
      let kind : BoxKind := match e.key with
        | "cropbox" => .crop
        | "bleedbox" => .bleed
        | "trimbox" => .trim
        | _ => .art
      match v with
      | .str s =>
        match pageBoxOf kind s (some ⟨ctx.file, pos⟩) with
        | some b => spec := { spec with boxes := (spec.boxes.filter (·.kind != kind)).push b }
        | none =>
          evs := say evs .E0323 s!"'{e.key}' in '\\page' expects four numbers in PDF points, got '{s}'"
      | v => evs := evs.push (.say (Decl.wrongType ctx.file "page" e.key
          "four quoted numbers in PDF points" v pos))
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
    -- lineno's `\linenumbers`; `modulo` is its `\modulolinenumbers[n]`.
    | "linenumbers", .ident v =>
      match v with
      | "on" | "true" => spec := { spec with linenumbers := some true }
      | "off" | "false" => spec := { spec with linenumbers := some false }
      | _ =>
        evs := say evs .E0323 s!"'linenumbers' in '\\page' expects on or off, got '{v}'"
    | "modulo", .int n =>
      if n ≥ 1 then spec := { spec with lineModulo := some n.toNat }
      else evs := say evs .E0323 "'modulo' in '\\page' expects a count of at least 1"
    -- `furnituregap` is in ink terms; `headsep` and `footskip` keep their baselines.
    | "furnituregap", v =>
      if let some d := asDim v then spec := { spec with furnitureGap := some d }
      else evs := evs.push (.say (Decl.wrongType ctx.file "page" "furnituregap" "a dimension" v pos))
    | "headsep", v =>
      if let some d := asDim v then spec := { spec with headsep := some d }
      else evs := evs.push (.say (Decl.wrongType ctx.file "page" "headsep" "a dimension" v pos))
    | "footskip", v =>
      if let some d := asDim v then spec := { spec with footskip := some d }
      else evs := evs.push (.say (Decl.wrongType ctx.file "page" "footskip" "a dimension" v pos))
    | "bottom", .ident v =>
      match v with
      | "flush" => spec := { spec with flushBottom := some true }
      | "ragged" => spec := { spec with flushBottom := some false }
      | _ =>
        evs := say evs .E0323 s!"'bottom' in '\\page' expects flush or ragged, got '{v}'"
    | key, v =>
      if key == "header" || key == "footer" then
        let cmd := if key == "header" then "\\runninghead" else "\\runningfoot"
        evs := say evs .E0327 s!"'{key}' is not a '\\page' key"
          (help := s!"{cmd}\{...} declares it; \\hfill pushes content to the right")
      else if pageKeys.contains key then
        let expected := if key == "size" then "a page size name"
          else if key == "measure" then "'checked' or 'free'"
          else if key == "marks" then "'cut' or 'none'"
          else if key == "modulo" then "a count of at least 1"
          else if key == "bottom" then "'flush' or 'ragged'"
          else if key == "rule" || key == "front-rule" then "\"x; y; width; height; colour\""
          else if key == "hyphenate" || key == "justify" || key == "protrusion"
            || key == "expansion" || key == "numbers"
            || key == "linenumbers" then "on or off"
          else "a dimension"
        evs := evs.push (.say (Decl.wrongType ctx.file "page" key expected v pos))
      else
        -- The help lists the native keys; LaTeX spellings and riders stay unlisted.
        evs := evs.push (.say (Decl.unknownKey ctx.file "page" key
          (pageKeys.filter
            (!["headsep", "footskip", "textwidth", "textheight", "baselineskip",
               "mark-gap", "mark-thickness", "modulo", "rule", "front-rule", "cropbox", "bleedbox",
               "trimbox", "artbox", "bottom"].contains ·)) pos))
    -- A clean count means the entry applied; a `rule` adds, so it overwrites nothing.
    if evs.size == before && e.key != "rule" && e.key != "front-rule" then
      evs := evs.push (.scalar "page" e.key (renderValue e.value) pos)
  return (composeLeading spec, evs)

private def fontSlot? (name : String) : Option Nat :=
  match name with
  | "body" | "rm" => some 0
  | "sans" | "sf" => some 1
  | "mono" | "tt" => some 2
  | _ => none

/-- A `body.bold`-style key as `(slot, weight, italic)`; a series code such as
`sans.sb.italic` names any other weight. -/
private def fontVariantKey? (key : String) : Option (Nat × Nat × Bool) :=
  let seriesKey (s : String) (italic : Bool) : Option (Nat × Bool) :=
    match Ir.Weight.parseSeries s with
    -- A width half names an axis the engine lacks, so the key is unknown.
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

/-- A declared family's variant spelling past the slot, such as `sb.italic`. -/
private def familyVariantKey? (variant : List String) : Option (Nat × Bool) :=
  (fontVariantKey? (String.intercalate "." ("body" :: variant))).map fun (_, w, i) => (w, i)

/-- The face a `\fonts` key declares for the unused-setting judge: its slot's, a declared family's,
or the math face's for an alphabet source; a directory declares none. -/
private def faceKeyOf? (key : String) : Option String :=
  match fontSlot? key, key.splitOn "." with
  | some 0, _ => some "body"
  | some 1, _ => some "sans"
  | some _, _ => some "mono"
  | none, "family" :: name :: _ => some s!"family.{name}"
  | none, _ =>
    match fontVariantKey? key with
    | some (0, _, _) => some "body"
    | some (1, _, _) => some "sans"
    | some _ => some "mono"
    | none => if key == "math" || (Math.MathAlphabet.sourceKey? key).isSome then some "math" else none

/-- Applies `\fonts{...}`: family names per slot, variant faces and font
directories. -/
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
    -- fontspec's `\newfontfamily`: `family.<cmd>` and its `family.<cmd>.<variant>` faces.
    | key, v@(.str f) =>
      match key.splitOn "." with
      | ["family", name] => spec := spec.declareFamily name f
      | "family" :: name :: variant =>
        match spec.familySlot name, familyVariantKey? variant with
        | some slot, some (w, i) => spec := spec.declareFace (slot, w, i) f
        | _, _ =>
          evs := evs.push (.say (Decl.unknownKey ctx.file "fonts" key
            (fontKeys ++ ["family.<name>", "family.<name>.<variant>"]) pos))
      | _ =>
        match fontVariantKey? key with
        | some variant => spec := spec.declareFace variant f
        | none =>
          match Math.MathAlphabet.sourceKey? key with
          | some _ =>
            evs := evs.push (.say (Decl.wrongType ctx.file "fonts" key "sym or text" v pos))
          | none =>
            evs := evs.push (.say (Decl.unknownKey ctx.file "fonts" key
              (fontKeys ++ ["<slot>.upright/.bold/.italic/.bolditalic",
                "<slot>.<series>[.italic] (series ul/el/l/sl/m/sb/b/eb/ub)",
                "family.<name>"]) pos))
    | key, v =>
      match Math.MathAlphabet.sourceKey? key with
      | some a =>
        match v with
        | .ident source =>
          match Math.MathAlphabetSource.ofName? source with
          | some value =>
            spec := { spec with mathSources := spec.mathSources.set a value }
          | none =>
            evs := evs.push (.say (Decl.wrongType ctx.file "fonts" key
              "sym or text" v pos))
        | _ =>
          evs := evs.push (.say (Decl.wrongType ctx.file "fonts" key
            "sym or text" v pos))
      | none =>
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
    -- Only slot and alphabet settings are scalars that report an overwrite.
    if evs.size == before then
      let aliases := [("rm", "body"), ("sf", "sans"), ("tt", "mono")]
      let canonical := (aliases.lookup e.key).getD e.key
      if ["body", "sans", "mono", "math"].contains canonical ||
          (Math.MathAlphabet.sourceKey? canonical).isSome then
        evs := evs.push (.scalar "fonts" canonical (renderValue e.value) pos)
      if let some face := faceKeyOf? e.key then
        evs := evs.push (.setting (.face face) pos)
  return (spec, evs)

private def styleKeys : List String :=
  ["font", "before", "after", "rule", "rule-position", "rule-thickness", "marker", "indent", "gap",
   "align", "separator", "rule-above", "rule-above-skip", "rule-above-gap",
   "rule-below", "rule-below-gap", "rule-below-skip", "author-font",
   "author-strut", "body-size", "hover", "focus", "motion", "slot", "color", "shape"] ++
    Ir.listSetKeys

/-- The keys of a block's `shape = {...}`. -/
private def blockShapeKeys : List String :=
  ["before", "title", "untitled", "between", "after", "whole", "edge"]

private def blockEdgeKeys : List String :=
  ["span", "side", "width", "sep", "hang", "color", "height", "depth"]

/-- Reads a title metric: terms in `lh` (the title's `\baselineskip`), `cap`
(its cap height) and fixed lengths, joined by `+` and `-`. -/
private def blockMetricOf (src : String) : Option BlockMetric :=
  let terms := ((src.replace " - " " + -").splitOn "+").map (·.trimAscii.toString)
  terms.foldlM (init := ({} : BlockMetric)) fun m t =>
    let milli (v : String) : Option Int :=
      (Decl.parseDecimal v).map fun (x, sc) => x * 1000 / (sc : Int)
    if t.isEmpty then none
    else if t.endsWith "lh" then
      (milli (t.dropEnd 2).toString).map fun v => { m with lead := m.lead + v }
    else if t.endsWith "cap" then
      (milli (t.dropEnd 3).toString).map fun v => { m with cap := m.cap + v }
    else (Decl.parseLength t).bind fun l =>
      if l.em == 0 && l.ex == 0 then some { m with sp := m.sp + l.sp } else none

/-- Reads a block's `shape = {...}`, the native spelling of a beamer block
template. -/
private def blockShapeOf (ctx : Ctx) (src : String) (pos : Pos) : EM (Option BlockShape) := do
  let unbrace (src : String) : String :=
    let t := src.trimAscii.toString
    if t.startsWith "{" && t.endsWith "}" && t.length ≥ 2
    then ((t.drop 1).dropEnd 1).toString else t
  let bad (what : String) : EM Unit :=
    diag ctx .E0323 s!"a block's 'shape' has {what}" pos
      (help := "write shape = { before = medskipamount, title = box strut, edge = { span = title, side = left, width = 2pt, sep = 4pt, hang = true, color = accent } }")
  let lengthOf (v : String) : Option Length :=
    match Decl.parseValue v ctx.tokens.entries with
    | some (.glue g) => if g.stretch == {} && g.shrink == {} && !g.fil then some g.width else none
    | some (.dim d) => some (Dim.Length.ofSp d)
    | _ =>
      match Decl.parseLengthExpr ctx.tokens.entries v with
      | .ok g => if g.stretch == {} && g.shrink == {} && !g.fil then some g.width else none
      | .error _ => none
  let skipsOf (v : String) : Option (Array BlockSkip) :=
    let items := ((unbrace v).splitOn "+").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
    items.toArray.mapM fun item =>
      if ["smallskipamount", "medskipamount", "bigskipamount"].contains item then
        some (.register item)
      else (Decl.parseGlue item).map .glue
  let mut sh : BlockShape := {}
  let mut ok := true
  for entry in Decl.splitEntries (unbrace src) do
    match Decl.splitEntry entry with
    | none => ok := false; bad s!"an entry that is not key = value: {entry.quote}"
    | some (k, v) =>
      let vt := v.trimAscii.toString
      match k with
      | "before" | "between" | "after" =>
        match skipsOf vt with
        | some sk =>
          if k == "before" then sh := { sh with before := sk }
          else if k == "between" then sh := { sh with between := sk }
          else sh := { sh with after := sk }
        | none => ok := false; bad s!"'{k}' that is not skip registers or glues joined by +: {vt.quote}"
      | "title" =>
        let words := (vt.splitOn " ").filter (!·.isEmpty)
        if words == ["plain"] then sh := { sh with title := {} }
        else if words.all (["box", "strut", "parskip"].contains ·) then
          sh := { sh with title := { boxed := words.contains "box", strut := words.contains "strut",
                                     parskip := words.contains "parskip" } }
        else ok := false; bad s!"a 'title' that is not plain or flags among box, strut, parskip: {vt.quote}"
      | "untitled" =>
        if vt == "box" then sh := { sh with bare := none }
        else if vt.startsWith "{" then
          let mut bare : BlockBare := {}
          for sub in Decl.splitEntries (unbrace vt) do
            match Decl.splitEntry sub with
            | some (uk, uv) =>
              match uk, skipsOf uv.trimAscii.toString with
              | "before", some sk => bare := { bare with before := sk }
              | "between", some sk => bare := { bare with between := sk }
              | _, _ =>
                ok := false
                bad s!"an 'untitled' entry that is not before or between skips: {sub.quote}"
            | none => ok := false; bad s!"an 'untitled' entry that is not key = value: {sub.quote}"
          sh := { sh with bare := some bare }
        else ok := false; bad s!"an 'untitled' that is neither box nor a group of skips: {vt.quote}"
      | "whole" =>
        if vt == "parskip" then sh := { sh with whole := some true }
        else if vt == "plain" then sh := { sh with whole := some false }
        else ok := false; bad s!"a 'whole' that is neither parskip nor plain: {vt.quote}"
      | "edge" =>
        let mut span : Option BlockSpan := none
        let mut side : FlushSide := .left
        let mut width : Option Length := none
        let mut sep : Length := {}
        let mut hang := true
        let mut color : Option (Ir.Color × Option ColorRef) := none
        let mut height : Option BlockMetric := none
        let mut depth : Option BlockMetric := none
        for sub in Decl.splitEntries (unbrace v) do
          match Decl.splitEntry sub with
          | none => ok := false; bad s!"an edge entry that is not key = value: {sub.quote}"
          | some (ek, ev) =>
            let et := ev.trimAscii.toString
            match ek with
            | "span" =>
              if et == "title" then span := some .title
              else if et == "whole" then span := some .whole
              else ok := false; bad s!"an edge 'span' that is neither title nor whole: {et.quote}"
            | "side" =>
              if et == "left" then side := .left
              else if et == "right" then side := .right
              else ok := false; bad s!"an edge 'side' that is neither left nor right: {et.quote}"
            | "width" =>
              match lengthOf et with
              | some l => width := some l
              | none => ok := false; bad s!"an edge 'width' that is not a length: {et.quote}"
            | "sep" =>
              match lengthOf et with
              | some l => sep := l
              | none => ok := false; bad s!"an edge 'sep' that is not a length: {et.quote}"
            | "hang" =>
              if et == "true" then hang := true
              else if et == "false" then hang := false
              else ok := false; bad s!"an edge 'hang' that is neither true nor false: {et.quote}"
            | "color" =>
              match ← readColor ctx ctx.palette none et pos with
              | .resolved c token => color := some (c, token)
              | .rejected => ok := false
              | .missing =>
                ok := false
                diag ctx .E0326 s!"'{et}' is not in the palette" pos
            | "height" | "depth" =>
              match blockMetricOf et with
              | some m => if ek == "height" then height := some m else depth := some m
              | none =>
                ok := false
                bad s!"an edge '{ek}' that is not a sum of lh, cap and fixed lengths: {et.quote}"
            | _ =>
              ok := false
              modify fun st' => { st' with
                diags := st'.diags.push (Decl.unknownKey ctx.file "block edge" ek blockEdgeKeys pos) }
        let reach : Option BlockReach := match height, depth, span with
          | none, none, _ => some .box
          | some a, some b, some _ => some (.lines a b)
          | _, _, _ => none
        match span, width, color, reach with
        | some sp, some w, some (c, n), some r =>
          let wg : SymGlue := { width := w }
          let sg : SymGlue := { width := sep }
          let edge : BlockEdge :=
            { span := sp, side := side, width := wg, sep := sg, hang := hang, color := c, name := n
              reach := r }
          sh := { sh with edges := sh.edges.push edge }
        | _, _, _, none =>
          ok := false
          bad "an edge reaching by lines with no 'height' or 'depth'"
        | _, _, _, _ => ok := false; bad "an edge without its span, width or color"
      | _ =>
        ok := false
        modify fun st' => { st' with
          diags := st'.diags.push (Decl.unknownKey ctx.file "block shape" k blockShapeKeys pos) }
  -- Lines reach by their struts: unstrutted, they stand as tall as their ink.
  if sh.edges.any (·.reach matches .lines ..) && !(sh.title.boxed && sh.title.strut) then
    ok := false
    bad "an edge reaching by lines beside a title that is not a box its struts bound"
  if sh.edges.any (fun e => e.span == .whole && e.reach matches .lines ..) &&
      (sh.whole.isSome || sh.edges.any fun e => e.span == .whole && e.reach matches .lines .. && !e.hang) then
    ok := false
    bad "an edge reaching by the block's lines inside its line or beside a box holding title and body"
  return if ok then some sh else none

/-- The keys of one `slot = {...}` group in `\style{titlepage}`. -/
private def titleSlotKeys : List String :=
  ["part", "set", "content", "font", "align", "width", "size", "anchor", "at",
   "xshift", "yshift", "inner-sep"]

/-- The keys of one independently styled part in a title slot. -/
private def titlePartKeys : List String :=
  ["set", "content", "font", "align", "size", "leading", "new-line", "before"]

/-- Applies `\style{element}{...}`, each entry read against the tokens
declared so far. -/
private def applyStyle (ctx : Ctx) (styles : Styles) (element src : String) (pos : Pos) :
    EM Styles := do
  unless styleableElements.contains element || ctx.user.any (·.name == element) do
    let lists := "{" ++ ",".intercalate ("list" :: Ir.listSetKinds) ++ "}{,1..4}"
    let named := styleableElements.filterMap fun e =>
      if e == "section" then some "{,sub,subsub}section"
      else if ["subsection", "subsubsection", "heading5", "heading6"].contains e then none
      else if e == "heading1" then some "heading{1,5,6}"
      else if e == "itemize" then some lists
      else if Ir.listSetElements.contains e then none
      else some e
    diag ctx .E0328 s!"'{element}' is not a styleable element or a '\\define'd name" pos
      (help := s!"elements: {String.intercalate ", " named}")
    return styles
  let mut st : ElementStyle := (styles.find? element).getD {}
  let inlineOf (src : String) : EM (Option (Array Inline)) := do
    let inner := if src.startsWith "{" && src.endsWith "}" && src.length ≥ 2
      then (src.drop 1).dropEnd 1 |>.toString else src
    let fragmentCtx := ctx.atCall "style" pos
    let (toks, _) := Lex.lex ctx.file inner
    let (raws, _) := Parse.parse ctx.file toks
    -- Warn-once keys are read, never merged back: this site drops the notes.
    let inherited := (ctx.user.extract 0 ctx.limit).toList.map (·.name)
    let (raws, ds, _) := Compat.rewrite ctx.file raws
      (warned := (← get).warnedUnknown) (inherited := inherited)
    let ds := (ds.filter (·.severity != .note)).map fun d =>
      { d with span := some (fragmentCtx.sourceSpan pos) }
    modify fun st => { st with diags := st.diags ++ ds }
    return some (← elabInlines fragmentCtx raws)
  let lengthOf (key src : String) : EM (Option SymGlue) := do
    -- The length grammar spells tokens bare, so the backslash is dropped.
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
      -- premise: titleHeadingChecks — no title-page site reads these keys
      if element == "titlepage" && Ir.titleUnreadKeys.contains key then
        warnOnce ctx ("style:titlepage:" ++ key) .W0104
          s!"'{key}' has no meaning on the title page; the title is set without it" pos
          (help := "draw rules around the title with rule-above, rule-below or separator")
      -- premise: none — no frame-title site reads these keys, so builds with and without one agree
      if element == "frametitle" && styleKeys.contains key && key != "font" then
        warnOnce ctx ("style:frametitle:" ++ key) .W0104
          s!"'{key}' has no meaning on a frame title; the title is set without it" pos
          (help := "a frame title reads its font, under a frame-title bar")
        continue
      if element == "frametitle" && key == "font" then
        if restatesPlainTitle valueSrc then
          modify fun st => { st with spans := { st.spans with
            frameTitleRestated := st.spans.frameTitleRestated <|> some (ctx.sourceSpan pos) } }
        else
          modify fun st => { st with spans := { st.spans with
            frameTitleFont := st.spans.frameTitleFont <|> some (ctx.sourceSpan pos) } }
      -- premise: listSpacingStyleChecks — no list site reads these keys there
      if (Ir.listSetOnly.contains element && styleKeys.contains key &&
          !Ir.listSetKeys.contains key) ||
          (Ir.listSetKeys.contains key && !Ir.listSetElements.contains element) then
        warnOnce ctx ("style:" ++ element ++ ":" ++ key) .W0104
          s!"'{key}' has no meaning on '{element}'; the element is set without it" pos
          (help := "a list's spacing reads topsep, partopsep, itemsep and parsep on its \
list, kind or level, and its other keys on the kind's own element")
        continue
      -- premise: blockStyleKeyChecks — no block site reads these keys
      if Ir.blockStyleElements.contains element && styleKeys.contains key &&
          !Ir.blockStyleKeys.contains key && key != "slot" then
        warnOnce ctx ("style:" ++ element ++ ":" ++ key) .W0104
          s!"'{key}' has no meaning on a beamer block; the block is set without it" pos
          (help := "a block reads its title's font and its template's shape")
        continue
      let asInline : EM (Option (Array Inline)) := inlineOf valueSrc
      let asLength : EM (Option SymGlue) := lengthOf key valueSrc
      let asColor : EM (Option (Ir.Color × Option Ir.ColorRef)) := do
        match ← readColor ctx ctx.palette none valueSrc pos with
        | .resolved c token => return some (c, token)
        | .rejected => return none
        | .missing =>
          diag ctx .E0326 s!"'{valueSrc}' is not in the palette" pos
          return none
      match key with
      | "topsep" | "partopsep" | "itemsep" | "parsep" =>
        if valueSrc.trimAscii.toString == "none" then st := { st with list := st.list.put key none }
        else if let some g ← asLength then st := { st with list := st.list.put key (some g) }
      | "font" => st := { st with font := ← asInline }
      | "marker" =>
        st := { st with marker := (← asInline).map fun body =>
          #[.located (ctx.sourceSpan pos) body] }
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
      | "shape" =>
        if !Ir.blockStyleElements.contains element then
          diag ctx .E0323 s!"'shape' in '\\style' belongs to a beamer block, not '{element}'" pos
            (help := "write \\style{block}{ shape = {...} }")
        else if let some sh ← blockShapeOf ctx valueSrc pos then
          st := { st with shape := some sh }
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
        | "left" => st := { st with align := some .left }
        | "center" => st := { st with align := some .center }
        | "right" => st := { st with align := some .right }
        | v =>
          diag ctx .E0323 s!"'align' in '\\style' expects left, center, or right, got '{v}'" pos
      | "hover" =>
        if let some v ← asColor then st := { st with hover := some v }
      | "focus" =>
        if let some v ← asColor then st := { st with focus := some v }
      | "color" =>
        if let some v ← asColor then st := { st with color := some v }
      | "motion" =>
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
  noteSetting ctx (.style element) pos
  return styles.declare element st

/-- Applies `\chrome{...}`, merging each declared footer slot onto the chrome
already declared. -/
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
                | "framenumber" | "slidenumber" => some .frameNumber
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
      else if key == "standout-note" then
        match valueSrc.trimAscii.toString with
        | "true" | "false" =>
          let enabled := valueSrc.trimAscii.toString == "true"
          chrome := { chrome with standoutNote := some enabled }
          evs := evs.push (.scalar "chrome" key (toString enabled) pos)
          evs := evs.push (.declared "chrome" key)
        | _ =>
          evs := say evs .E0321
            s!"cannot read 'standout-note' in '\\chrome': {valueSrc.quote}"
            (help := "standout-note = true or false")
      else
        evs := evs.push (.say (Decl.unknownKey ctx.file "chrome" key ["footer", "standout-note"] pos))
  return (chrome, evs)

/-- The bare comma lists `\output` takes. -/
private inductive OutputList where
  | formats
  | profiles
  | schemes

/-- Applies `\output{...}`; an entry without `=` continues the list last
opened. -/
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
  let addProfile (o : OutputSpec) (evs : Array PEvent) (p : String) :
      OutputSpec × Array PEvent :=
    if PdfContract.Profile.names.contains p then
      (o.addProfile p, evs)
    else
      (o, say evs .E0321 s!"'{p}' is not a conformance profile"
        (help := s!"profiles: {String.intercalate ", " PdfContract.Profile.names}"))
  let addScheme (o : OutputSpec) (evs : Array PEvent) (v : String) :
      OutputSpec × Array PEvent :=
    match Scheme.all.find? (·.name == v) with
    | some sc =>
      let l := o.schemes.getD #[]
      ({ o with schemes := some (if l.contains sc then l else l.push sc) }, evs)
    | none =>
      (o, say evs .E0321 s!"'{v}' is not a colour scheme"
        (help := s!"schemes: {String.intercalate ", " (Scheme.all.map (·.name))}"))
  let addListed (o : OutputSpec) (evs : Array PEvent) (l : OutputList) (v : String) :
      OutputSpec × Array PEvent :=
    match l with
    | .formats => addFormat o evs v
    | .profiles => addProfile o evs v
    | .schemes => addScheme o evs v
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
    | some ("schemes", v) =>
      inList := some .schemes
      let (o', evs') := addScheme { o with schemes := some #[] } evs v
      o := o'
      evs := evs'
    | some ("css", v) =>
      inList := none
      if ["own", "bulma", "none"].contains v then
        o := { o with css := some v }
        evs := evs.push (.scalar "output" "css" v pos)
      else
        evs := say evs .E0321 s!"'{v}' is not a stylesheet mode"
          (help := "css: own (the engine's sheet), bulma (Bulma's class names, styled by the sheet stylesheet = ... declares, within the page's CSS subset), none (markup only)")
    | some ("stylesheet", v) =>
      inList := none
      let v := match Decl.stringBody? v.toList with
        | some body => String.ofList body
        | none => v
      o := { o with stylesheet := some v }
      evs := evs.push (.scalar "output" "stylesheet" v pos)
    | some ("md", v) =>
      inList := none
      let v := match Decl.stringBody? v.toList with
        | some body => String.ofList body
        | none => v
      o := { o with md := some v }
      evs := evs.push (.scalar "output" "md" v pos)
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
        (["formats", "profiles", "schemes", "css", "stylesheet", "md"] ++ OutputContract.facts) pos))
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

/-- Applies `\pdfmeta{...}`, the PDF document information. -/
private def applyMeta (ctx : Ctx) (m0 : Meta) (entries : Array Decl.Entry)
    (pos : Pos) : Meta × Array PEvent := Id.run do
  let mut m := m0
  let mut evs : Array PEvent := #[]
  for e in entries do
    let before := evs.size
    match e.key, e.value with
    | "title", .str s => m := { m with title := some (Ir.metaClean s) }
    | "language", .str s =>
      if (Locale.forTag s).isNone then
        evs := evs.push (.say (Diag.of .W0368
          s!"no locale for language '{s}'; English captions and patterns stand in" (some ⟨ctx.file, pos⟩)
          (help := some "the engine ships locale records for: en, fr, de")))
      m := { m with language := some s }
    | "author", .str s => m := { m with author := some (Ir.metaClean s) }
    | "subject", .str s => m := { m with subject := some (Ir.metaClean s) }
    | "keywords", .str s => m := { m with keywords := some (Ir.metaClean s) }
    | "url", .str s => m := { m with url := some s }
    | "image", .str s => m := { m with image := some s }
    | "favicon", .str s => m := { m with favicon := some s }
    | "version", .str s =>
      if s == "1.6" || s == "1.7" || s == "2.0" then
        m := { m with pdfVersion := some s, versionSpan := some ⟨ctx.file, pos⟩ }
      else
        evs := evs.push (.say (diagOf ctx .E0323
          s!"'version' in '\\pdfmeta' expects \"1.6\", \"1.7\" or \"2.0\", got '{s}'" (some pos) none))
    | "standard", .str s =>
      if s == "X-4" then m := { m with pdfx := some s }
      else
        evs := evs.push (.say (diagOf ctx .E0323
          s!"'standard' in '\\pdfmeta' expects \"X-4\", got '{s}'" (some pos) none))
    | "intent", .str s =>
      m := { m with intent := some { m.intent.getD {} with profile := s, span := some ⟨ctx.file, pos⟩ } }
    | "intent-condition", .str s =>
      m := { m with intent := some { m.intent.getD {} with condition := some s } }
    | "intent-info", .str s => m := { m with intent := some { m.intent.getD {} with info := some s } }
    | "intent-registry", .str s =>
      m := { m with intent := some { m.intent.getD {} with registry := some s } }
    | "intent-components", .str c =>
      match c.toNat? with
      | some n =>
        if n == 1 || n == 3 || n == 4 then
          m := { m with intent := some { m.intent.getD {} with components := some n } }
        else
          evs := evs.push (.say (diagOf ctx .E0323
            s!"'intent-components' in '\\pdfmeta' expects 1, 3 or 4, got {n}" (some pos) none))
      | none =>
        evs := evs.push (.say (diagOf ctx .E0323
          s!"'intent-components' in '\\pdfmeta' expects 1, 3 or 4, got '{c}'" (some pos) none))
    | "intent-components", .int n =>
      if n == 1 || n == 3 || n == 4 then
        m := { m with intent := some { m.intent.getD {} with components := some n.toNat } }
      else
        evs := evs.push (.say (diagOf ctx .E0323
          s!"'intent-components' in '\\pdfmeta' expects 1, 3 or 4, got {n}" (some pos) none))
    | "created", .str s | "modified", .str s =>
      if (PdfDate.parse? s).isSome then
        m := if e.key == "created" then { m with created := some s } else { m with modified := some s }
      else
        evs := evs.push (.say (diagOf ctx .E0323
          s!"'{e.key}' in '\\pdfmeta' expects a date, 2026-01-31 or 2026-01-31T09:00:00Z, got '{s}'"
          (some pos) none))
    | "trapped", .ident w | "trapped", .str w =>
      let v := w.toLower
      if v == "true" || v == "false" then
        m := { m with trapped := some (v == "true"), trappedUnknownAt := none }
      else if v == "unknown" then
        m := { m with trapped := none, trappedUnknownAt := some ⟨ctx.file, pos⟩ }
      else
        evs := evs.push (.say (diagOf ctx .E0323
          s!"'trapped' in '\\pdfmeta' expects true, false or unknown, got '{v}'" (some pos) none))
    | key, v =>
      if metaKeys.contains key then
        let expected := if key == "trapped" then "true, false or unknown"
          else if key == "intent-components" then "1, 3 or 4" else "a string"
        evs := evs.push (.say (Decl.wrongType ctx.file "pdfmeta" key expected v pos))
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

/-- Reads `\assert{...}`, a layout invariant checked against the shipped
pages. -/
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

/-- One scanned preamble declaration, its payload raw until `applyDecl`
elaborates it in order. -/
public inductive PDecl where
  | docclass (options : Option String) (cls : Option String) (pos : Pos)
  | pictures (src : Option String) (pos : Pos)
  | figures (src : Option String) (pos : Pos)
  | defineCmd (decl : Array Raw) (pos : Pos)
  | defineEnv (name : Option (String × Pos)) (sig : String) (dflt : Option (Array Raw))
      (beginB : Option (Array Raw)) (endB : Option (Array Raw)) (pos : Pos)
  | fileMark (f : String)
  | running (name : String) (opts : Option (Array Raw))
      (body : Option (Array Raw)) (pos : Pos)
  | logo (body : Option (Array Raw)) (pos : Pos)
  /-- `\logoleft`/`\logoright`: a headline band's corner slot. -/
  | logoSlot (left : Bool) (body : Option (Array Raw)) (pos : Pos)
  | palette (opts : Option (Array Raw)) (body : Option String) (pos : Pos)
  | beamerColor (name : String) (star : Bool) (source : String) (pos : Pos)
  | standoutColor (name source : String) (pos : Pos)
  /-- A block template's paint site: the beamer element chain, latest first,
  the channel and the palette entry it paints. -/
  | beamerSite (chain : List String) (channel key : String) (pos : Pos)
  /-- `\pagecolor`, or `\nopagecolor` as `none`. -/
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
  /-- hyperref's metadata lowered by Compat: the construct, its link styles, its dates and trapping
  as `\pdfmeta` entries, each key's TeX. -/
  | pdfmetaText (what links words : String) (pairs : Array (Compat.MetaKey × Array Raw)) (pos : Pos)
  | captionsetup (scope : Option String) (unclosed : Option Pos) (body : Option String) (pos : Pos)
  /-- url.sty's `\urlstyle`: the family `\url` and `\nolinkurl` set in. -/
  | urlstyle (v : Option String) (pos : Pos)
  /-- A preamble ink declaration still in force where the body begins, replayed
  as the body's first. -/
  | bodyStart (source : String) (pos : Pos)
  | titleDecl (name : String) (unclosed : Option Pos) (recovered : Bool)
      (body : Option (Array Raw × Option (Array Raw))) (pos : Pos)
  | reserved (name : String) (code : DiagCode) (unclosed : Option Pos) (pos : Pos)
  | unknownCmd (name : String) (args : String) (unclosed : Option Pos) (pos : Pos)
  /-- `\SetKw` and family: a document-global algorithm2e keyword. -/
  | algKw (name : String) (args : Option (Array Raw × Array Raw)) (pos : Pos)
  /-- `\DontPrintSemicolon`/`\LinesNumbered`: a document-wide algorithm
  default. -/
  | algFlag (name : String) (pos : Pos)
  /-- An algorithm2e display setting outside the model, named and ignored. -/
  | algSetting (name : String) (pos : Pos)
  /-- `\newtheorem{env}[shared]{heading}[within]`, starred unnumbered as in
  amsthm. -/
  | newtheorem (star : Bool) (env : String) (shared : Option String)
      (heading : Option (Array Raw)) (within : Option String) (pos : Pos)
  /-- amsthm's `\theoremstyle{s}`: the style the `\newtheorem`s after it
  take. -/
  | theoremstyle (name : Option String) (pos : Pos)
  /-- amsmath's `\numberwithin[fmt]{counter}{within}`; `none` when its groups
  are missing. -/
  | numberwithin (fmt : Option String) (counter : Option (String × String)) (pos : Pos)
  /-- `\AtBeginSection[starred]{code}` or `\AtBeginSubsection`, as written. -/
  | sectionHook (name : String) (starred code : Option (Array Raw)) (pos : Pos)
  /-- A cancel package load's options, as written. -/
  | cancelOpts (src : String) (pos : Pos)
  /-- A blueprint's site declaration: its package load, `\github`, `\dochome` or `link`. -/
  | blueprintSite (key : Blueprint.SiteKey) (url : String) (pos : Pos)
  /-- Text before `\begin{document}`, as written. -/
  | stray (src : String)

/-- The preamble fold's state. -/
public structure PreState where
  ctx : Ctx
  docClass : Ir.DocClass := .article
  sawClass : Bool := false
  /-- The class named is not one the engine has, whose error accounts for its options. -/
  classUnknown : Bool := false
  classOptions : String := ""
  page : PageSpec := {}
  sawPage : Bool := false
  fonts : FontSpec := {}
  palette : Palette := {}
  /-- A `\pagecolor` resolved in preamble order, overlaid on the final
  palette. -/
  pageGround : Option Color := none
  tokens : Tokens := {}
  /-- The caption positions `\captionsetup` declared. -/
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
  /-- The document wrote a `\theme{...}`, known or not. -/
  sawTheme : Bool := false
  /-- The frame-alignment keys the installed theme sets. -/
  frameKeys : Ir.FrameKeys := .beamer
  /-- Whether the installed theme sets each section on a page of its own. -/
  themeSectionPage : Bool := false
  /-- The form a refused abstract redefinition sets its body in, where it opens a quotation. -/
  abstractForm : Option Ir.AbstractForm := none

/-- An optional `[...]` run at `j` and the index past it; an unclosed run
reaches the end. -/
private def takeOptRun (preamble : Array Raw) (j : Nat) :
    Option (Array Raw) × Nat :=
  if preamble[j]? matches some (.sym '[' _) then
    match closeBracketFrom preamble (j + 1) with
    | some c => (some (preamble.extract (j + 1) c), c + 1)
    | none => (some (preamble.extract (j + 1) preamble.size), preamble.size)
  else (none, j)

/-- Each key's group and its value's group, from a lowered metadata group. -/
private def metaTextPairs : List Raw → Array (Compat.MetaKey × Array Raw) →
    Array (Compat.MetaKey × Array Raw)
  | .group k _ :: .group v _ :: rest, acc =>
    metaTextPairs rest (match Compat.MetaKey.ofName? (rawSrc k) with
      | some key => acc.push (key, v)
      | none => acc)
  | _, acc => acc

/-- The `\pdfmeta` group at `j` when Compat lowered it from TeX values (`Compat.metaTextMark`). -/
private def metaTextAt (raws : Array Raw) (j : Nat) :
    Option (String × String × String × Array (Compat.MetaKey × Array Raw) × Nat) :=
  match raws[j]? with
  | some (.group body _) =>
    match body.toList with
    | .ctrl m _ :: .group what _ :: .group links _ :: .group words _ :: rest =>
      if m == Compat.metaTextMark then
        some (rawSrc what, rawSrc links, rawSrc words, metaTextPairs rest #[], j + 1)
      else none
    | _ => none
  | _ => none

/-- Segments the preamble into declaration values, `\input` wrappers
spliced open between file markers. -/
public def scanDecls (file : String) (pre : Array Raw) : Array PDecl := Id.run do
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
            #[Raw.ctrl (Marker.name .file f) pos] ++ wrapped ++
            #[Raw.ctrl (Marker.name .file curFile) pos] ++
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
          let mut dflt : Option (Array Raw) := none
          let mut k := j + 1
          let mut beginRaws : Option (Array Raw) := none
          for _ in [k:preamble.size] do
            match preamble[k]? with
            | some (.group b _) =>
              beginRaws := some b
              k := k + 1
              break
            | some (.sym '[' _) =>
              -- The default an absent optional argument takes stands before the codes.
              match closeBracketFrom preamble (k + 1) with
              | some c =>
                dflt := some (preamble.extract (k + 1) c)
                k := c + 1
              | none =>
                sigRaws := sigRaws.push (.sym '[' pos)
                k := k + 1
            | some r' =>
              sigRaws := sigRaws.push r'
              k := k + 1
            | none => break
          let k2 := skipSpaces preamble k
          -- environ's `\NewEnviron`: the code before `\BODY` begins, the rest ends.
          let isMark (r : Raw) : Bool := match r with
            | .ctrl n _ => n == Marker.name .environBody ""
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
              | some (bb, ee) => (bb.push (.ctrl (Marker.name .environBody "") pos), ee)
              | none => (#[], code)
            i := kf
            out := out.push (.defineEnv (some (envName, npos)) (rawSrc sigRaws) dflt
              (some bb) (some (ee ++ final.getD #[.ctrl "ignorespacesafterend" pos])) pos)
          | _, _ =>
            let endRaws : Option (Array Raw) := match preamble[k2]? with
              | some (.group e _) => some e
              | _ => none
            i := if endRaws.isSome then k2 + 1 else k
            out := out.push (.defineEnv (some (envName, npos)) (rawSrc sigRaws) dflt
              beginRaws endRaws pos)
        | _ =>
          out := out.push (.defineEnv none "" none none none pos)
          i := j + 1
      | .ctrl name pos =>
        i := i + 1
        let marker := Marker.read? name
        if let some (.file, f) := marker then
          curFile := f
          out := out.push (.fileMark f)
        else if marker.any fun (k, _) => k == .series || k == .lang then
          -- premise: compatMarkerChecks — the Doc is the one without it
          pure ()
        else if let some (.pageColor, source) := marker then
          out := out.push (.pageGround (some source) pos)
        else if marker.any (·.1 == .pageColorReset) then
          out := out.push (.pageGround none pos)
        else if let some (.ink, source) := marker then
          out := out.push (.bodyStart source pos)
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
        else if name == BeamerColor.siteMarker then
          let j := skipSpaces preamble i
          let j2 := skipSpaces preamble (j + 1)
          let j3 := skipSpaces preamble (j2 + 1)
          match preamble[j]?, preamble[j2]?, preamble[j3]? with
          | some (.group elems _), some (.group ch _), some (.group key _) =>
            i := j3 + 1
            let chain := elems.toList.filterMap fun r => match r with
              | .group el _ => some (rawSrc el).trimAscii.toString
              | _ => none
            out := out.push (.beamerSite chain (rawSrc ch).trimAscii.toString
              (rawSrc key).trimAscii.toString pos)
          | _, _, _ => out := out.push (.unknownCmd "usebeamercolor" "" none pos)
        else if name == BeamerColor.marker || name == BeamerColor.starMarker ||
            name == BeamerColor.standoutMarker then
          let j := skipSpaces preamble i
          let j2 := skipSpaces preamble (j + 1)
          match preamble[j]?, preamble[j2]? with
          | some (.group elem _), some (.group body _) =>
            i := j2 + 1
            out := out.push (if name == BeamerColor.standoutMarker then
              .standoutColor (rawSrc elem) (rawSrc body) pos
              else .beamerColor (rawSrc elem) (name == BeamerColor.starMarker) (rawSrc body) pos)
          | _, _ => out := out.push (.unknownCmd "setbeamercolor" "" none pos)
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
          let (_, k) := takeOptRun preamble (skipSpaces preamble i)
          i := k
          out := out.push (.pictures (some "tool = lualatex") pos)
        else if name == Compat.cancelOptionsMark then
          match preamble[i]? with
          | some (.group body _) =>
            i := i + 1
            out := out.push (.cancelOpts (rawSrc body) pos)
          | _ => out := out.push (.cancelOpts "" pos)
        else if name == Compat.blueprintSiteMark then
          match preamble[i]?, preamble[i + 1]? with
          | some (.group key _), some (.group url _) =>
            i := i + 2
            if let some k := Blueprint.SiteKey.ofName? (rawSrc key) then
              out := out.push (.blueprintSite k (rawSrc url) pos)
          | _, _ => pure ()
        else if let some (what, links, words, pairs, k) :=
            (if name == "pdfmeta" then metaTextAt preamble (skipSpaces preamble i) else none) then
          i := k
          out := out.push (.pdfmetaText what links words pairs pos)
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
          | "figures" => out := out.push (.figures src pos)
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
            scope := some (bracketSrc preamble j j').trimAscii.toString
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
            let short := bracketArgRaws? preamble i pos
            i := j + 1
            out := out.push (.titleDecl name unclosed recovered
              (some (b, short)) pos)
          | _ =>
            out := out.push (.titleDecl name unclosed recovered none pos)
            if recovered then
              i := j
        else if name == "newtheorem" then
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
        else if name == "AtBeginSection" || name == "AtBeginSubsection" then
          let (starred, code, j) := hookArgsAt preamble i
          i := j
          out := out.push (.sectionHook name starred code pos)
        else if name == "theoremstyle" then
          let j := skipSpaces preamble i
          match preamble[j]? with
          | some (.group g _) =>
            i := j + 1
            out := out.push (.theoremstyle (some (rawSrc g).trimAscii.toString) pos)
          | _ =>
            out := out.push (.theoremstyle none pos)
        else if name == "numberwithin" then
          let (fmt, j0) := takeOptRun preamble (skipSpaces preamble i)
          let fmt := fmt.map fun r => (rawSrc r).trimAscii.toString
          let j1 := skipSpaces preamble j0
          let j2 := skipSpaces preamble (j1 + 1)
          match preamble[j1]?, preamble[j2]? with
          | some (.group c _), some (.group w _) =>
            i := j2 + 1
            out := out.push (.numberwithin fmt
              (some ((rawSrc c).trimAscii.toString, (rawSrc w).trimAscii.toString)) pos)
          | _, _ =>
            i := j0
            out := out.push (.numberwithin fmt none pos)
        else if let some code := reservedCtrl.lookup name then
          let (j, unclosed) := skipReservedArgs preamble i pos
          match unclosed with
          | some bpos =>
            out := out.push (.reserved name code (some bpos) pos)
            i := malformedRun preamble i pos (groups := true)
          | none =>
            out := out.push (.reserved name code none pos)
            i := j
        else
          -- A TeX register assignment's `=` and value go with the skipped name.
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
          let args := rawSrc (preamble.extract i j)
          match unclosed with
          | some bpos =>
            out := out.push (.unknownCmd name args (some bpos) pos)
            i := malformedRun preamble i pos (groups := true)
          | none =>
            out := out.push (.unknownCmd name args none pos)
            i := j
      | _ =>
        i := i + 1
        out := out.push (.stray (rawSrc #[r]))
    else
      break
  return out

/-- Applies `\allow{...}`: each named code accepts its loss, a renumbered or
retired code is noted, and an unknown one is refused. -/
private def applyAllow (ctx : Ctx) (allow : Array String) (src : String) (pos : Pos) :
    Array String × Array PEvent := Id.run do
  let mut allow := allow
  let mut evs : Array PEvent := #[]
  for code in Decl.splitEntries src do
    match DiagCode.ofString? code with
    | some c =>
      unless allow.contains c.code do
        allow := allow.push c.code
    | none =>
      match DiagCode.renumbered.lookup code, DiagCode.retired.lookup code with
      | some succ, _ =>
        unless allow.contains succ do
          allow := allow.push succ
        evs := evs.push (.say (diagOf ctx .N0105
          s!"'\\allow' names the renumbered code '{code}'; '{succ}' reports the same loss \
now, and is accepted in its place"
          (some pos) (help := s!"write '{succ}' in \\allow instead of '{code}'")
          (subject := some ("allow:" ++ code))))
      | none, some (some succ) =>
        evs := evs.push (.say (diagOf ctx .N0105
          s!"'\\allow' names the retired code '{code}'; '{succ}' reports this now, \
so this accepts nothing"
          (some pos) (help := s!"remove '{code}' from \\allow and review the '{succ}' diagnostic")
          (subject := some ("allow:" ++ code))))
      | none, some none =>
        evs := evs.push (.say (diagOf ctx .N0105
          s!"'\\allow' names the retired code '{code}'; the loss it named cannot occur"
          (some pos) (subject := some ("allow:" ++ code))))
      | none, none =>
        evs := evs.push (.say (diagOf ctx .E0329
          s!"'\\allow' names no diagnostic code '{code}'" (some pos)
          (help := "codes look like 'E0333'; each names the one loss it accepts")))
  return (allow, evs)

/-- Emits a pure step's reporting events and returns its state. -/
private def stepDone (ctx : Ctx) (r : PreState × Array PEvent) : EM PreState := do
  emitEvents ctx r.2
  return r.1

private def stepPage (s : PreState) (src : String) (pos : Pos) :
    PreState × Array PEvent :=
  let pb := Decl.parseBlock s.ctx.file src pos "page" s.tokens.entries
  let pe := applyPage s.ctx s.page pb.1 pos s.tokens.entries
  -- Only geometry keys claim the page, so a parskip alone keeps the default margin.
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

private def stepOutput (s : PreState) (src : String) (pos : Pos) :
    PreState × Array PEvent :=
  let oe := applyOutput s.ctx s.output src pos
  ({ s with output := oe.1 }, oe.2)

/-- Applies `\chrome`, warning under a class that never draws it. -/
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

/-- A keyed head missing its `{...}` block, as a step. -/
private def stepMissing (s : PreState) (name : String) (what : String) (pos : Pos) :
    PreState × Array PEvent :=
  (s, #[.say (diagOf s.ctx .E0304 s!"'\\{name}' needs {what}" (some pos))])

/-- Applies one preamble declaration to the fold state. -/
public def applyDecl (s : PreState) (d : PDecl) : EM PreState := do
  match d with
  | .docclass options cls pos =>
    let s := { s with sawClass := true }
    let s := match options with
      | some o => { s with classOptions := o }
      | none => s
    match cls with
    | some named =>
      match Ir.DocClass.ofString? named with
      | some c =>
        return { s with docClass := c, palette := { s.palette with
          classColors := c.classColors (Ir.Surface.ofPath s.ctx.file) } }
      | none =>
        diag s.ctx .E0309 s!"unknown document class '{named}'" pos
          (help := "classes: article, slides, card, resume, webpage")
        return { s with classUnknown := true }
    | none =>
      diag s.ctx .E0304 "'\\documentclass' needs a {class}" pos
      return s
  | .defineCmd decl pos =>
    let ⟨(cmd?, _), _⟩ ← takeDefine s.ctx decl 0 pos
    if let some cmd := cmd? then
      if let some (lvl, parts) := secFmtDefine? cmd then
        -- Not a macro: a heading-number format declaration.
        applySecFmt lvl parts
        return s
    let cmd? ← match cmd? with
      | some cmd => do
        if (← gateRedefB s.ctx cmd) then pure (some cmd) else pure none
      | none => pure none
    match cmd? with
    | some cmd =>
      return { s with ctx := bindCmd s.ctx cmd }
    | none => return s
  | .defineEnv name sig dflt beginB endB pos =>
    match name with
    | some (envName, npos) =>
      if builtinEnvNames.contains envName then
        -- A refused abstract redefinition still declares its heading style and body size.
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
        let quoted := envName == "abstract" && beginB.any (opensQuotation ·.toList)
        modify fun st => { st with diags := st.diags.push (Diag.of .W0303
          (match est, heading, quoted with
           | some _, some _, true =>
             s!"'\{{envName}}' is built in; this definition's heading, body size and quotation \
margins style it, the built-in's body font and vertical skips stand{replaced}"
           | some _, some _, false =>
             s!"'\{{envName}}' is built in; this definition's heading and body size style it, \
the built-in's margins, body font and vertical skips stand{replaced}"
           | some _, none, true =>
             s!"'\{{envName}}' is built in; of this definition only its body size and quotation \
margins are read, the built-in's heading stands{replaced}"
           | some _, none, false =>
             s!"'\{{envName}}' is built in; of this definition only its body size is read, \
the built-in's heading and margins stand{replaced}"
           | none, _, _ =>
            s!"'\{{envName}}' is built in; this definition is ignored")
          (some ⟨s.ctx.file, npos⟩)
          (help := "the built-in already does this; \\define it under another name")) }
        let s := if quoted then { s with abstractForm := some .quotation } else s
        match est with
        | some est =>
          let merged := Theme.styleMerge ((s.styles.find? "abstract").getD {}) est
          return { s with styles := s.styles.declare "abstract" merged }
        | none => return s
      else
        match beginB, endB with
        | some b, some e =>
          let params ← parseSig s.ctx sig pos
          if dflt.isSome && !(params[0]?.any (·.optional)) then
            warnOnce s.ctx ("defineenv:default:" ++ envName) .W0110
              s!"'\\defineenv \{{envName}}' gives a default, but its first parameter is not \
optional; the default is ignored" pos
              (help := "mark the first parameter optional, as in (title?: content)")
          let params := match dflt with
            | some d =>
              params.modify 0 fun p => if p.optional then { p with default := some d } else p
            | none => params
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
    return { s with ctx := { s.ctx with file := f, callSite := none } }
  | .running name opts body pos =>
    -- `from` gates only this head or foot; a redeclaration without it resets.
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
      -- An empty body only defers the gate; it never clears a declared line.
      if content.isEmpty then
        if name == "runninghead" then
          return { s with headFrom := max s.headFrom fromPage }
        else
          return { s with footFrom := max s.footFrom fromPage }
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
    let cmd := if left then "logoleft" else "logoright"
    match body with
    | some b =>
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
  | .beamerColor name star src pos =>
    let pal ← applyBeamerColor s.ctx s.palette name star src pos
    return { s with palette := pal, ctx := { s.ctx with palette := pal } }
  | .beamerSite chain channel key _ =>
    modify fun st => { st with scope := { st.scope with
      palette := st.scope.palette.addSite chain channel key } }
    let pal ← resolveBeamerColors s.ctx s.palette
    return { s with palette := pal, ctx := { s.ctx with palette := pal } }
  | .standoutColor name source pos =>
    modify fun st => { st with scope := { st.scope with palette := { st.scope.palette with
      standoutAliases := st.scope.palette.standoutAliases ++
        [⟨name.trimAscii.toString, source, s.ctx.sourceSpan pos⟩] } } }
    return s
  | .palette opts body pos =>
    let (decorative, seeds, skipBlock) ← match opts with
      | some opt => parsePaletteOpts s.ctx (rawSrc opt) pos
      | none => pure (false, false, false)
    match body with
    | some src =>
      if skipBlock then
        return s
      else
        let pal ← applyPalette s.ctx s.palette src pos (decorative := decorative) (seeds := seeds)
          (depth := s.docClass.record.groundDepth)
        return { s with palette := pal, ctx := { s.ctx with palette := pal } }
    | none =>
      diag s.ctx .E0304 "'\\palette' needs a {...} block" pos
      return s
  | .style args pos =>
    match args with
    | some (elem, body) =>
      -- premise: frameTitleKeyChecks — only the frame model draws a frame title
      if elem.trimAscii.toString == "frametitle" && s.docClass.record.model != .frame then
        warnOnce s.ctx "style:frametitle" .W0104
          s!"'\\style\{frametitle}' styles frame titles, which the {s.docClass.name} class never \
draws; skipped" pos
          (help := "a frame title is set by a presentation class, such as beamer")
        return s
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
      let s := { s with sawTheme := true }
      let tname := src.trimAscii.toString
      -- beamer's `default` installs no bundle and displaces the class default.
      if tname == "default" then
        return { s with themeSectionPage := false }
      match Theme.find? tname with
      | some th =>
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
        -- Judged against what the document declared, not an earlier bundle.
        for (kind, key) in Theme.replaces th before do
          if (← get).declaredKeys.contains (kind.name, key) then
            diag s.ctx .W0348
              s!"theme '{tname}' replaces the document's earlier '{key}' from '\\{kind.name}'"
              (some pos)
              (help := "overrides go after '\\theme': move the declaration below it")
        -- A theme with a section page sets its own hook, as beamer's does, over an earlier one.
        -- premise: sectionPageChecks — the replaced hook is named
        if th.sectionPage && (← get).sectionHook.isSome then
          diag s.ctx .W0348
            s!"theme '{tname}' replaces the document's earlier '\\AtBeginSection'" (some pos)
            (help := "overrides go after '\\theme': move the declaration below it")
          modify fun st => { st with sectionHook := none }
        let installed := (Theme.declares th s.palette.classColors.depth).map
          fun (k, key) => (k.name, key)
        let ownRoles (rs : Array Role) : Array Role :=
          rs.filter fun r => !installed.contains ("palette", (ColorRef.role r).key)
        modify fun st => { st with
          declaredKeys := st.declaredKeys.filter (fun e => !installed.contains e)
          spans := { st.spans with docRoles := ownRoles st.spans.docRoles } }
        let ds := Theme.apply th before
        modify fun st => { st with scope := { st.scope with palette := { st.scope.palette with theme := tname } } }
        for (key, c) in (th.realize s.palette.classColors.depth).entries do
          recordColorDeclaration key.key c (s.ctx.sourceSpan pos)
          if let .role r := key then
            modify fun st => { st with scope := { st.scope with
              palette := st.scope.palette.native r c } }
        let pal ← resolveBeamerColors s.ctx ds.palette
        -- A share the preamble declared before the theme binds the bundle it installs.
        let pal ← match pal.coveredFraction with
          | some n => reseedCovered s.ctx pos pal s.docClass.record.groundDepth n
          | none => pure pal
        return { s with
          palette := pal
          tokens := ds.tokens
          styles := ds.styles
          chrome := ds.chrome
          frameKeys := th.frameKeys
          themeSectionPage := th.sectionPage
          ctx := { s.ctx with palette := pal, tokens := ds.tokens } }
      | none =>
        diag s.ctx .W0319 s!"unknown theme '{tname}'; the document is unthemed"
          (some pos)
          (help := s!"themes: {String.intercalate ", " Theme.names}")
          (refused := some tname)
        return { s with themeSectionPage := false }
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
  | .figures body pos =>
    match body with
    | some src =>
      let mut s := s
      for e in Decl.splitEntries src do
        match Decl.splitEntry e with
        | some ("convert", v) =>
          let v := v.trimAscii.toString
          if v == "none" then
            s := { s with ctx := { s.ctx with pic := { s.ctx.pic with convert := false } } }
          else if v == "pdftocairo" || v == "rsvg-convert" then
            s := { s with ctx := { s.ctx with pic := { s.ctx.pic with convert := true } } }
          else
            diag s.ctx .E0321
              s!"cannot read a converter for 'convert' in 'figures': '{v}'" pos
              (help := "the engine runs only the converters it pins: pdftocairo for a PDF \
figure's web face and rsvg-convert for an SVG figure; \
convert = none refuses both")
        | some (key, _) =>
          let d := Decl.unknownKey s.ctx.file "figures" key ["convert"] pos
          modify fun st => { st with diags := st.diags.push d }
        | none => pure ()
      return s
    | none =>
      diag s.ctx .E0304 "'\\figures' needs a {...} block" pos
      return s
  | .pdfmeta (some src) pos => stepDone s.ctx (stepPdfmeta s src pos)
  | .pdfmeta none pos => stepDone s.ctx (stepMissing s "pdfmeta" "a {...} block" pos)
  | .pdfmetaText what links words pairs pos =>
    let mut info := s.info
    let mut evs : Array PEvent := #[]
    let mut said : Array String := #[]
    for (key, raws) in pairs do
      -- A value is body TeX read as text, its reserved characters text, its report alone kept.
      let saved ← get
      let inherited := (s.ctx.user.extract 0 s.ctx.limit).toList.map (·.name)
      let (raws, ds, _) := Compat.rewrite s.ctx.file raws (warned := saved.warnedUnknown)
        (inherited := inherited)
      modify fun st => { st with diags := st.diags ++ ds.filter (·.severity != .note) }
      let xs ← elabInlines { s.ctx with argBody := true } raws
      modify fun st => { saved with
        diags := st.diags, warnedUnknown := st.warnedUnknown, runShapes := st.runShapes
        spans := { saved.spans with recoveryDiags := st.spans.recoveryDiags } }
      let text := Ir.metaText xs
      let unresolved := xs.any fun x =>
        Ir.foldInline (fun b y => b || y matches .ref .. || y matches .cite ..) false x
      if unresolved then
        modify fun st => { st with diags := st.diags.push (diagOf s.ctx .W0349
          s!"pdf{key.name} holds a reference or citation, which metadata reads before the page \
numbers it; set as '??' or '?'" (some pos)
          (help := "write the number or the source as text in the metadata value")
          (subject := some s!"pdf{key.name}")) }
      if text.trimAscii.isEmpty then continue
      info := match key with
        | .title => { info with title := some text }
        | .author => { info with author := some text }
        | .subject => { info with subject := some text }
        | .keywords => { info with keywords := some text }
      evs := evs.push (.scalar "pdfmeta" key.name text pos)
      said := said.push s!"{key.name} = {Decl.quote text}"
    let (worded, wordEvs) := stepPdfmeta { s with info } words pos
    unless words.isEmpty do said := said.push words
    let native := (if said.isEmpty then "" else
      s!"\\pdfmeta\{ {String.intercalate ", " said.toList} }") ++ links
    diag s.ctx .N0100 s!"'{what}' → {if native.isEmpty then "nothing: its values are empty" else native}" pos
    emitEvents s.ctx (evs ++ wordEvs)
    return { s with info := worded.info }
  | .urlstyle v pos =>
    -- The family is read before the fold (`urlFamily0`); this arm only reports.
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
      | .resolved c _ =>
        noteDocRoles [.page]
        return { s with pageGround := some c }
      | .missing =>
        warnPageColorMiss s.ctx source pos
        return s
      | .rejected => return s
  | .bodyStart _ _ =>
    -- The body opens with it; the fold has nothing to apply.
    return s
  | .captionsetup scope unclosed body pos =>
    -- caption3.sty's skip, margin and position keys; any other key is named.
    if let some bpos := unclosed then
      warnUnclosed s.ctx "'\\captionsetup'" bpos
    let kind? : Option (Option Ir.FloatKind) := scope.map Ir.FloatKind.ofCaptionType?
    match body with
    | some src =>
      let mut s := s
      for entry in KeyVal.items src do
        let (key, value) := KeyVal.entry entry
        if key.isEmpty then continue
        let value := value.getD ""
        let honouredToken ← do
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
            -- premise: captionScopeChecks — a self-assigned caption skip is a no-op
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
        -- caption3.sty: `tableposition` and `figureposition` carry their own scope.
        let posScope : Option String := match key, kind? with
          | "tableposition", _ => some "table"
          | "figureposition", _ => some "figure"
          | "position", some (some k) => some k.captionScope
          | "position", none => some ""
          | _, _ => none
        let mut honouredPos := false
        if let some sc := posScope then
          if let some p := Ir.CaptionPos.ofKey? value then
            s := { s with captionPos := Ir.redeclare s.captionPos sc p }
            honouredPos := true
        unless honouredToken || honouredPos do
          noteMentions value
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
    if let some bpos := unclosed then
      warnUnclosed s.ctx s!"'\\{name}'" bpos
    match body with
    | some (b, short) =>
      let short ← short.mapM (elabInlines s.ctx)
      storeTitlePart name (← elabInlines s.ctx b) short
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
      modify fun st => { st with alg := { st.alg with kws := Ir.redeclare st.alg.kws key kd } }
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
      warnOnce s.ctx ("theoremstyle:" ++ name.getD "") .W0110
        s!"'\\theoremstyle' names '{name.getD ""}', not one of plain, definition, \
remark; plain applies, as amsthm sets it" pos
      modify fun e => { e with ctr := { e.ctr with thm := { e.ctr.thm with style := .plain } } }
      return s
  | .numberwithin fmt counter pos =>
    match counter with
    | none =>
      warnOnce s.ctx "numberwithin:" .E0304
        "'\\numberwithin' needs {counter}{within}" pos
      return s
    | some (c, w) =>
      if let some f := fmt then
        unless f == "\\arabic" do
          warnOnce s.ctx ("numberwithin:" ++ c ++ ":fmt") .W0110
            s!"'\\numberwithin[{f}]\{{c}}' formats the number as '{f}', which the engine \
does not model; the number is arabic" pos
      let thms := (← get).ctr.thm
      match sectionLevel w with
      | none =>
        warnOnce s.ctx ("numberwithin:" ++ c) .W0110
          s!"'\\numberwithin\{{c}}\{{w}}' numbers within '{w}', a counter the engine \
does not keep; the number stands alone" pos
      | some lvl =>
        if c == "equation" then
          modify fun e => { e with ctr := { e.ctr with eqWithin := some lvl } }
        else if thms.counters.any (·.1 == c) then
          modify fun e => { e with ctr := { e.ctr with thm := { e.ctr.thm with
            counters := e.ctr.thm.counters.map fun p =>
              if p.1 == c then (c, some lvl) else p } } }
        else
          warnOnce s.ctx ("numberwithin:" ++ c) .W0110
            s!"'\\numberwithin\{{c}}' names a counter the engine does not number within \
a heading; its numbers stand alone" pos
      return s
  | .sectionHook name starred code pos =>
    -- the hooks are beamer's: outside a deck LaTeX knows neither
    if s.docClass.record.model != .frame then
      warnOnce s.ctx ("ctrl:" ++ name) .W0301
        s!"unknown command '\\{name}' in the preamble; skipped" pos
        (help := unknownCmdHelp name false)
      return s
    match code with
    | some c => recordSectionHook s.ctx name starred c pos
    | none => diag s.ctx .E0304 s!"'\\{name}' needs a \{...} group" pos
    return s
  | .cancelOpts src _ =>
    -- Compat named every option the package does not declare at the load.
    let opts := (KeyVal.items src).toList
    return { s with ctx := { s.ctx with cancel := (Math.CancelSpec.ofOptions opts).1 } }
  | .blueprintSite key url _ =>
    return { s with ctx := { s.ctx with blueprint := s.ctx.blueprint.declare key url } }
  | .unknownCmd name args unclosed pos =>
    -- Set lines the engine or an open boundary reads are not unknown.
    if Compat.nativeReadCtrls.contains name ||
        (s.ctx.pic.tool.isSome && Compat.boundaryCtrls.contains name) then
      return s
    noteMentions args
    warnOnce s.ctx ("ctrl:" ++ name) .W0301
      s!"unknown command '\\{name}' in the preamble; skipped" pos
      (help := unknownCmdHelp name false)
      (demote := Compat.styInternal s.ctx.file name)
    if let some bpos := unclosed then
      warnUnclosed s.ctx s!"'\\{name}'" bpos
    return s
  | .stray src =>
    noteMentions src
    if s.textDiagged then
      return s
    else
      diag s.ctx .E0313 "only declarations may appear before '\\begin{document}'" none
      return { s with textDiagged := true }

/-- The elaboration state with the stores only diagnostics read erased. -/
public def ESt.sem (e : ESt) : ESt :=
  { e with diags := #[], warnedUnknown := #[], seenScalars := #[], declaredKeys := #[],
           settings := #[], owedColors := {}, mentions := {}, packageInputs := #[], unjudged := #[] }

/-- The fold state with its reporting once-latch erased. -/
public def PreState.sem (s : PreState) : PreState := { s with textDiagged := false }

/-- The head of a keyed block declaration, whose apply step is a pure value
plus reporting events. -/
public def PDecl.keyedHead? : PDecl → Option String
  | .page _ _ => some "page"
  | .pdfmeta _ _ => some "pdfmeta"
  | .fonts _ _ => some "fonts"
  | .output _ _ => some "output"
  | .chrome _ _ => some "chrome"
  | .assert _ _ => some "assert"
  | .allow _ _ => some "allow"
  | _ => none

public def PDecl.Independent (d₁ d₂ : PDecl) : Prop :=
  match d₁.keyedHead?, d₂.keyedHead? with
  | some h₁, some h₂ => h₁ ≠ h₂
  | _, _ => False

private theorem EM.run_bind (m : EM α) (f : α → EM β) (e : ESt) :
    (m >>= f).run e = (f (m.run e).1).run (m.run e).2 := by rfl

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
  | setting setting pos =>
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
    ((stepDone ctx r).run e).1 = r.1 := by rfl

private theorem EM.run_stepDone_snd (ctx : Ctx) (r : PreState × Array PEvent) (e : ESt) :
    ((stepDone ctx r).run e).2 = r.2.foldl (applyEvent ctx) e := by rfl

private theorem applyDecl_page_some (s : PreState) (src : String) (pos : Pos) :
    applyDecl s (.page (some src) pos) = stepDone s.ctx (stepPage s src pos) := by rfl
private theorem applyDecl_page_none (s : PreState) (pos : Pos) :
    applyDecl s (.page none pos)
      = stepDone s.ctx (stepMissing s "page" "a {...} block" pos) := by rfl
private theorem applyDecl_fonts_some (s : PreState) (src : String) (pos : Pos) :
    applyDecl s (.fonts (some src) pos) = stepDone s.ctx (stepFonts s src pos) := by rfl
private theorem applyDecl_fonts_none (s : PreState) (pos : Pos) :
    applyDecl s (.fonts none pos)
      = stepDone s.ctx (stepMissing s "fonts" "a {...} block" pos) := by rfl
private theorem applyDecl_pdfmeta_some (s : PreState) (src : String) (pos : Pos) :
    applyDecl s (.pdfmeta (some src) pos) = stepDone s.ctx (stepPdfmeta s src pos) := by rfl
private theorem applyDecl_pdfmeta_none (s : PreState) (pos : Pos) :
    applyDecl s (.pdfmeta none pos)
      = stepDone s.ctx (stepMissing s "pdfmeta" "a {...} block" pos) := by rfl
private theorem applyDecl_output_some (s : PreState) (src : String) (pos : Pos) :
    applyDecl s (.output (some src) pos) = stepDone s.ctx (stepOutput s src pos) := by rfl
private theorem applyDecl_output_none (s : PreState) (pos : Pos) :
    applyDecl s (.output none pos)
      = stepDone s.ctx (stepMissing s "output" "a {...} block" pos) := by rfl
private theorem applyDecl_chrome_some (s : PreState) (src : String) (pos : Pos) :
    applyDecl s (.chrome (some src) pos) = stepDone s.ctx (stepChrome s src pos) := by rfl
private theorem applyDecl_chrome_none (s : PreState) (pos : Pos) :
    applyDecl s (.chrome none pos)
      = stepDone s.ctx (stepMissing s "chrome" "a {...} block" pos) := by rfl
private theorem applyDecl_assert_some (s : PreState) (src : String) (pos : Pos) :
    applyDecl s (.assert (some src) pos) = stepDone s.ctx (stepAssert s src pos) := by rfl
private theorem applyDecl_assert_none (s : PreState) (pos : Pos) :
    applyDecl s (.assert none pos)
      = stepDone s.ctx (stepMissing s "assert" "a {...} block" pos) := by rfl
private theorem applyDecl_allow_some (s : PreState) (src : String) (pos : Pos) :
    applyDecl s (.allow (some src) pos) = stepDone s.ctx (stepAllow s src pos) := by rfl
private theorem applyDecl_allow_none (s : PreState) (pos : Pos) :
    applyDecl s (.allow none pos)
      = stepDone s.ctx (stepMissing s "allow" "a {...} block of diagnostic codes" pos) := by rfl

/-- Independent adjacent preamble declarations commute up to reporting, in
both orders. -/
public theorem applyDecl_comm (s : PreState) (e : ESt) (d₁ d₂ : PDecl)
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
                  stepAssert, stepAllow, stepMissing]))

/-- The styling a refused `\renewcommand{\maketitle}` body declares around
`\@title`, read at the preamble's end; `none` once a redefinition won. -/
public def refusedTitleFragment (s : PreState) (body : Option (Array Raw)) :
    Option Ir.ElementStyle := do
  let body ← body
  if (lookupUser s.ctx "maketitle").isSome then none
  else refusedTitleReadout s.ctx.user s.ctx.limit body

/-- Merges a refused title body's styling under the document's own
`titlepage` style. -/
public def titleStyleMerge (s : PreState) (fragment : Option Ir.ElementStyle) : PreState :=
  match fragment with
  | none => s
  | some est =>
    let styles := s.styles.declare "titlepage"
      (Theme.styleMerge ((s.styles.find? "titlepage").getD {}) est)
    { s with styles := styles }

public def titleStyleApply (s : PreState) (body : Option (Array Raw)) : PreState :=
  titleStyleMerge s (refusedTitleFragment s body)

private def titleStyleDiagState (st : ESt) : ESt := Id.run do
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

/-- Applies a refused title body's styling and names it on the refusal's
diagnostic. -/
public def applyRefusedTitleStyle (s : PreState) : EM PreState := fun st =>
  let fragment := refusedTitleFragment s st.refusedTitleBody
  let st := { st with refusedTitleBody := none }
  (titleStyleMerge s fragment, if fragment.isSome then titleStyleDiagState st else st)

public theorem applyRefusedTitleStyle_result_exact (s : PreState) (st : ESt) :
    ((applyRefusedTitleStyle s).run st).1 = titleStyleApply s st.refusedTitleBody := by rfl

/-- Reads each refused size-command redefinition opening with
`\@setfontsize` as a size step and leading of the body, keeping the
built-in where the step would put the named sizes out of order. -/
private def applyRefusedSizeLadder (s : PreState) : EM PreState := do
  let stash := (← get).refusedSizeBodies
  if stash.isEmpty then return s
  modify fun st => { st with refusedSizeBodies := #[] }
  let mut steps : Array (String × Nat × Option Nat × Span) := #[]
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
    -- `sz` is milli-points, so the quotient is already per mille.
    let factor : Nat := ((Dim.pt (Int.ofNat sz) + bodySp / 2) / bodySp).toNat
    let skip := (fsArgs[2]?.bind Compat.ptMacroArg).filter (0 < ·) |>.map fun ld =>
      Ir.skipRowOf (Dim.pt (Int.ofNat ld)) bodySp
    steps := Ir.redeclare steps name (factor, skip, span)
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
  let withSkips (skips : List (String × Nat)) (landed : List (String × Option Nat)) :
      List (String × Nat) :=
    landed.foldl (fun sk (name, skip) => match skip with
      | some row => Ir.setSkip sk name row
      | none => sk) skips
  match Ir.setStepsAll s.page.scale (steps.toList.map fun q => (q.1, q.2.1)) with
  | some ladder =>
    for (name, factor, _, span) in steps do
      land name factor span
    let skips := withSkips s.page.skipScale (steps.toList.map fun q => (q.1, q.2.2.1))
    return { s with page := { s.page with sizes := some ladder, skips := some skips } }
  | none =>
    let mut ladder := s.page.scale
    let mut landed : Array (String × Option Nat) := #[]
    for (name, factor, skip, span) in steps do
      match Ir.setStep ladder name factor with
      | some l' =>
        ladder := l'
        landed := landed.push (name, skip)
        land name factor span
      | none =>
        refuse name factor
    if !landed.isEmpty then
      return { s with page := { s.page with sizes := some ladder
                                            skips := some (withSkips s.page.skipScale landed.toList) } }
    else
      return s

/-- The LaTeX2e definers, re-emitted to the boundary standalone as one
guarded `\renewcommand`. -/
private def latexDefiners : List String :=
  ["newcommand", "renewcommand", "providecommand", "DeclareRobustCommand"]

/-- The xparse definers, re-emitted as `\DeclareDocumentCommand`. -/
private def xparseDefiners : List String :=
  ["NewDocumentCommand", "RenewDocumentCommand", "DeclareDocumentCommand",
   "ProvideDocumentCommand"]

/-- TeX's primitive definers, re-emitted in their own spelling. -/
private def texDefiners : List String := ["def", "gdef", "edef", "xdef"]

/-- A definer's name argument, braced or bare. -/
private def definerName? (raws : Array Raw) (i : Nat) : Option String :=
  match raws[i]? with
  | some (.ctrl n _) => some n
  | some (.group b _) =>
    b.findSome? fun (r : Raw) =>
      match r with
      | .ctrl n _ => some n
      | _ => none
  | _ => none

/-- One LaTeX2e definer, re-emitted as a `\providecommand` guard and a
`\renewcommand` with its arity and default as written. -/
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

/-- One xparse definer, its argument specification kept as written. -/
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

/-- The control at `i` and the first group among the `reach - 1` raws after it: the control's name,
the raws between, the group's body and the index past it. -/
private def definerHead? (raws : Array Raw) (i reach : Nat) :
    Option (String × Array Raw × Array Raw × Nat) := do
  let some (.ctrl name _) := raws[i]? | none
  let k ← (List.range' (i + 1) (min raws.size (i + reach) - (i + 1))).find? fun k =>
    raws[k]? matches some (.group _ _)
  let some (.group body _) := raws[k]? | none
  return (name, raws.extract (i + 1) k, body, k + 1)

/-- One TeX definer, its parameter text kept verbatim; the body group must
follow within 16 elements. -/
private def texDefiner? (head : String) (raws : Array Raw) (i : Nat) :
    Option ((String × String) × Nat) := do
  let (name, params, body, next) ← definerHead? raws i 17
  return ((name, s!"\\{head}\\{name}{rawSrc params}\{{rawSrc body}}"), next)

/-- `\DeclareMathOperator` and its starred form, re-emitted through
`\operatorname` and guarded as a LaTeX definer is. -/
private def operatorDefiner? (raws : Array Raw) (i : Nat) :
    Option ((String × String) × Nat) := do
  let star := raws[i]? matches some (.word "*" _)
  let i := skipStar raws i
  let name ← definerName? raws i
  let j := skipSpaces raws (i + 1)
  match raws[j]? with
  | some (.group body _) =>
    let op := if star then "\\operatorname*" else "\\operatorname"
    some ((name, s!"\\providecommand\{\\{name}}\{}\
\\renewcommand\{\\{name}}\{{op}\{{rawSrc body}}}"), j + 1)
  | _ => none

/-- `\setlength{\name}{value}`, re-emitted with a `\newlength` only where the
length is undefined. -/
private def lengthDefiner? (raws : Array Raw) (i : Nat) :
    Option ((String × String) × Nat) := do
  let name ← definerName? raws i
  let j := skipSpaces raws (i + 1)
  match raws[j]? with
  | some (.group body _) =>
    some ((name, s!"\\ifdefined\\{name}\\else\\newlength\{\\{name}}\\fi\
\\setlength\{\\{name}}\{{rawSrc body}}"), j + 1)
  | _ => none

/-- The native `\define \name(sig) {body}`, re-emitted as a LaTeX definer
whose arity is the signature's parameter count. -/
private def nativeDefiner? (raws : Array Raw) (i : Nat) :
    Option ((String × String) × Nat) := do
  let (name, sig, body, next) ← definerHead? raws i 33
  let entries := ((rawSrc sig).splitOn ",").filter fun e => e.toList.any Char.isAlpha
  let spec :=
    if entries.isEmpty then ""
    else if ((entries.headD "").splitOn "?").length > 1 then s!"[{entries.length}][]"
    else s!"[{entries.length}]"
  let line := s!"\\providecommand\{\\{name}}\{}\
\\renewcommand\{\\{name}}{spec}\{{rawSrc body}}"
  return ((name, line), next)

mutual

-- conserves: none — collects macro definitions, drops the rest
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
      else if name == "DeclareMathOperator" then operatorDefiner? raws (i + 1)
      else if name == "setlength" then lengthDefiner? raws (i + 1)
      else none
    match read? with
    | some (entry, k) =>
      let provide := name == "providecommand" || name == "ProvideDocumentCommand"
      let kept := if provide && (out.any (fun q => q.1 == entry.1) ||
          TikzCommands.pgfDefined.contains entry.1)
        then out else out.push entry
      macroScanLevel raws kept rest (i + 1) (k - (i + 1))
    | none => macroScanLevel raws out rest (i + 1) 0
  | r :: rest, i, 0 => macroScanLevel raws (macroScanRaw out r) rest (i + 1) 0

/-- Descends into a group or an environment, skipping a picture's own body. -/
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

/-- The document's macro definitions for the boundary, one per name at its
last definition; a name defined with different texts is left out. -/
public def macroScan (raws : Array Raw) : Array (String × String) := Id.run do
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

/-- The style table a picture setting leaves for the next one. -/
public def pictureSettingStyles (styles : List (String × Array Picture.Tok))
    (setting : Span × Array Raw) : List (String × Array Picture.Tok) :=
  (Picture.readStyleList styles (Picture.ofSetting setting)).1

/-- Names an unread picture key once, at the setting that declares it. -/
private def pictureKeyState (ctx : Ctx) (span : Span) (st : ESt) (key : String) : ESt :=
  warnOnceState { ctx with file := span.file, callSite := none } ("picture:set:" ++ key)
    .W0334 s!"picture key {key} is outside the rendered picture subset; the key is dropped"
    span.pos (some "the rendered subset reads 'name/.style={...}' definitions") false st

/-- Names the keys one setting leaves unread, then advances the style table. -/
private def pictureSettingState (ctx : Ctx)
    (acc : List (String × Array Picture.Tok) × ESt)
    (setting : Span × Array Raw) : List (String × Array Picture.Tok) × ESt := Id.run do
  let mut st := acc.2
  for key in Picture.unreadKeys acc.1 (Picture.ofSetting setting) do
    st := pictureKeyState ctx setting.1 st key
  return (pictureSettingStyles acc.1 setting, st)

/-- Names every picture setting's unread keys in declaration order, earlier
styles carried forward. -/
public def reportPictureKeys (ctx : Ctx) (sets : Array (Span × Array Raw)) (st : ESt) : ESt :=
  Id.run do
    let mut acc := (([] : List (String × Array Picture.Tok)), st)
    for setting in sets do
      acc := pictureSettingState ctx acc setting
    return acc.2

/-- Where picture key losses enter the document's diagnostic sequence. -/
public structure PictureReportContext where
  ctx : Ctx
  offset : Nat

/-- Names unread picture keys at the report's offset when the body holds an
engine-drawn picture. -/
public def finishPictureKeys (report : PictureReportContext) (doc : Doc)
    (sets : Array (Span × Array Raw)) (st : ESt) : ESt :=
  -- premise: pictureKeyGateChecks — only engine-drawn pictures lose keys
  if 0 < enginePictures doc.body then
    let named := reportPictureKeys report.ctx sets { st with diags := #[] }
    { named with diags := st.diags.extract 0 report.offset ++ named.diags ++
        st.diags.extract report.offset st.diags.size }
  else st

/-- The declaration fold's result with the body and trailing raws it leaves. -/
public structure DocPreamble where
  state : PreState
  decls : Array PDecl
  body : Array Raw
  trailing : Array Raw

/-- What the document continuation decides after the body elaborates. -/
public structure BodyCompletion where
  doc : Doc
  table : Ir.RefTable
  pictureReport : PictureReportContext
  locale : Locale
  resolve : Bool

/-- Attaches the numbered body and resolves references across the document. -/
public def BodyCompletion.attach (completion : BodyCompletion) (blocks : Array Block) : Doc :=
  let doc := { completion.doc with body := blocks }
  if completion.resolve then
    Ir.mapDoc (Ir.resolveRefInlines completion.locale completion.table)
      (Ir.resolveRefs completion.locale completion.table) doc
  else doc

public theorem BodyCompletion.attach_body_exact (completion : BodyCompletion)
    (blocks : Array Block) :
    (completion.attach blocks).body =
      if completion.resolve then Ir.resolveRefs completion.locale completion.table blocks
      else blocks := by
  unfold BodyCompletion.attach
  split <;> rfl

/-- The body interpreter's inputs and its document continuation. -/
public structure DocBodyPlan where
  ctx : Ctx
  raws : Array Raw
  finish : Array Block → EM BodyCompletion

/-- The `\label` keys the body bound; none in a deck, whose labels stand on what is set next, as
beamer's do. -/
private def referentKeys (ctx : Ctx) (st : ESt) : Ir.ReferentKeys :=
  if ctx.slides then Ir.ReferentKeys.empty else { labels := st.labelKeys }

/-- Numbers the body's floats, stands each label at what it names, runs the continuation and
attaches the body. -/
public def finishDocBody (plan : DocBodyPlan) (blocks : Array Block) :
    EM (Doc × Ir.RefTable × PictureReportContext) := do
  let blocks := Ir.anchorReferents (referentKeys plan.ctx (← get)) (Ir.numberFloats blocks)
  let completion ← plan.finish blocks
  return (completion.attach blocks, completion.table, completion.pictureReport)

public def runDocBody (plan : DocBodyPlan) : EM (Doc × Ir.RefTable × PictureReportContext) := do
  finishDocBody plan (← elabBlocks plan.ctx plan.raws)

/-- An unhandled control and its group. -/
public structure RecoveryGroup where
  name : String
  body : Array Raw
  pos : Pos
  groupPos : Pos

public def RecoveryGroup.call (group : RecoveryGroup) : Array Raw :=
  #[.ctrl group.name group.pos, .group group.body group.groupPos]

public def RecoveryGroup.braced (group : RecoveryGroup) : Array Raw :=
  #[.group group.body group.groupPos]

/-- The inputs on which an unhandled control's group recovers as an inline
paragraph of its braced spelling. -/
public def RecoveryGroupInput (ctx : Ctx) (raws : Array Raw) (group : RecoveryGroup) : Prop :=
  raws = group.call ∧
  ctx.macroRoles = ({file := ""} : Ctx).macroRoles ∧
  group.pos.origins = [] ∧ group.groupPos.origins = [] ∧
  recoversInlineName ctx group.name = true ∧
  isBlockStart ctx group.name group.call 0 #[] = false ∧
  group.body.any isParRaw = false ∧
  (group.body.any isCenteringRaw || bodyIsBlock group.body) = false

/-- Elaborates the group as braced content under the control's recovery
warning, then finishes the document. -/
public def runBracedRecovery (plan : DocBodyPlan) (group : RecoveryGroup) :
    EM (Doc × Ir.RefTable × PictureReportContext) := do
  let blocks ← withControlRecovery plan.ctx group.name group.pos group.braced
    (elabBlocks plan.ctx group.braced)
  finishDocBody plan blocks

attribute [local irreducible] elabBlocks finishDocBody in
public theorem runDocBody_recovery_group_exact (plan : DocBodyPlan) (group : RecoveryGroup)
    (h : RecoveryGroupInput plan.ctx plan.raws group) :
    runDocBody plan = runBracedRecovery plan group := by
  obtain ⟨hraw, hm, hp, hgp, hn, hb, hpar, hblock⟩ := h
  unfold runDocBody runBracedRecovery
  rw [hraw]
  change (do
    finishDocBody plan (← elabBlocks plan.ctx
      #[.ctrl group.name group.pos, .group group.body group.groupPos])) = _
  rw [elabBlocks_recovery_group_exact plan.ctx group.name group.body group.pos
    group.groupPos hm hp hgp hn hb hpar hblock]
  rfl

/-- An unhandled control applied to one literal word that trimming and smart
punctuation leave fixed. -/
public def RecoveryWordInput (ctx : Ctx) (raws : Array Raw) (word : String) : Prop :=
  ∃ name pos groupPos wordPos,
    raws = #[.ctrl name pos, .group #[.word word wordPos] groupPos] ∧
    ctx.macroRoles = ({file := ""} : Ctx).macroRoles ∧
    pos.origins = [] ∧ groupPos.origins = [] ∧ wordPos.origins = [] ∧
    recoversInlineName ctx name = true ∧ smartPunct word = word ∧
    word.isEmpty = false ∧
    String.ofList (word.toList.dropWhile (· == ' ')) = word ∧
    word.trimAscii.isEmpty = false ∧
    String.ofList ((word.toList.reverse.dropWhile (· == ' ')).reverse) = word ∧
    isBlockStart ctx name raws 0 #[] = false

public theorem runDocBody_recovered_word_exact (plan : DocBodyPlan) (st : ESt) (word : String)
    (h : RecoveryWordInput plan.ctx plan.raws word) :
    Ir.blocksText ((runDocBody plan).run st).1.1.body = word := by
  obtain ⟨name, pos, groupPos, wordPos, hraw, hm, hp, hgp, hwp, hn, hs,
    he, hl, ht, hr, hb⟩ := h
  rw [hraw] at hb
  have hbs := elabBlocks_recovered_shape plan.ctx st name word pos groupPos wordPos
    hm hp hgp hwp hn hs he hl ht hr hb
  rw [← hraw] at hbs
  obtain ⟨lang, ds, hbs⟩ := hbs
  change Ir.blocksText ((((plan.finish
    (Ir.anchorReferents (referentKeys plan.ctx ((elabBlocks plan.ctx plan.raws).run st).2)
      (Ir.numberFloats ((elabBlocks plan.ctx plan.raws).run st).1))).run
      ((elabBlocks plan.ctx plan.raws).run st).2).1.attach
        (Ir.anchorReferents (referentKeys plan.ctx ((elabBlocks plan.ctx plan.raws).run st).2)
          (Ir.numberFloats ((elabBlocks plan.ctx plan.raws).run st).1))).body) = _
  rw [hbs, numbered_recovered_para, referent_recovered_para, BodyCompletion.attach_body_exact]
  split
  · rw [resolve_recovered_para]
    exact recovered_para_census plan.ctx wordPos word lang ds
  · exact recovered_para_census plan.ctx wordPos word lang ds

private def beginDoc (file : String) (raws : Array Raw) (picPre : String)
    (picSets : Array (Span × Array Raw)) (picMacros : Array (String × String))
    (picMetric : Ir.Pic.LabelMetric) (picWithdrawn : Array String)
    (listingReplies : Array ListingReply.Answer) : EM DocPreamble := do
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
  let decls := scanDecls file preamble
  -- Read before the fold, so a `\pictures` line binds the settings above it.
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
  -- Read before the fold: LaTeX sets preamble content after every selector.
  let urlFamily0 : Option Ir.Style := decls.foldl (fun fam d =>
      match d with
      | .urlstyle (some v) _ => (urlStyleFamily? v).getD fam
      | _ => fam) (← get).scope.urlFamily
  modify fun st => { st with scope := { st.scope with urlFamily := urlFamily0 }
                             packageInputs := Compat.packageInputs file raws }
  let s ← decls.foldlM applyDecl
    { ctx := { file := file, listingReplies := listingReplies
               pic := { tool := picTool0, preamble := picPre, metric := picMetric
                        withdrawn := picWithdrawn, macros := picMacros
                        sets := picSets, graphics := Compat.graphicsPath file raws } } }
  return { state := s, decls, body, trailing }

private def prepareStyledBody (file : String) (decls : Array PDecl)
    (body trailing : Array Raw) (s : PreState) : EM DocBodyPlan := do
  let mut ctx := s.ctx
  let docClass := s.docClass
  let sawClass := s.sawClass
  let classOptions := s.classOptions
  let mut page := s.page
  let sawPage := s.sawPage
  let fonts := s.fonts
  let defaultBundle := s.docClass == Ir.DocClass.slides && !s.sawTheme
  -- A seeded palette is the whole palette: the bundle's colours do not install.
  let bundle := if s.palette.seeded.isSome then
      { Theme.daylight with palette := {}, seeds := none, derived := [] }
    else Theme.daylight
  let classColors := s.docClass.classColors (Ir.Surface.ofPath file)
  let themedDs : Theme.Decls :=
    let own : Theme.Decls := { palette := { s.palette with classColors }, tokens := s.tokens
                               styles := s.styles, chrome := s.chrome }
    if defaultBundle then Theme.applyUnder bundle own else own
  let basePalette ← resolveBeamerColors ctx themedDs.palette true
  let docRoles := (← get).spans.docRoles
  let palette := match s.pageGround with
    | some c => (basePalette.declare (.role .page) c).reseed docRoles.contains
    | none => basePalette
  -- `\normalcolor` restores the ink in force when the body opens (color.sty).
  let openingInk := decls.foldl (fun pal d => match d with
    | .bodyStart source _ =>
      if source == Compat.normalInkSource then pal.restore basePalette (.role .ink)
      else match pal.resolveSource none source with
        | .ok (some c) => pal.declare (.role .ink) c
        | _ => pal
    | _ => pal) basePalette
  let tokens := themedDs.tokens
  let styles := themedDs.styles
  let chrome := themedDs.chrome
  ctx := { ctx with palette := palette, basePalette := openingInk, tokens := tokens, styles := styles
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
  if !sawClass && file.endsWith ".tex" then
    diag ctx .N0017 "no '\\documentclass'; the article page model is assumed" none
      (help := "declare \\documentclass{article} (or slides, card, resume, webpage, poster) to choose it")
  let record := docClass.record
  if page.fontSize == ({} : PageSpec).fontSize then
    let optSize := (KeyVal.items classOptions).findSome? fun o =>
      let o := match KeyVal.entry o with
        | ("fontsize", some v) => v
        | (k, _) => k
      if o.endsWith "pt" then
        ((o.dropEnd 2).toString.toNat?).filter (· > 0) |>.map fun n => Dim.pt n
      else none
    match optSize with
    | some d => page := { page with fontSize := d }
    | none =>
      if let some d := record.fontSize then
        page := { page with fontSize := d }
  -- A declared size is absolute, so its step is read against the body size the class settles.
  page := (← applyRefusedSizeLadder { s with page }).page
  if page.parskip.isNone then
    if let some g := record.parskip then
      page := { page with parskip := some g }
  let classOpts := (KeyVal.items classOptions).toList
  page := classPageDefaults record classOpts page
  let classSay (code : DiagCode) (o msg : String) : EM Unit := do
    let d := diagOf ctx code msg none (subject := some (Compat.paramSubject "documentclass" o))
    modify fun st => { st with diags := st.diags.push d }
  for o in if s.classUnknown then [] else classOpts do
    let key := (KeyVal.entry o).1
    if KeyVal.entry o matches ("twocolumn", none) | ("twocolumn", some "true") then
      classSay .W0356 key
        "class option 'twocolumn' asks for a two-column page; the text is set in one column"
    else if KeyVal.entry o matches ("draft", none) | ("draft", some "true") then
      classSay .W0356 key
        "class option 'draft' asks for a proofing mode the engine does not have; the document is rendered in full"
    else if let some why := (classOptionsInert.lookup record.model).bind (·.lookup o) then
      classSay .N0100 key s!"'\\documentclass[{o}]' → nothing: {why}"
    else unless classOptionRead record.model o || key.isEmpty do
      classSay .W0356 key s!"class option '{o}' is not honoured; the document renders without it"
  let surface := Ir.Surface.ofPath file
  if record.model == .flow && !sawPage then
    page := { page with hmargin := (page.width - surface.textBlock) / 2 }
  if !record.runningFurniture && (head.isSome || foot.isSome) then
    diag ctx .W0317
      "a card carries no running head or foot; the declaration is dropped" none
    head := none
    foot := none
  if output.formats.isEmpty then
    for f in record.formats do
      output := output.addFormat f
  if output.md.isNone then
    output := { output with md := record.mdName }
  let face := Ir.PreambleFace.ofClass record page.fontSize
  let tokens := face.fixLoadLengths tokens
  ctx := { ctx with slides := record.model == .frame
                    groundDepth := record.groundDepth
                    frameAlign := classFrameAlign classOpts
                    face := record.model == .face
                    numberHeadings := record.numberHeadings, styles := styles
                    page := page, tokens := tokens, surface := surface, lists := record.lists
                    preamble := face
                    engineTokens := engineLengthTokensOfPage page ++ classMarginTokens record.lists
                    abstractNests := s.abstractForm.getD
                      (abstractFormUnder record.abstractForm classOpts) == .quotation }
  let opening : Array Raw := decls.filterMap fun d =>
    match d with
    | .bodyStart source p => some (.ctrl (Marker.name .ink source) p)
    | _ => none
  return { ctx, raws := opening ++ body, finish := fun blocks => do
    let mut asserts := asserts
    let mut output := output
    let mut info := info
    finishBeamerColors ctx
    let pictureReport : PictureReportContext := { ctx, offset := (← get).diags.size }
    let stRefs ← get
    let table := if stRefs.labels.isEmpty then stRefs.labels
      else Ir.withFloatRows stRefs.labels (Ir.floatLabelRows blocks)
    let mut warnedRefs : Array String := #[]
    for (key, form, rpos) in stRefs.refSites do
      unless warnedRefs.contains key do
        if let some (_, some b) := table.find? (·.1 == key) then
          if b.kind.isNone && refFormNeedsKind form then
            warnedRefs := warnedRefs.push key
            diag ctx .W0380
              s!"'{key}' names a bare counter step, not a heading, equation, or float; the plain number is set"
              (some rpos)
              (help := "reference it with \\ref, or move the \\label after the numbered thing it should name")
    if (Ir.bibRefsBlocks blocks).isEmpty && (Ir.ownBibItemsBlocks blocks).isEmpty then
      for (key, span) in stRefs.spans.cites do
        let help := if ctx.surface == .markdown then
            "the document declares no bibliography; its metadata's 'bibliography: refs.bib' names \
the .bib file"
          else "the document declares no bibliography; \\bibliography{file} names the .bib file"
        modify fun st => { st with diags := st.diags.push (Diag.of .W0351
          s!"citation '{key}' has no bibliography to resolve against; it shows as '?'"
          (some span) (help := help) (subject := some key)) }
    -- The final flow palette only judges shadowing; the document keeps epoch 0.
    let stBody ← get
    let finalPalette := stBody.scope.palette.current.getD palette
    let mut shadowSaid : Array String := #[]
    for cmd in ctx.user do
      if !shadowSaid.contains cmd.name && (finalPalette.find? cmd.name).isSome then
        shadowSaid := shadowSaid.push cmd.name
        modify fun st => { st with diags := st.diags.push (Diag.of .W0342
          (s!"'\\{cmd.name}' is also a palette role; this definition freezes it, " ++
            "so the palette and the contrast check no longer reach it")
          (some cmd.span)
          (help := s!"drop the definition and '\\{cmd.name}' colours as declared; " ++
            s!"declared: {String.intercalate ", " (finalPalette.entries.toList.map (·.1.key))}")) }
    let mut logo := (← get).logos.main
    if !record.runningFurniture && logo.isSome then
      diag ctx .W0317
        "a card carries no logo; the declaration is dropped" none
      logo := none
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
    let st ← get
    let fallback (cur : Option String) (src : Option (Array Inline)) : Option String :=
      match cur with
      | some s => some s
      | none =>
        src.bind fun xs =>
          let t := Ir.metaText xs
          if t.isEmpty then none else some t
    info := { info with
      title := fallback info.title st.title
      author := fallback info.author st.author }
    let doc : Doc := {
      docClass := docClass
      surface := surface
      classOptions := classOptions
      abstractForm := s.abstractForm.getD (abstractFormUnder record.abstractForm classOpts)
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
      frameKeys := if defaultBundle then Theme.daylight.frameKeys else s.frameKeys
      sectionPages := { theme := if defaultBundle then Theme.daylight.sectionPage
                                   else s.themeSectionPage
                        atSection := (← get).sectionHook
                        atSubsection := (← get).subsectionHook }
      ownRoles := (← get).spans.docRoles
      styles := styles
      info := info
      output := output
      asserts := asserts
      allow := allow
      citeSetup := (← get).citeSetup
      pictureTool := ctx.pic.tool
      figureConvert := ctx.pic.convert
      pictureSrcs := (← get).pictures
      picturePreamble := ctx.pic.preamble
      graphicsPath := ctx.pic.graphics
      -- Only a picture request carries macros, so a definition alone moves no `Doc`.
      pictureMacros := if (← get).pictures.isEmpty then #[] else ctx.pic.macros
      salvage := (← get).salvage
      frameRestart := (← get).frameRestart
      listNotes := (← get).ctr.notesAt.map (·, 0)
    }
    return { doc, table, pictureReport, locale := ctx.locale, resolve := !stRefs.refSites.isEmpty }
  }

/-- Applies refused title and size bodies and class defaults, returning the
body plan. -/
public def prepareDocBody (file : String) (preamble : DocPreamble) : EM DocBodyPlan := do
  let s ← applyRefusedTitleStyle preamble.state
  prepareStyledBody file preamble.decls preamble.body preamble.trailing s

/-- Elaborates the body that follows a completed declaration fold. -/
public def finishPreamble (file : String) (preamble : DocPreamble) :
    EM (Doc × Ir.RefTable × PictureReportContext) := do
  runDocBody (← prepareDocBody file preamble)

public theorem finishPreamble_run_congr (file : String) (preamble : DocPreamble)
    (left right : ESt)
    (h : (applyRefusedTitleStyle preamble.state).run left =
      (applyRefusedTitleStyle preamble.state).run right) :
    (finishPreamble file preamble).run left = (finishPreamble file preamble).run right := by
  change
    (let (s, st) := (applyRefusedTitleStyle preamble.state).run left
     ((do runDocBody (← prepareStyledBody file preamble.decls preamble.body
       preamble.trailing s)) : EM _).run st) =
    (let (s, st) := (applyRefusedTitleStyle preamble.state).run right
     ((do runDocBody (← prepareStyledBody file preamble.decls preamble.body
       preamble.trailing s)) : EM _).run st)
  rw [h]

private def elabDocCore (file : String) (raws : Array Raw) (picPre : String)
    (picSets : Array (Span × Array Raw)) (picMacros : Array (String × String))
    (picMetric : Ir.Pic.LabelMetric) (picWithdrawn : Array String)
    (listingReplies : Array ListingReply.Answer) :
    EM (Doc × Ir.RefTable × PictureReportContext) := do
  let preamble ← beginDoc file raws picPre picSets picMacros picMetric picWithdrawn listingReplies
  finishPreamble file preamble

/-- Elaborates a document and names the unread settings of its engine-drawn
pictures. -/
public def elabDoc (file : String) (raws : Array Raw) (picPre : String := "")
    (picSets : Array (Span × Array Raw) := #[])
    (picMacros : Array (String × String) := #[])
    (picMetric : Ir.Pic.LabelMetric := fun _ _ => {})
    (picWithdrawn : Array String := #[])
    (listingReplies : Array ListingReply.Answer := #[]) :
    EM (Doc × Ir.RefTable) := fun initial =>
  let ((doc, table, report), st) :=
    (elabDocCore file raws picPre picSets picMacros picMetric picWithdrawn listingReplies).run initial
  ((doc, table), finishPictureKeys report doc picSets st)

/-- Where a document's requests were declared, for the driver's missing-file
diagnostics. -/
public structure ReqSpans where
  /-- The input-reader calls that produced the prepared surface. -/
  inputAttempts : Array Compat.InputAttempt := #[]
  /-- Each `\bibliography` marker's span, keyed by its source. -/
  bib : Array (String × Span) := #[]
  /-- Each image source's first span, file images and boundary pictures alike. -/
  images : Array (String × Span) := #[]
  /-- Each top-level frame's opening span, keyed by its block index in
  `Doc.body`. -/
  frames : Array (Nat × Span) := #[]
  /-- The boundary pictures, by id, that the rendered subset draws in part
  and draws natively when no tool does. -/
  fallbacks : Array String := #[]
  /-- The pictures, by id, the rendered subset draws in part under
  `\pictures{ tool = none }`. -/
  declined : Array String := #[]
  /-- Each reference key's first site. -/
  refs : Array (String × Span) := #[]
  /-- The label table resolution read. -/
  labels : Ir.RefTable := #[]
  /-- Inline code in a language only the highlighter reads, as language and
  source. -/
  code : Array (String × String) := #[]
  /-- The faces the document itself declares, at sites no other warning names, which the face
  set's judge reads. -/
  faces : Array (String × Span) := #[]
  deriving Repr, BEq, Inhabited

/-- The rewritten source and scans every elaboration of one document reads. -/
public structure Prepared where
  raws : Array Raw
  picPre : String
  picSets : Array (Span × Array Raw)
  picMacros : Array (String × String)
  warned : Array String
  compatDiags : Array Diag
  /-- The original spellings, kept after compatibility expands macros. -/
  sourceTriggers : Compat.SourceTriggers := {}
  /-- The input-reader calls execution made. -/
  inputAttempts : Array Compat.InputAttempt := #[]
  /-- The source of each value a construct execution refused carried. -/
  mentions : Array String := #[]
  /-- The highlighter answers every elaboration of this input reads. -/
  listingReplies : Array ListingReply.Answer := #[]
  /-- The notes each bibliography list's fields set, in document order; empty
  on a first elaboration. -/
  listNotes : Array Nat := #[]

/-- The name a definer's head binds, when its next item (past spaces and a
`*`) is a one-word group. -/
private def definedEnvName : List Raw → Option String
  | .space :: rest => definedEnvName rest
  | .sym '*' _ :: rest => definedEnvName rest
  | .group #[.word n _] _ :: _ => some n
  | _ => none

mutual

/-- Settles split environment halves as a plain parse does; the `skip`
groups a refused definition still holds pass through unsettled. -/
-- conserves: none — rebuilds the parse's recovery tree
private def settleList (file : String) (skip : Nat) (out : Array Raw)
    (ds : Array Diag) : List Raw → Array Raw × Array Diag
  | [] => (out, ds)
  | .ctrl d p :: rest =>
    -- premise: refusedEnvChecks — a refused definition's halves owe nothing
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

/-- Settles every definer body's split halves in a parsed tree. -/
public def settleSplits (file : String) (raws : Array Raw) : Array Raw × Array Diag :=
  settleList file 0 #[] #[] raws.toList

public theorem settleSplits_package_exact (file command names : String)
    (pos groupPos namePos : Pos) :
    settleSplits file (Compat.packageCall command names pos groupPos namePos) =
      (Compat.packageCall command names pos groupPos namePos, #[]) := by
  simp [settleSplits, Compat.packageCall_exact, settleList, settleOne]

/-- Executes input-bearing macros with the driver's reader, after settling
split halves. -/
public def executeInputs [Monad m] (reader : Compat.InputReader m) (file : String)
    (raws : Array Raw) : m Compat.Executed :=
  let (raws, splitDiags) := settleSplits file raws
  Compat.executeInputs reader file raws
    (provideKeeps := providedNames) (diags := splitDiags) (ignoredDefs := ignoredDefNames)

/-- Resumes execution with a file answer, after settling its split halves. -/
public def resumeInput [Monad m] (reader : Compat.InputReader m) (context : Compat.InputContext)
    (file : String) (raws : Array Raw) : m (Array Raw × Compat.InputContext) :=
  let (raws, splitDiags) := settleSplits file raws
  Compat.resumeInput reader context raws splitDiags

/-- An included markdown file's answer: under hybrid its TeX reading run through the walk, the
package's options it sets ending with it, else its raws kept from the walk at `pos`. -/
public def markdownAnswer [Monad m] (reader : Compat.InputReader m) (context : Compat.InputContext)
    (file : String) (raws : Array Raw) (hybrid : Bool) (pos : Pos) :
    m (Array Raw × Compat.InputContext) := do
  if hybrid then
    let (answer, after) ← resumeInput reader context file raws
    return (answer, after.restoreMarkdown context.markdown)
  return context.keep raws pos

/-- Finishes preparation: text rewriting over the compatibility walk's
output, with the caller's scans. -/
public def prepareRewritten (file : String) (picScan : Compat.BoundaryScan)
    (picMacros : Array (String × String)) (sourceTriggers : Compat.SourceTriggers)
    (priorDiags : Array Diag)
    (rewritten : Array Raw × Array Diag × Array String)
    (inputAttempts : Array Compat.InputAttempt := #[]) (mentions : Array String := #[]) :
    Prepared :=
  let (raws, compatDiags, warned) := rewritten
  let (raws, textDiags, warned) := Compat.rewriteText file raws warned
  { raws := raws, picPre := picScan.pre, picSets := picScan.sets
    picMacros := picMacros, warned := warned
    compatDiags := priorDiags ++ compatDiags ++ textDiags
    sourceTriggers := sourceTriggers, inputAttempts := inputAttempts, mentions := mentions }

/-- Prepares a document whose macro and input execution already ran. -/
public def prepareExecuted (file : String) (executed : Compat.Executed) : Prepared :=
  let picScan := Compat.boundaryScan file executed.raws
  let picMacros := macroScan executed.raws
  prepareRewritten file picScan picMacros executed.sourceTriggers
    (Compat.unusedLengths file executed.raws) (Compat.rewriteExecuted executed) executed.inputAttempts
    executed.mentions

private theorem prepareRewritten_carried_exact (file : String)
    (scan : Compat.BoundaryScan) (macros : Array (String × String))
    (triggers : Compat.SourceTriggers) (prior : Array Diag)
    (rewritten : Array Raw × Array Diag × Array String)
    (attempts : Array Compat.InputAttempt) (mentions : Array String) :
    (prepareRewritten file scan macros triggers prior rewritten attempts mentions).inputAttempts =
        attempts ∧
      (prepareRewritten file scan macros triggers prior rewritten attempts mentions).sourceTriggers =
        triggers := by
  rcases rewritten with ⟨raws, diags, warned⟩
  unfold prepareRewritten
  cases Compat.rewriteText file raws warned
  exact ⟨rfl, rfl⟩

attribute [local irreducible] prepareRewritten macroScan in
public theorem prepareExecuted_inputAttempts_exact (file : String) (executed : Compat.Executed) :
    (prepareExecuted file executed).inputAttempts = executed.inputAttempts := by
  unfold prepareExecuted
  exact (prepareRewritten_carried_exact file _ _ _ _ _ _ _).1

attribute [local irreducible] prepareRewritten macroScan in
public theorem prepareExecuted_sourceTriggers_exact (file : String) (executed : Compat.Executed) :
    (prepareExecuted file executed).sourceTriggers = executed.sourceTriggers := by
  unfold prepareExecuted
  exact (prepareRewritten_carried_exact file _ _ _ _ _ _ _).2

/-- Settles, scans, executes and rewrites a parsed document, once. -/
public def prepare (file : String) (raws : Array Raw) : Prepared :=
  let (raws, splitDiags) := settleSplits file raws
  let picScan := Compat.boundaryScan file raws
  let picMacros := macroScan raws
  let executed := Compat.execute file raws
    (provideKeeps := providedNames) (ignoredDefs := ignoredDefNames)
  prepareRewritten file picScan picMacros executed.sourceTriggers
    (splitDiags ++ Compat.unusedLengths file executed.raws) (Compat.rewriteExecuted executed)
    (mentions := executed.mentions)

/-- Whether the source holds a natively drawn picture, and whether one sets a
formula. -/
public structure PicWants where
  draws : Bool := false
  math : Bool := false

mutual

-- conserves: none — answers two Bools, not a tree
private def picWantsLevel (inPic : Bool) (acc : PicWants) : List Raw → PicWants
  | [] => acc
  | r :: rest => picWantsLevel inPic (picWantsRaw inPic acc r) rest

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

/-- What a source's pictures could need of a face; a false `draws` means no
picture is ever measured. -/
public def picWants (raws : Array Raw) : PicWants :=
  picWantsLevel false {} raws.toList

/-- The preamble elaborated as a document with an empty body, its diagnostics
discarded. -/
public def preambleDoc (file : String) (p : Prepared) : Doc :=
  let docIdx := p.raws.findIdx? fun r =>
    match r with
    | .env "document" _ _ => true
    | _ => false
  let raws := match docIdx with
    | some idx => (p.raws.extract 0 idx).push (.env "document" #[] { line := 0, col := 0 })
    | none => #[.env "document" #[] { line := 0, col := 0 }]
  ((elabDoc file raws p.picPre p.picSets p.picMacros).run
    { warnedUnknown := p.warned }).1.1

/-- An unlocated report for a recovery that arrived without its producer's
diagnostic. -/
public def recoveryDiagnostic (item : Ir.Recovered) : Diag :=
  Diag.of item.code
    s!"{item.code.meaning}; content from '\\{item.command}' was kept"
    none (subject := some item.subject)

public def recoveryMatches (item : Ir.Recovered) (d : Diag) : Bool :=
  decide (d.kind = item.code) && d.subject == some item.subject

public def accountRecoveredItem (diags : Array Diag) (item : Ir.Recovered)
    (observed : Array Diag := #[]) : Array Diag :=
  if diags.any (recoveryMatches item) then diags
  else
    let reports := observed.filter (recoveryMatches item)
    if reports.isEmpty then diags.push (recoveryDiagnostic item)
    else diags ++ reports

/-- Accounts for each recovery the log misses with its producer's reports,
or else an unlocated one. -/
public def accountRecovered (items : Array Ir.Recovered) (diags : Array Diag)
    (observed : Array Diag := #[]) : Array Diag := Id.run do
  let mut diags := diags
  for item in items do
    diags := accountRecoveredItem diags item observed
  return diags

public theorem recoveryDiagnostic_subject_exact (item : Ir.Recovered) :
    (recoveryDiagnostic item).subject = some item.subject := by
  simp only [recoveryDiagnostic, Diag.of_record_exact]

public theorem recoveryDiagnostic_code_exact (item : Ir.Recovered) :
    (recoveryDiagnostic item).kind = item.code := by
  simp only [recoveryDiagnostic, Diag.of_record_exact]

public theorem accountRecoveredItem_replay_exact (diags observed : Array Diag)
    (item : Ir.Recovered)
    (hmissing : diags.any (recoveryMatches item) = false)
    (hevidence : (observed.filter (recoveryMatches item)).isEmpty = false) :
    accountRecoveredItem diags item observed =
      diags ++ observed.filter (recoveryMatches item) := by
  simp only [accountRecoveredItem, hmissing, hevidence, Bool.false_eq_true, ↓reduceIte]

private theorem warnUnknownCmd_replay_exact (ctx : Ctx) (name text : String)
    (optionRun : Bool) (pos : Pos) (st : ESt) (diags : Array Diag)
    (hmissing : diags.any (recoveryMatches
      { code := (unknownCmdDiag name {}).1, command := name, text }) = false) :
    let item : Ir.Recovered :=
      { code := (unknownCmdDiag name {}).1, command := name, text }
    let observed := ((warnUnknownCmd ctx name optionRun pos).run st).2.spans.recoveryDiags
    accountRecoveredItem diags item observed =
      diags ++ observed.filter (recoveryMatches item) := by
  apply accountRecoveredItem_replay_exact _ _ _ hmissing
  rw [warnUnknownCmd_recovery_exact]
  rcases warnUnknownCmd_push_exact ctx name optionRun pos st with ⟨d, _, hd, hk, hs⟩
  apply Array.isEmpty_eq_false_iff_exists_mem.mpr
  refine ⟨d, Array.mem_filter.mpr ⟨Array.mem_of_back? hd, ?_⟩⟩
  have hc := hk.trans (unknownCmdDiag_shape_id name (RunShape.one optionRun))
  simp [recoveryMatches, hc, hs, Ir.Recovered.subject]

public theorem accountRecovered_run_exact (items : Array Ir.Recovered) (diags observed : Array Diag) :
    accountRecovered items diags observed =
      items.foldl (fun ds item => accountRecoveredItem ds item observed) diags := by
  simp [accountRecovered, Array.forIn_pure_yield_eq_foldl]

public theorem accountRecoveredItem_mem (diags : Array Diag) (item : Ir.Recovered)
    (observed : Array Diag) (d : Diag) (h : d ∈ diags) :
    d ∈ accountRecoveredItem diags item observed := by
  unfold accountRecoveredItem
  split
  · exact h
  · dsimp only
    split
    · exact Array.mem_push.mpr (Or.inl h)
    · exact Array.mem_append.mpr (Or.inl h)

private theorem accountRecoveredFold_mem (items : List Ir.Recovered)
    (observed diags : Array Diag) (d : Diag) (h : d ∈ diags) :
    d ∈ items.foldl (fun ds item => accountRecoveredItem ds item observed) diags := by
  induction items generalizing diags with
  | nil => exact h
  | cons item _ ih => exact ih _ (accountRecoveredItem_mem diags item observed d h)

public theorem accountRecovered_mem (items : Array Ir.Recovered) (diags observed : Array Diag)
    (d : Diag) (h : d ∈ diags) :
    d ∈ accountRecovered items diags observed := by
  rw [accountRecovered_run_exact, ← Array.foldl_toList]
  exact accountRecoveredFold_mem items.toList observed diags d h

/-- Runs the document judges over an elaborated document and assembles its
log and request spans. -/
public def completePrepared (file : String) (p : Prepared) (earlier : Array Diag)
    (doc : Doc) (table : Ir.RefTable) (report : PictureReportContext) (st : ESt) :
    Doc × Array Diag × ReqSpans :=
  let contrast := Contrast.docDiags doc
    (fun pal name c => colorSiteOf st.spans.colors name c
      (declarations := st.spans.colorDeclarations) (palette := some pal))
  let st := finishPictureKeys report doc p.picSets st
  let outline := Ir.outlineDiags doc
  -- File images only: the driver judges boundary pictures after fulfilment.
  let alt := Ir.altDiags doc fun src => (st.spans.images.find? (·.1 == src)).map (·.2)
  let links := Ir.linkDiags doc
  let sequences := Ir.footerSequenceDiags doc
  let unread := if st.spans.tokenKeys.isEmpty then #[]
    else unreadPaletteKeys (doc.page.drawn.foldl (fun acc r => acc ++ Ir.colorNames r.color)
      st.spans.colorReads) st.spans.tokenKeys
  let unread := unread ++ unreadFrameTitleFont doc st.spans.frameTitleFont st.spans.frameTitleRestated
  let said := earlier ++ p.compatDiags ++ st.diags ++ contrast ++ outline ++ alt ++ links ++
    sequences ++ unread ++ Ir.boxDiags doc.page
  -- A declaration a definition's replacement text makes at its call is the definition's.
  let settings := st.settings.filter fun d =>
    d.span.pos.command.isSome && p.sourceTriggers.writtenAt d.span.file d.span.pos == d.span.pos.command
  -- premise: Tests.UnusedSettings.accountingChecks — a site another warning or a split names
  let named := if settings.isEmpty then #[] else
    said.filterMap (fun d => if d.severity == .note then none else d.span) ++ st.unjudged
  let unused := if settings.isEmpty then #[] else
    -- A title block reads the title page's style whatever datum it sets.
    let shown := UnusedSetting.shown doc (if st.titleDone then #["titlepage"] else #[])
    -- A construct the engine refused or could not resolve still names what it names.
    let words (acc : Std.HashSet String) (src : String) := (Ir.colorNames src).foldl (·.insert ·) acc
    let read := doc.salvage.foldl (fun acc r => words acc r.text) (p.mentions.foldl words st.mentions)
    let read := doc.page.drawn.foldl (fun acc r => words acc r.color)
      (st.spans.colorReads.foldl (·.insert ·) read)
    UnusedSetting.diags settings shown read named
  (doc, Diag.tallySites ((accountRecovered doc.salvage (said ++ unused)
    st.spans.recoveryDiags).map p.sourceTriggers.attribute),
    { inputAttempts := p.inputAttempts
      bib := st.spans.bib
      images := st.spans.images
      frames := st.spans.frames.sites
      fallbacks := st.spans.fallbacks
      declined := st.spans.declined
      code := st.spans.code
      refs := (st.refSites.foldl (init := (#[], (∅ : Std.HashSet String)))
        fun (out, seen) (key, _, pos) =>
          if seen.contains key then (out, seen)
          else (out.push (key, ⟨file, pos⟩), seen.insert key)).1
      labels := table
      faces := UnusedSetting.faceSites settings named })

public theorem completePrepared_inputAttempts_exact (file : String) (p : Prepared)
    (earlier : Array Diag) (doc : Doc) (table : Ir.RefTable)
    (report : PictureReportContext) (st : ESt) :
    (completePrepared file p earlier doc table report st).2.2.inputAttempts =
      p.inputAttempts := by rfl

/-- Runs the declaration fold over prepared input, keeping its state. -/
public def preparedPreamble (file : String) (p : Prepared)
    (picMetric : Ir.Pic.LabelMetric := fun _ _ => {})
    (picWithdrawn : Array String := #[]) : DocPreamble × ESt :=
  -- Starts from the rewrite's warn-once keys, so no warning is said twice.
  (beginDoc file p.raws p.picPre p.picSets p.picMacros picMetric picWithdrawn
    p.listingReplies).run { warnedUnknown := p.warned, ctr := { listNotes := p.listNotes } }

/-- The body plan and state after the declaration fold and class defaults. -/
public def preparedBody (file : String) (p : Prepared)
    (picMetric : Ir.Pic.LabelMetric := fun _ _ => {})
    (picWithdrawn : Array String := #[]) : DocBodyPlan × ESt :=
  let (preamble, initial) := preparedPreamble file p picMetric picWithdrawn
  (prepareDocBody file preamble).run initial

/-- Finishes a preamble and runs the document judges. -/
public def runPreamble (file : String) (p : Prepared) (earlier : Array Diag)
    (preamble : DocPreamble) (initial : ESt) : Doc × Array Diag × ReqSpans :=
  let ((doc, table, report), st) := (finishPreamble file preamble).run initial
  completePrepared file p earlier doc table report st

/-- Elaborates prepared input against a label metric, with the withdrawn
boundary requests. -/
public def runPrepared (file : String) (p : Prepared) (earlier : Array Diag := #[])
    (picMetric : Ir.Pic.LabelMetric := fun _ _ => {})
    (picWithdrawn : Array String := #[]) : Doc × Array Diag × ReqSpans :=
  let (preamble, st) := preparedPreamble file p picMetric picWithdrawn
  runPreamble file p earlier preamble st

attribute [local irreducible] preparedPreamble prepareDocBody runDocBody completePrepared in
public theorem runPrepared_body_exact (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Pic.LabelMetric) (withdrawn : Array String) :
    runPrepared file p earlier metric withdrawn =
      let (plan, initial) := preparedBody file p metric withdrawn
      let ((doc, table, report), st) := (runDocBody plan).run initial
      completePrepared file p earlier doc table report st := by rfl

attribute [local irreducible] preparedPreamble finishPreamble completePrepared in
public theorem runPrepared_complete_exact (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Pic.LabelMetric) (withdrawn : Array String) :
    ∃ doc table report st,
      runPrepared file p earlier metric withdrawn =
        completePrepared file p earlier doc table report st := by
  cases hphase : preparedPreamble file p metric withdrawn with
  | mk preamble initial =>
    cases hresult : (finishPreamble file preamble).run initial with
    | mk result st =>
      obtain ⟨doc, table, report⟩ := result
      refine ⟨doc, table, report, st, ?_⟩
      simp only [runPrepared, hphase, runPreamble, hresult]

public theorem runPrepared_inputAttempts_exact (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Pic.LabelMetric) (withdrawn : Array String) :
    (runPrepared file p earlier metric withdrawn).2.2.inputAttempts = p.inputAttempts := by
  obtain ⟨doc, table, report, st, h⟩ :=
    runPrepared_complete_exact file p earlier metric withdrawn
  rw [h, completePrepared_inputAttempts_exact]

/-- Prepares and elaborates parsed input with its request spans, leaving
unresolved references to the driver's judge. -/
public def runRawsSpanned (file : String) (raws : Array Raw) (earlier : Array Diag := #[])
    (picMetric : Ir.Pic.LabelMetric := fun _ _ => {}) :
    Doc × Array Diag × ReqSpans :=
  runPrepared file (prepare file raws) earlier picMetric

public def ReqSpans.spanOf (rs : Array (String × Span)) (key : String) : Option Span :=
  (rs.find? (·.1 == key)).map (·.2)

/-- Runs a pass, reruns it with its fallback requests withdrawn when it has
any, and judges unresolved references. -/
public def finishPreparedRuns (pass : Array String → Doc × Array Diag × ReqSpans) :
    Doc × Array Diag :=
  let first := pass #[]
  let (doc, diags, rs) := if first.2.2.fallbacks.isEmpty then first
    else pass first.2.2.fallbacks
  (Ir.eraseLocations doc, Diag.tallySites (diags ++ Ir.refDiags rs.labels (ReqSpans.spanOf rs.refs) doc))

public def runPreparedFinal (file : String) (p : Prepared) (earlier : Array Diag)
    (picMetric : Ir.Pic.LabelMetric) : Doc × Array Diag :=
  finishPreparedRuns (fun withdrawn => runPrepared file p earlier picMetric withdrawn)

public theorem runPreparedFinal_preamble_exact (file : String) (p : Prepared)
    (earlier : Array Diag) (metric : Ir.Pic.LabelMetric) :
    runPreparedFinal file p earlier metric =
      finishPreparedRuns (fun withdrawn =>
        let phase := preparedPreamble file p metric withdrawn
        runPreamble file p earlier phase.1 phase.2) := by rfl

/-- Elaborates parsed input with no file request fulfilled. -/
public def runRaws (file : String) (raws : Array Raw) (earlier : Array Diag := #[])
    (picMetric : Ir.Pic.LabelMetric := fun _ _ => {}) : Doc × Array Diag :=
  runPreparedFinal file (prepare file raws) earlier picMetric

/-- Elaborates a surface whose file requests execution already fulfilled. -/
public def runExecuted (file : String) (executed : Compat.Executed) (earlier : Array Diag := #[])
    (picMetric : Ir.Pic.LabelMetric := fun _ _ => {}) : Doc × Array Diag :=
  runPreparedFinal file (prepareExecuted file executed) earlier picMetric

/-- A markdown or code file's raws elaborated as the driver runs them, the walk left out. -/
public def runKept (file : String) (raws : Array Raw) (earlier : Array Diag := #[])
    (picMetric : Ir.Pic.LabelMetric := fun _ _ => {}) : Doc × Array Diag :=
  runExecuted file (Compat.kept file raws) earlier picMetric

/-- The same with the spans its requests name. -/
public def runKeptSpanned (file : String) (raws : Array Raw) (earlier : Array Diag := #[])
    (picMetric : Ir.Pic.LabelMetric := fun _ _ => {}) : Doc × Array Diag × ReqSpans :=
  runPrepared file (prepareExecuted file (Compat.kept file raws)) earlier picMetric

public def run (file input : String) : Doc × Array Diag :=
  let (toks, lexDiags) := Lex.lex file input
  let (raws, parseDiags) := Parse.parse file toks
  runRaws file raws (lexDiags ++ parseDiags)

private theorem elabBlocksGo_end (ctx : Ctx) (st : ESt) (raws : Array Raw) (i : Nat)
    (blocks : Array Block) (gen : Nat)
    (hm : ctx.macroRoles = ({file := ""} : Ctx).macroRoles) (hi : raws.size ≤ i) :
    (elabBlocksGo ctx raws i blocks #[] gen).run st = (blocks, st) := by
  have hf : (flowCtx ctx st gen).macroRoles = ({file := ""} : Ctx).macroRoles := by
    unfold flowCtx
    split <;> exact hm
  rw [elabBlocksGo, run_get]
  simp only [show ¬ i < raws.size from Nat.not_lt.mpr hi, ↓reduceDIte]
  simp [blockMacroStep, flowMCtx, hf, blockMacroKinds, hi, flushPara, carryDecls_empty,
    closeBlockFrameSources, commonOrigins, moveMacroRuns, closeMacroRuns, MacroRoles.empty]
  rfl

end LeanTex.Core.Elab
