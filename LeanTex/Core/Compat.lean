import LeanTex.Core.Lex
import LeanTex.Core.Parse
import LeanTex.Core.Theme
import LeanTex.Core.Decl
import LeanTex.Core.Ir

namespace LeanTex.Core.Compat

open LeanTex.Core LeanTex.Core.Parse

/-! # LaTeX idioms, spelled natively

A document written for lualatex spends its preamble asking packages for what
this engine provides directly. Each idiom below is rewritten into the native
declaration before elaboration, with a note saying what it became, so the
document compiles as written and its author can see the shorter spelling.

The rewrite works on the parsed tree, never on text, so it cannot unbalance a
brace it did not create; and translated content re-enters through the lexer
and parser, so it obeys exactly the rules hand-written input does. -/

/-- Packages whose whole job the engine does natively. Seeing one is a note,
not a warning: nothing was lost at the `\usepackage` line — a construct one
of these packages provides that the engine cannot render is named where it
is used, never at the load (`tikzpicture` renders its subset and W0334 or
E0333 names each shape outside it; `\appendix` is an unknown command and
W0301 says so where it stands, and so do `\nicefrac` and `\multirow` when
a document actually uses them). `xurl` is `url` with better breaking;
`amsfonts` is a subset of what `amssymb`/`unicode-math` already provide;
`caption`/`subcaption` land on the caption path, their option interface
judged at `\captionsetup` (honoured or W0354, never silent). -/
def nativePackages : List String :=
  ["geometry", "hyperref", "xcolor", "color", "microtype", "enumitem", "babel",
   "beamerposter",
   "fontspec", "url", "xurl", "scrlayer-scrpage", "inputenc", "fontenc", "lmodern",
   "amsmath", "amssymb", "amsfonts", "unicode-math", "parskip", "titlesec", "fancyhdr",
   "textcomp", "csquotes", "polyglossia", "graphicx", "booktabs", "array",
   "calc", "etoolbox", "xparse", "kvoptions", "setspace", "soul", "tikz",
   "caption", "subcaption", "nicefrac", "multirow",
   "appendixnumberbeamer", "natbib"]

/-- Classes that are an `article` with different defaults. -/
def articleClasses : List String :=
  ["scrartcl", "scrreprt", "scrbook", "report", "book", "memoir", "letter"]

/-- Résumé classes: the same flow model with the résumé genre's contract —
`moderncv` and `res` map onto the native `resume` class, as `beamer` maps
onto `slides`. -/
def resumeClasses : List String :=
  ["moderncv", "res"]

/-- Commands that configure TeX's own machinery and change nothing this
engine models — the test every entry must pass to earn silence; a construct
that fails it warns from `configSkip` instead. Defended entry by entry:
catcode and register machinery has no counterpart here (`makeatletter`,
`makeatother`, `relax`, `newlength`); `clearpairofpagestyles` resets KOMA
furniture defaults to the empty state this engine starts from;
`frenchspacing`/`nonfrenchspacing` toggle inter-sentence space the engine
sets uniformly either way; `raggedbottom`/`flushbottom` pick a vertical
distribution the page-opening `vdist` obligation will own (AGENTS table);
`noindent` and `urlstyle` adjust detail the engine does not yet
style. Table rules (`midrule`, `toprule`, …) are NOT here: they are the
table elaborator's vocabulary and must reach it. -/
def meaningFree : List (String × Nat) :=
  [("makeatletter", 0), ("makeatother", 0), ("relax", 0), ("noindent", 0),
   ("clearpairofpagestyles", 0), ("urlstyle", 1),
   ("KOMAoptions", 1), ("newlength", 1), ("frenchspacing", 0),
   ("nonfrenchspacing", 0),
   ("raggedbottom", 0), ("flushbottom", 0),
   ("selectfont", 0),
   ("column", 1)]

/-- Declarations whose loss is real — justification, breaking tolerance,
hyphenation language, page furniture — skipped with a warning that names
what changed, never silently: they used to sit in the silent list under a
comment claiming they say nothing about the document, and they do. Each
entry: arguments consumed, the message, the help. -/
def configSkip : List (String × Nat × String × Option String) :=
  [("raggedright", 0,
    "'\\raggedright' asks for unjustified setting; the document stays justified",
    some "declare \\page{ justify = false }"),
   -- The alignment declarations (every LaTeX environment is also a command
   -- pair, so `\flushleft` is a legal spelling): a block alignment axis is
   -- owed (the `align` obligation row); until it lands each names its loss.
   ("flushleft", 0,
    "'\\flushleft' asks for left-aligned unjustified setting; the declared justification stands",
    some "declare \\page{ justify = false }"),
   ("flushright", 0,
    "'\\flushright' asks for right-aligned setting; content keeps its alignment",
    none),
   ("raggedleft", 0,
    "'\\raggedleft' asks for right-aligned ragged setting; content keeps its alignment",
    none),
   ("fontseries", 1,
    "'\\fontseries' selects a font series; the family's regular weight is used",
    none),
   ("sloppy", 0,
    "'\\sloppy' loosens TeX's line-breaking tolerance; the breaker keeps \
its own and an overfull line warns by itself", none)]

/-- Beamer configuration commands: how many `{...}` arguments each carries.
The engine has no beamer templating layer, so each is skipped whole — the
construct, its options, and its arguments — with one warning naming it (and
its native spelling, where one exists). What must never happen is the
arguments leaking into elaboration as stray content (that was an E0313
cascade per construct). `\usetheme` is not here: it rewrites to `\theme`.
Neither is `\setbeamertemplate`: `frame footer` has a native meaning
(`\framefoot`) and its own arm; every other template skips there. And
neither are `\usefonttheme` and `\setbeameroption`, whose own arms silence
the one argument each that asks for what the engine already does. -/
def beamerConfig : List (String × Nat) :=
  [("usecolortheme", 1),
   ("addtobeamertemplate", 3),
   ("setbeamerfont", 2), ("setbeamercolor", 2),
   ("beamertemplatenavigationsymbolsempty", 0)]

/-- The native spelling a skipped beamer construct now has, named in its
warning's help: a warning the author can act on beats a dead end. -/
def beamerNative : List (String × String) :=
  [("usecolortheme", "\\theme{name} selects a token bundle; \\palette overrides its entries"),
   ("usefonttheme", "\\fonts selects families; \\style{element}{ font = {...} } styles one element"),
   ("setbeamercolor", "declare the colour with \\palette{ name = #RRGGBB }"),
   ("setbeamerfont", "declare it with \\style{element}{ font = {...} }"),
   ("setbeamertemplate", "'frame footer' translates to \\framefoot{...}; \\style{element}{...} \
styles elements; \\runningfoot sets a document footer"),
   ("addtobeamertemplate", "\\style{element}{...} styles elements; \\framefoot sets a frame footer")]

private structure St where
  file : String
  diags : Array Diag := #[]
  /-- Running-content slots gathered across `\ihead`/`\chead`/`\ohead`,
  landing as one declaration once the preamble ends. Slot 0 inner, 1 centre,
  2 outer — one entry per slot: a same-slot repeat replaces, as fancyhdr
  defines it (fancyhdr manual §2: `\lhead` *redefines* the field). -/
  head : Array (Nat × String) := #[]
  foot : Array (Nat × String) := #[]
  runPos : Pos := ⟨1, 1⟩
  runFrom : Nat := 1
  /-- Upcoming groups that are macro bodies, where `#k` names a parameter:
  one for a `\define`/`\newcommand` body, two for `\newenvironment`'s begin
  and end halves. Scoped: descending into a group consumes one and shields
  the count from the group's own definitions. -/
  bodyNext : Nat := 0
  /-- A `\usetheme` was seen: `\alert` then maps to the theme's alert colour
  rather than the unthemed bold stand-in. -/
  themed : Bool := false
  /-- The main language's BCP 47 tag, from babel's package options (last
  language option = main, babel's rule): what `\enquote` reads its quote
  delimiters through. -/
  mainLang : String := "en"
  /-- Inside the document environment: where a preamble declaration —
  `\usepackage` first among them — is a placement defect (W0340), never
  a support question (W0103). -/
  inDoc : Bool := false
  /-- Constructs already warned about: forty frames sharing one unsupported
  idiom are one problem, not forty. -/
  warned : Array String := #[]
  /-- Control words the document has defined so far, recorded by the
  conditional pass: what `\ifdefined` reads. Flat — TeX's group-local
  scoping is not modelled here. -/
  defined : Array String := #[]
  /-- `\newif` flags by base name (`\newif\ifshowdetail` records
  `showdetail`, initially false — plain TeX's `\newif` sets `\iffalse`)
  with the value the last `\Xtrue`/`\Xfalse` gave. Flat, like `defined`. -/
  flags : Array (String × Bool) := #[]
  /-- Command names the rewrite walk has bound so far, in document order:
  what `\providecommand`'s keep-existing policy reads. Separate from
  `defined`, which the conditional pass fills for the whole document
  before any rewrite runs — a policy about "before this point" cannot
  read a whole-document set. -/
  bound : Array String := #[]

private abbrev M := StateM St

/-- The TeX82 primitive control words — a closed, documented list (Knuth,
The TeXbook, Appendix I marks each primitive in its index; canonically the
`primitive` initialisations in tex.web). One half of the `texInternal`
boundary; the `@`-name convention is the other. -/
def texPrimitives : Array String := #[
  "above", "abovedisplayshortskip", "abovedisplayskip", "abovewithdelims",
  "accent", "adjdemerits", "advance", "afterassignment", "aftergroup",
  "atop", "atopwithdelims", "badness", "baselineskip", "batchmode",
  "begingroup", "belowdisplayshortskip", "belowdisplayskip", "binoppenalty",
  "botmark", "box", "boxmaxdepth", "brokenpenalty", "catcode", "char",
  "chardef", "cleaders", "closein", "closeout", "clubpenalty", "copy",
  "count", "countdef", "cr", "crcr", "csname", "day", "deadcycles", "def",
  "defaulthyphenchar", "defaultskewchar", "delcode", "delimiter",
  "delimiterfactor", "delimitershortfall", "dimen", "dimendef",
  "discretionary", "displayindent", "displaylimits", "displaystyle",
  "displaywidowpenalty", "displaywidth", "divide", "doublehyphendemerits",
  "dp", "dump", "edef", "else", "emergencystretch", "end", "endcsname",
  "endgroup", "endinput", "endlinechar", "eqno", "errhelp", "errmessage",
  "errorcontextlines", "errorstopmode", "escapechar", "everycr",
  "everydisplay", "everyhbox", "everyjob", "everymath", "everypar",
  "everyvbox", "exhyphenpenalty", "expandafter", "fam", "fi",
  "finalhyphendemerits", "firstmark", "floatingpenalty", "font",
  "fontdimen", "fontname", "futurelet", "gdef", "global", "globaldefs",
  "halign", "hangafter", "hangindent", "hbadness", "hbox", "hfil", "hfill",
  "hfilneg", "hfuzz", "hoffset", "holdinginserts", "hrule", "hsize",
  "hskip", "hss", "ht", "hyphenation", "hyphenchar", "hyphenpenalty", "if",
  "ifcase", "ifcat", "ifdim", "ifeof", "iffalse", "ifhbox", "ifhmode",
  "ifinner", "ifmmode", "ifnum", "ifodd", "iftrue", "ifvbox", "ifvmode",
  "ifvoid", "ifx", "ignorespaces", "immediate", "indent", "input",
  "inputlineno", "insert", "insertpenalties", "interlinepenalty",
  "jobname", "kern", "language", "lastbox", "lastkern", "lastpenalty",
  "lastskip", "lccode", "leaders", "left", "lefthyphenmin", "leftskip",
  "leqno", "let", "limits", "linepenalty", "lineskip", "lineskiplimit",
  "long", "looseness", "lower", "lowercase", "mag", "mark", "mathaccent",
  "mathbin", "mathchar", "mathchardef", "mathchoice", "mathclose",
  "mathcode", "mathinner", "mathop", "mathopen", "mathord", "mathpunct",
  "mathrel", "mathsurround", "maxdeadcycles", "maxdepth", "meaning",
  "medmuskip", "message", "mkern", "month", "moveleft", "moveright",
  "mskip", "multiply", "muskip", "muskipdef", "newlinechar", "noalign",
  "noboundary", "noexpand", "noindent", "nolimits", "nonscript",
  "nonstopmode", "nulldelimiterspace", "nullfont", "number", "omit",
  "openin", "openout", "or", "outer", "output", "outputpenalty", "over",
  "overfullrule", "overline", "overwithdelims", "pagedepth",
  "pagefilllstretch", "pagefillstretch", "pagefilstretch", "pagegoal",
  "pageshrink", "pagestretch", "pagetotal", "par", "parfillskip",
  "parindent", "parshape", "parskip", "patterns", "pausing", "penalty",
  "postdisplaypenalty", "predisplaypenalty", "predisplaysize",
  "pretolerance", "prevdepth", "prevgraf", "radical", "raise", "read",
  "relax", "relpenalty", "right", "righthyphenmin", "rightskip",
  "romannumeral", "scriptfont", "scriptscriptfont", "scriptscriptstyle",
  "scriptspace", "scriptstyle", "scrollmode", "setbox", "setlanguage",
  "sfcode", "shipout", "show", "showbox", "showboxbreadth", "showboxdepth",
  "showlists", "showthe", "skewchar", "skip", "skipdef", "spacefactor",
  "spaceskip", "span", "special", "splitbotmark", "splitfirstmark",
  "splitmaxdepth", "splittopskip", "string", "tabskip", "textfont",
  "textstyle", "the", "thickmuskip", "thinmuskip", "time", "toks",
  "toksdef", "tolerance", "topmark", "topskip", "tracingcommands",
  "tracinglostchars", "tracingmacros", "tracingonline", "tracingoutput",
  "tracingpages", "tracingparagraphs", "tracingrestores", "tracingstats",
  "uccode", "uchyph", "underline", "unhbox", "unhcopy", "unkern",
  "unpenalty", "unskip", "unvbox", "unvcopy", "uppercase", "vadjust",
  "valign", "vbadness", "vbox", "vcenter", "vfil", "vfill", "vfilneg",
  "vfuzz", "voffset", "vrule", "vsize", "vskip", "vsplit", "vss", "vtop",
  "wd", "widowpenalty", "wlog", "xdef", "xleaders", "xspaceskip", "year"]

/-- Is this control word a TeX internal — the boundary for the spliced-`.sty`
demotion? The union of the `@`-names (LaTeX's internal-name convention:
`\makeatletter` scopes them, ltdefns.dtx; `Lex.nameChar` already admits `@`)
and the TeX82 primitives. A package or venue macro (`\NewEnviron`) is
neither: the author might know it, so its refusal stays a per-line
warning. -/
def texInternal (name : String) : Bool :=
  name.contains '@' || texPrimitives.contains name

/-- A refusal of `name` at a site in `file` demotes exactly when the site is
inside a spliced `.sty` — the only door a `.sty` span enters by is the
splice (`\input` reads `.tex`) — and the name is a TeX internal. The author
can act on a per-line warning in their own files; in a venue's style file
they cannot, and N0020 already names that file once. -/
def styInternal (file name : String) : Bool :=
  file.endsWith ".sty" && texInternal name

private def say (code : DiagCode) (msg : String) (pos : Pos) (help : Option String := none)
    (demote : Bool := false) : M Unit :=
  modify fun st => { st with
    diags := st.diags.push (
      let d := Diag.of code msg (some ⟨st.file, pos⟩) help
      if demote then d.demote else d) }

/-- Keys are namespaced (`ctrl:`, `spec:`, `beamer:`), never bare names: the
catch-all `beamer:` key set grows with `beamerConfig`, and a flat space would
let a future entry claim a literal arm's key and silence it. -/
private def sayOnce (key : String) (code : DiagCode) (msg : String) (pos : Pos)
    (help : Option String := none) (demote : Bool := false) : M Unit := do
  unless (← get).warned.contains key do
    modify fun st => { st with warned := st.warned.push key }
    say code msg pos help demote

/-- Every translation is one note in the same shape, so `-v` reads as a list
of things the document could say directly. -/
private def became (what native : String) (pos : Pos) : M Unit :=
  say .N0100 s!"'{what}' → {native}" pos

private def synth (s : String) : M (Array Raw) := do
  let file := (← get).file
  return (Parse.parse file (Lex.lex file s).1).1

mutual

/-- Point every position in a synthesised tree at the command it came from, so
a diagnostic inside translated content names the LaTeX that produced it. -/
private def rebase (p : Pos) : Raw → Raw
  | .word s _ => .word s p
  | .space => .space
  | .par _ => .par p
  | .ctrl n _ => .ctrl n p
  | .sym c _ => .sym c p
  | .group body _ => .group (rebaseList p body.toList).toArray p
  | .math d body _ => .math d (rebaseList p body.toList).toArray p
  | .env n body _ => .env n (rebaseList p body.toList).toArray p
  | .verb s _ => .verb s p

private def rebaseList (p : Pos) : List Raw → List Raw
  | [] => []
  | r :: rest => rebase p r :: rebaseList p rest

end

private def synthAt (s : String) (pos : Pos) : M (Array Raw) := do
  return (← synth s).map (rebase pos)

/-- One optional `[...]` argument, as source text. -/
private def takeOpt (raws : Array Raw) (i : Nat) : Option String × Nat := Id.run do
  let j := skipSpaces raws i
  match raws[j]? with
  | some (.sym '[' _) =>
    let mut k := j + 1
    let mut inner : Array Raw := #[]
    for _ in [k:raws.size + 1] do
      match raws[k]? with
      | some (.sym ']' _) => return (some (rawSrc inner), k + 1)
      | some r => inner := inner.push r; k := k + 1
      | none => break
    return (none, i)
  | _ => (none, i)

/-- Up to `n` brace groups. A bare control word or single word counts as a
group too, as in TeX: `\newcommand\x` and `\textbf x` are legal. -/
private def takeGroups (raws : Array Raw) (i n : Nat) : Array (Array Raw) × Nat := Id.run do
  let mut out : Array (Array Raw) := #[]
  let mut j := i
  for _ in [0:n] do
    let k := skipSpaces raws j
    match raws[k]? with
    | some (.group body _) => out := out.push body; j := k + 1
    | some (r@(.ctrl _ _)) => out := out.push #[r]; j := k + 1
    | _ => break
  return (out, j)

/-- The `*` of a starred LaTeX form, standing between the command and its
arguments. In LaTeX the star on the definers (`\newcommand*` and siblings)
makes the arguments "short" — `\par` is forbidden in them (LaTeX2e
usrguide §"Defining commands"; `\def` vs `\long\def`) — and on `\vspace*`
it makes the space survive a column or page break rather than being
discarded there (LaTeX2e classes.dtx `\@vspace*`). The engine models
neither distinction, so the star is ignorable — consumed, never content:
left in the stream it lands where content may not stand and turns the
construct's warning into E0313, a fifteen-diagnostic cascade from one
character. -/
private def skipStar (raws : Array Raw) (i : Nat) : Nat :=
  match raws[i]? with
  | some (.word "*" _) => i + 1
  | _ => i

/-- The kernel's point-size macros at the values size10.clo–size12.clo and
ltplain give them, in milli-points: `\@xpt` is 10 pt, `\@xipt` 10.95 —
what `\@setfontsize` is called with. -/
private def ptMacros : List (String × Nat) :=
  [("@vpt", 5000), ("@vipt", 6000), ("@viipt", 7000), ("@viiipt", 8000),
   ("@ixpt", 9000), ("@xpt", 10000), ("@xipt", 10950), ("@xiipt", 12000),
   ("@xivpt", 14400), ("@xviipt", 17280), ("@xxpt", 20740), ("@xxvpt", 24880)]

/-- One `\@setfontsize` argument in milli-points: a kernel size macro, or
a literal number (`{14}`, `{10.95}`). -/
private def ptMacroArg (r : Array Raw) : Option Nat :=
  match r.toList with
  | [.ctrl n _] => ptMacros.lookup n
  | _ =>
    (Decl.parseDecimal (rawSrc r).trimAscii.toString).bind fun (m, s) =>
      if m ≥ 0 && s > 0 then some (m.toNat * 1000 / s) else none

/-- A milli value as its shortest decimal spelling: 10000 is "10",
10950 "10.95", 913 "0.913". -/
private def milliStr (m : Nat) : String :=
  let i := m / 1000
  let f := m % 1000
  if f == 0 then toString i else
  let digits := ((toString (1000 + f)).drop 1).toString
  let digits := if digits.endsWith "00" then (digits.dropEnd 2).toString
    else if digits.endsWith "0" then (digits.dropEnd 1).toString
    else digits
  s!"{i}.{digits}"

/-! # Decidable TeX conditionals

`\ifdefined\name` asks whether `\name` is defined, and the document's own
definitions make that decidable here: a name nothing in the document has
bound is undefined — which is the honest answer for another engine's
primitives too (`\directlua`, `\pdfoutput`: this engine is not that
engine). The pass below resolves each such conditional to its taken
branch, with a note naming the decision, before the idiom rewrite runs.
TeX's `\if` family is open-ended and the rest of it (`\ifx`, `\ifcsname`,
`\ifnum`, …) compares things the parse tree does not carry, so any other
`\if…` head inside an extent makes it undecidable and the whole construct
falls back to the skip-whole warning. -/

/-- Definers that bind the control word standing after them, directly or
as `{\name}`. Recording is flat — TeX's group-local scoping is not
modelled — which only ever errs toward "defined", the reading that keeps
a guarded branch. -/
private def definesNext : List String :=
  ["def", "edef", "gdef", "xdef", "let", "newcommand", "renewcommand",
   "providecommand", "DeclareRobustCommand", "DeclareMathOperator",
   "define", "defineenv"]

private def recordDefined (n : String) : M Unit :=
  modify fun st =>
    if st.defined.contains n then st else { st with defined := st.defined.push n }

/-- The control word a definer binds, read from the element after it. -/
private def boundName : Raw → Option String
  | .ctrl n _ => some n
  | .group body _ =>
    match body.toList with
    | .ctrl n _ :: _ => some n
    | _ => none
  | _ => none

/-- A definer's starred form separates it from the name it binds. -/
private def isSpaceOrStar : Raw → Bool
  | .space => true
  | .word "*" _ => true
  | _ => false

/-- What a resolution says: which way it went, and what that keeps. -/
private def condMsg (n : String) (defined : Bool) : String :=
  if defined then
    s!"'\\ifdefined\\{n}': '\\{n}' is defined, so the branch before '\\else' is kept"
  else
    s!"'\\ifdefined\\{n}': '\\{n}' is not defined, so only the '\\else' branch is kept"

/-- The same, for a `\newif` flag's conditional. -/
private def flagMsg (n : String) (value : Bool) : String :=
  if value then
    s!"'\\{n}' is true here, so the branch before '\\else' is kept"
  else
    s!"'\\{n}' is false here, so only the '\\else' branch is kept"

/-- The base name of a `\newif` flag this control word tests (`\ifX`),
when the pass has recorded it. -/
private def flagTested (flags : Array (String × Bool)) (n : String) :
    Option (String × Bool) :=
  if n.startsWith "if" && n.length > 2 then
    flags.find? (·.1 == (n.drop 2).toString)
  else none

/-- Is the conditional heading `raws[i]` one the pass can resolve? True
when a matching `\fi` closes it at this level and every conditional inside
the extent is itself `\ifdefined` naming a control word, or an `\ifX` of a
recorded `\newif` flag. Any other `\if…` head is undecidable and would
also desynchronise the `\else`/`\fi` matching, so it invalidates the whole
extent. -/
private def condExtent (flags : Array (String × Bool)) (raws : Array Raw)
    (i : Nat) : Bool := Id.run do
  let mut depth := 0
  let mut j := i
  for _ in [i:raws.size] do
    match raws[j]? with
    | some (.ctrl "ifdefined" _) =>
      let k := skipSpaces raws (j + 1)
      match raws[k]? with
      | some (.ctrl _ _) =>
        depth := depth + 1
        j := k + 1
      | _ => return false
    | some (.ctrl "fi" _) =>
      if depth == 1 then return true
      depth := depth - 1
      j := j + 1
    | some (.ctrl n _) =>
      if (flagTested flags n).isSome then
        depth := depth + 1
        j := j + 1
      else if n == "if" || (n.startsWith "if" && n.length > 2) then return false
      else j := j + 1
    | some _ => j := j + 1
    | none => return false
  return false

mutual

/-- Resolve the decidable conditionals at one level. `stack` is the truth
of every open `\ifdefined`, innermost first — an element is emitted only
when all of them hold, `\else` flips the innermost, `\fi` closes it — and
a bare `\else`/`\fi` with nothing open is not ours and passes through.
The list drives the recursion; `raws` and `i` give the extent check its
lookahead, exactly as `rewriteList` pairs them. -/
private def condList (raws : Array Raw) (out : Array Raw) (stack : List Bool) :
    List Raw → Nat → M (Array Raw)
  | [], _ => pure out
  | .ctrl "ifdefined" pos :: .ctrl n np :: rest, i => do
    if stack.isEmpty && !condExtent (← get).flags raws i then
      -- Undecidable: leave the construct for the skip-whole warning.
      condList raws ((out.push (.ctrl "ifdefined" pos)).push (.ctrl n np)) stack rest (i + 2)
    else
      let defined := (← get).defined.contains n
      if stack.all id then
        say .N0114 (condMsg n defined) pos
      condList raws out (defined :: stack) rest (i + 2)
  | .ctrl "ifdefined" pos :: .space :: .ctrl n np :: rest, i => do
    if stack.isEmpty && !condExtent (← get).flags raws i then
      condList raws (((out.push (.ctrl "ifdefined" pos)).push .space).push (.ctrl n np))
        stack rest (i + 3)
    else
      let defined := (← get).defined.contains n
      if stack.all id then
        say .N0114 (condMsg n defined) pos
      condList raws out (defined :: stack) rest (i + 3)
  | .ctrl "ifdefined" pos :: rest, i =>
    -- Nothing testable follows; pass the head through untouched.
    condList raws (out.push (.ctrl "ifdefined" pos)) stack rest (i + 1)
  | .ctrl "newif" pos :: .ctrl n np :: rest, i => do
    -- `\newif\ifX` declares a decidable flag, initially false (plain TeX:
    -- `\newif` ends with `\csname …false\endcsname`): `\ifX` joins this
    -- pass, `\Xtrue`/`\Xfalse` set it. A `\newif` whose next token is not
    -- an `\if…` name passes through for the ordinary unknown warning.
    if !(stack.all id) then
      condList raws out stack rest (i + 2)
    else if n.startsWith "if" && n.length > 2 then
      let x := (n.drop 2).toString
      modify fun st => { st with
        flags := (st.flags.filter (·.1 != x)).push (x, false) }
      recordDefined n
      recordDefined (x ++ "true")
      recordDefined (x ++ "false")
      say .N0114 s!"'\\newif\\{n}': '\\{n}' is resolved from here on, initially false" pos
      condList raws out stack rest (i + 2)
    else
      condList raws ((out.push (.ctrl "newif" pos)).push (.ctrl n np)) stack rest (i + 2)
  | .ctrl "newif" pos :: .space :: .ctrl n np :: rest, i => do
    if !(stack.all id) then
      condList raws out stack rest (i + 3)
    else if n.startsWith "if" && n.length > 2 then
      let x := (n.drop 2).toString
      modify fun st => { st with
        flags := (st.flags.filter (·.1 != x)).push (x, false) }
      recordDefined n
      recordDefined (x ++ "true")
      recordDefined (x ++ "false")
      say .N0114 s!"'\\newif\\{n}': '\\{n}' is resolved from here on, initially false" pos
      condList raws out stack rest (i + 3)
    else
      condList raws (((out.push (.ctrl "newif" pos)).push .space).push (.ctrl n np))
        stack rest (i + 3)
  | .ctrl "else" pos :: rest, i => do
    match stack with
    | [] => condList raws (out.push (.ctrl "else" pos)) [] rest (i + 1)
    | top :: more => condList raws out ((!top) :: more) rest (i + 1)
  | .ctrl "fi" pos :: rest, i => do
    match stack with
    | [] => condList raws (out.push (.ctrl "fi" pos)) [] rest (i + 1)
    | _ :: more => condList raws out more rest (i + 1)
  | .ctrl n pos :: rest, i => do
    let flags := (← get).flags
    match flagTested flags n with
    | some (_, value) =>
      -- `\ifX` of a recorded flag: resolve exactly as `\ifdefined` does,
      -- extent check included.
      if stack.isEmpty && !condExtent flags raws i then
        condList raws (out.push (.ctrl n pos)) stack rest (i + 1)
      else
        if stack.all id then
          say .N0114 (flagMsg n value) pos
        condList raws out (value :: stack) rest (i + 1)
    | none =>
      if !(stack.all id) then
        condList raws out stack rest (i + 1)
      else if n.endsWith "true" && flags.any (·.1 == (n.dropEnd 4).toString) then
        let x := (n.dropEnd 4).toString
        modify fun st => { st with
          flags := (st.flags.filter (·.1 != x)).push (x, true) }
        say .N0114 s!"'\\{n}': '\\if{x}' is true from here on" pos
        condList raws out stack rest (i + 1)
      else if n.endsWith "false" && flags.any (·.1 == (n.dropEnd 5).toString) then
        let x := (n.dropEnd 5).toString
        modify fun st => { st with
          flags := (st.flags.filter (·.1 != x)).push (x, false) }
        say .N0114 s!"'\\{n}': '\\if{x}' is false from here on" pos
        condList raws out stack rest (i + 1)
      else
        if definesNext.contains n then
          if let some m := (rest.dropWhile isSpaceOrStar).head?.bind boundName then
            recordDefined m
        condList raws (out.push (.ctrl n pos)) stack rest (i + 1)
  | r :: rest, i => do
    if stack.all id then
      condList raws (out.push (← condOne r)) stack rest (i + 1)
    else
      condList raws out stack rest (i + 1)

/-- Descend into a group or environment body; an `\input` wrapper switches
the file its notes name, as `rewriteRaw` does. -/
private def condOne : Raw → M Raw
  | .group body p => do
    return .group (← condList body #[] [] body.toList 0) p
  | .math d body p => do
    return .math d (← condList body #[] [] body.toList 0) p
  | .env n body p => do
    match Parse.inputEnvFile? n with
    | some f =>
      let saved := (← get).file
      modify fun st => { st with file := f }
      let body' ← condList body #[] [] body.toList 0
      modify fun st => { st with file := saved }
      return .env n body' p
    | none =>
      return .env n (← condList body #[] [] body.toList 0) p
  | r => pure r

end

mutual

/-- `\\AtBeginDocument{...}` defers its body to `\\begin{document}`
(ltfiles.dtx: the begindocument hook). This engine's preamble is
declarations, and a declaration is document-scoped wherever it stands, so
the body is read where it is written — the same bindings, no hook
machinery — and whatever in it the engine refuses is named where it
stands, exactly as if written unwrapped. -/
private def unwrapBeginHookList (out : Array Raw) : List Raw → M (Array Raw)
  | [] => pure out
  | .ctrl "AtBeginDocument" pos :: .group body _ :: rest => do
    became "\\AtBeginDocument{...}" "its body, read where it stands" pos
    let out ← unwrapBeginHookList out body.toList
    unwrapBeginHookList out rest
  | .ctrl "AtBeginDocument" pos :: .space :: .group body _ :: rest => do
    became "\\AtBeginDocument{...}" "its body, read where it stands" pos
    let out ← unwrapBeginHookList out body.toList
    unwrapBeginHookList out rest
  | r :: rest => do
    unwrapBeginHookList (out.push (← unwrapBeginHookOne r)) rest

/-- Descend into a group or environment body; an `\\input` wrapper switches
the file its note names, as `condOne` and `rewriteRaw` do. -/
private def unwrapBeginHookOne : Raw → M Raw
  | .group body p => do
    return .group (← unwrapBeginHookList #[] body.toList) p
  | .env n body p => do
    match Parse.inputEnvFile? n with
    | some f =>
      let saved := (← get).file
      modify fun st => { st with file := f }
      let body' ← unwrapBeginHookList #[] body.toList
      modify fun st => { st with file := saved }
      return .env n body' p
    | none =>
      return .env n (← unwrapBeginHookList #[] body.toList) p
  | r => pure r

end

/-- A TeX length in the native spelling: `0.5\rhythm` is `0.5 * rhythm`,
`\relax` vanishes. -/
private def lengthSrc (raws : Array Raw) : String := Id.run do
  let mut s := ""
  let mut prevNumber := false
  for r in raws do
    match r with
    | .ctrl "relax" _ => pure ()
    | .ctrl "p@" _ =>
      -- TeX's \p@ is 1pt and \z@ 0pt (plain.tex); a `.sty` spells its
      -- lengths in them, and its rubber in \@plus/\@minus (ltdefns.dtx:
      -- the sanitised glue keywords "plus" and "minus").
      s := s ++ (if prevNumber then "pt" else "1pt")
      prevNumber := false
    | .ctrl "z@" _ =>
      s := s ++ (if prevNumber then "pt" else "0pt")
      prevNumber := false
    | .ctrl "@plus" _ =>
      s := s ++ " plus "
      prevNumber := false
    | .ctrl "@minus" _ =>
      s := s ++ " minus "
      prevNumber := false
    | .ctrl n _ =>
      s := s ++ (if prevNumber then " * " else "") ++ n
      prevNumber := false
    | .word w _ =>
      s := s ++ w
      prevNumber := w.toList.all fun c => c.isDigit || c == '.'
    | .space => s := s ++ " "
    | other => s := s ++ rawSrcOne other
  return s.trimAscii.toString

/-- A TeX length from option text: `3\\sepunit` is `3 * sepunit`, `\\x` is `x`. -/
private def lengthOfTeX (v : String) : String :=
  let t := v.trimAscii.toString
  match t.splitOn "\\" with
  | [plain] => plain.trimAscii.toString
  | num :: name :: _ =>
    let n := num.trimAscii.toString
    let name := name.trimAscii.toString
    if n.isEmpty then name else s!"{n} * {name}"
  | [] => t

/-- The control word inside a group, ignoring whitespace around it. -/
private def ctrlName (raws : Array Raw) : Option String :=
  match raws.toList.filter (fun r => match r with | .space => false | _ => true) with
  | [.ctrl n _] => some n
  | _ => none

/-- An xparse argument spec, or a plain count, as native parameters
`a1 … an`. Only the argument *types* matter here: `m` is mandatory, and `o`,
`O{..}`, `d..`, `D..{..}`, `s`, `t.` are all optional. Every parameter is
`content` — a LaTeX macro argument may carry markup (`\light{\texttt{x}}`),
and typing it `text` would reject exactly the calls LaTeX accepts. Payloads
such as defaults and delimiters ride inside braces that the parser has
already grouped, so a spec is read from its own source text and braces are
skipped. -/
private def signature (spec : String) : String := Id.run do
  let mut letters : Array Char := #[]
  let mut depth := 0
  for c in spec.toList do
    if c == '{' then depth := depth + 1
    else if c == '}' then depth := depth - 1
    else if depth == 0 then
      if c == 'm' || c == 'r' || c == 'R' || c == 'v' || c == 'b' then letters := letters.push 'm'
      else if c == 'o' || c == 'O' || c == 'd' || c == 'D' || c == 's' || c == 't' then
        letters := letters.push 'o'
  let params := letters.toList.zipIdx.map fun (c, k) =>
    s!"a{k + 1}{if c == 'o' then "?" else ""}: content"
  String.intercalate ", " params

/-- `\usepackage[opts]{geometry}`, `\geometry{...}`, `\newgeometry{...}`
→ `\page{...}`. `textwidth`/`textheight` pass through to the `\page` keys
of the same names (geometry manual §5.2: they size the body; the engine
centres it — geometry's own oneside `hmarginratio` 1:1). `headsep` and
`footskip` pass through too, carrying their LaTeX baseline semantics to
the one correction site (`Layout.furnGapOfSep`); `headheight` is satisfied
by construction — the head's band reserves its line's whole ink
(`Layout.bodyTop_clears_head`), which is what a declared `headheight`
exists to guarantee. The one-sided margins `top`/`bottom` and
`left`/`right` map when the pair agrees (the engine's page model has one
margin per axis) and are dropped named when it does not. -/
private def geometry (opts : String) (pos : Pos)
    (spelling : String := "\\usepackage{geometry}") : M (Array Raw) := do
  let mut keys : Array String := #[]
  let mut dropped : Array String := #[]
  let mut sides : Array (String × String) := #[]
  for e in Decl.splitEntries opts do
    match e.splitOn "=" with
    | [flag] =>
      let f := flag.trimAscii.toString
      if f.endsWith "paper" then
        keys := keys.push s!"size = {(f.dropEnd "paper".length).toString}"
      else if f == "noheadfoot" || f == "nohead" || f == "nofoot" then
        -- Asks for no running furniture, the state the engine starts from.
        pure ()
      else dropped := dropped.push f
    | k :: v =>
      let k := k.trimAscii.toString
      let v := (String.intercalate "=" v).trimAscii.toString
      -- geometry's width/height size the text block, paperwidth/paperheight
      -- the page (geometry manual §5.2); \page speaks in page dimensions.
      let k := if k == "paperwidth" then "width" else if k == "paperheight" then "height" else k
      -- A `\dimexpr` is TeX arithmetic `lengthOfTeX` cannot carry: mapping
      -- it would synthesize an unreadable `\page` value and turn a named
      -- drop into an error. It stays a drop, named.
      if v.startsWith "\\dimexpr" then
        dropped := dropped.push k
      else if ["margin", "vmargin", "hmargin", "width", "height",
          "textwidth", "textheight", "headsep", "footskip"].contains k then
        keys := keys.push s!"{k} = {lengthOfTeX v}"
      else if k == "headheight" then
        pure ()
      else if ["top", "bottom", "left", "right"].contains k then
        sides := sides.push (k, lengthOfTeX v)
      else dropped := dropped.push k
    | [] => pure ()
  -- geometry's per-side margins, folded pairwise: an equal pair is the
  -- symmetric margin the engine centres with (geometry manual §5.2's
  -- oneside hmarginratio 1:1 is the same statement), an unequal or lone
  -- side has no native equivalent and stays named.
  let side (n : String) : Option String :=
    (sides.findRev? (·.1 == n)).map (·.2)
  for (a, b, key) in [("top", "bottom", "vmargin"), ("left", "right", "hmargin")] do
    match side a, side b with
    | some va, some vb =>
      if va == vb then keys := keys.push s!"{key} = {va}"
      else dropped := dropped ++ #[a, b]
    | some _, none => dropped := dropped.push a
    | none, some _ => dropped := dropped.push b
    | none, none => pure ()
  let native := s!"\\page\{ {String.intercalate ", " keys.toList} }"
  became spelling native pos
  unless dropped.isEmpty do
    say .W0101 s!"geometry keys without a native equivalent were dropped: \
{String.intercalate ", " dropped.toList}" pos
  synthAt native pos

/-- The beamerposter size table, read off beamerposter.sty v1.13's own
size branch: name → board (w × h in mm, landscape as the sty spells it)
and the fontscale normalization in hundred-millionths — (1/√2)ⁿ against
a0, the sty's own comments beside each value. -/
private def beamerposterSizes : List (String × (Nat × Nat) × Nat) :=
  [("a0b", (1190, 880), 100000000),
   ("a0", (1189, 841), 100000000),
   ("a1", (841, 594), 70710678),
   ("a2", (594, 420), 50000000),
   ("a3", (420, 297), 35355339),
   ("a4", (297, 210), 25000000)]

/-- Format sp-free fixed-point `v/10000` pt as a decimal `pt` value. -/
private def ptTenThousandths (v : Int) : String :=
  let whole := v / 10000
  let frac := (v % 10000).toNat
  if frac == 0 then s!"{whole}pt"
  else
    let digits := String.ofList (Nat.toDigits 10 frac)
    let padded := String.ofList (List.replicate (4 - digits.length) '0') ++ digits
    let fs := String.ofList (padded.toList.reverse.dropWhile (· == '0')).reverse
    s!"{whole}.{fs}pt"

/-- `\usepackage[size=…,orientation=…,scale=…]{beamerposter}` →
`\documentclass{poster}` + `\page{ width, height, fontsize }`. The board
comes from the sty's own size table (`beamerposterSizes`); the sty's
default is `size=a0`, landscape, `scale=1.0` (`\ExecuteOptionsX`), and
`orientation=portrait` swaps the axes. `size=custom` reads `width=` and
`height=` as cm, fontscale 1, exactly the sty's custom branch. The body
size is the sty's own calibration — 24.88 pt at scale 1 — times
`scale=` times the named size's fontscale normalization, the product
rounded to two decimals as the sty's `\FPupn{...}{... 2 round}` rounds
it. The synthesized `\documentclass` stands after the beamer→slides
rewrite in stream order and the last `\documentclass` wins in
`applyDecl` (posterCompatChecks pins it), so the poster class displaces
the slides one. An option outside the model (`debug`, printer sizing) is
dropped by name (W0367). -/
private def beamerposter (opts : String) (pos : Pos) : M (Array Raw) := do
  let mut size := "a0"
  let mut portrait := false
  let mut scaleNum : Int := 1
  let mut scaleDen : Nat := 1
  let mut customW : Option String := none
  let mut customH : Option String := none
  let mut dropped : Array String := #[]
  for e in Decl.splitEntries opts do
    match (e.splitOn "=").map (·.trimAscii.toString) with
    | ["size", v] => size := v
    | ["orientation", v] => portrait := v == "portrait"
    -- a bare `orientation` takes the sty's declared default value
    -- (`\DeclareOptionX{orientation}[portrait]`).
    | ["orientation"] => portrait := true
    | ["scale", v] =>
      match Decl.parseDecimal v with
      | some (m, s) => scaleNum := m; scaleDen := s
      | none => dropped := dropped.push (e.trimAscii.toString)
    | ["scale"] => pure ()
    | ["width", v] => customW := some v
    | ["height", v] => customH := some v
    | [""] => pure ()
    | _ => dropped := dropped.push (e.trimAscii.toString)
  let mut keys : Array String := #[]
  let mut fontscale : Nat := 100000000
  if size == "custom" then
    match customW, customH with
    | some w, some h =>
      let (w, h) := if portrait then (h, w) else (w, h)
      keys := keys.push s!"width = {w}cm"
      keys := keys.push s!"height = {h}cm"
    | _, _ =>
      dropped := dropped.push "size=custom (needs width= and height=)"
  else
    match beamerposterSizes.lookup size with
    | some ((w, h), fs) =>
      fontscale := fs
      let (w, h) := if portrait then (h, w) else (w, h)
      keys := keys.push s!"width = {w}mm"
      keys := keys.push s!"height = {h}mm"
    | none => dropped := dropped.push s!"size={size}"
  -- myfontscale = scale × fontscale, rounded to two decimals (the sty's
  -- own FPupn rounding); normalsize = 24.88 pt × myfontscale.
  let den : Int := (scaleDen : Int) * 100000000
  let cents := (scaleNum * (fontscale : Int) * 100 + den / 2) / den
  keys := keys.push s!"fontsize = {ptTenThousandths (2488 * cents)}"
  let native := s!"\\documentclass\{poster}\\page\{ {String.intercalate ", " keys.toList} }"
  became "\\usepackage{beamerposter}" native pos
  unless dropped.isEmpty do
    say .W0367 s!"beamerposter options outside the poster model: \
{String.intercalate ", " dropped.toList}; ignored" pos
      (help := "size, orientation, scale, and custom width/height carry over; \
\\page{ ... } declares anything further")
  synthAt native pos

/-- `\hypersetup{pdfauthor=..., pdftitle=...}` → `\pdfmeta{...}`; rendering
hints (`colorlinks`, `pdfborder`) have no meaning and go quietly. -/
private def hypersetup (opts : String) (pos : Pos) : M (Array Raw) := do
  let mut keys : Array String := #[]
  for e in Decl.splitEntries opts do
    match e.splitOn "=" with
    | k :: v =>
      let k := k.trimAscii.toString
      let v := (String.intercalate "=" v).trimAscii.toString
      let v := if v.startsWith "{" && v.endsWith "}" then
        (v.drop 1).dropEnd 1 |>.toString else v
      for m in ["title", "author", "subject", "keywords"] do
        if k == "pdf" ++ m then keys := keys.push s!"{m} = \"{v}\""
    | [] => pure ()
  let native := s!"\\pdfmeta\{ {String.intercalate ", " keys.toList} }"
  became "\\hypersetup" native pos
  synthAt native pos

private def color (model value : String) (pos : Pos) : M (Option String) := do
  match model with
  | "HTML" => return some s!"#{value}"
  | "cmyk" =>
    -- The print model, kept as declared: PDF paints it in DeviceCMYK.
    return some s!"cmyk({value})"
  | "rgb" | "RGB" =>
    let parts := (value.splitOn ",").filterMap fun p =>
      Decl.parseDecimal p.trimAscii.toString
    match parts with
    | [(r, rs), (g, gs), (b, bs)] =>
      let mult := if model == "rgb" then 255 else 1
      let ch (m : Int) (s : Nat) : Nat := min 255 (m * mult / s).toNat
      let hex (n : Nat) : String := Ir.Color.hexByte (UInt8.ofNat n)
      return some s!"#{hex (ch r rs)}{hex (ch g gs)}{hex (ch b bs)}"
    | _ => return none
  | _ =>
    say .W0102 s!"colour model '{model}' is not supported; use HTML, rgb, or cmyk" pos
    return none

/-- KOMA's `\\sectionlinesformat` is a hook for drawing after a heading. The one
idiom worth reading is a rule in a colour, `\\textcolor{X}{\\leaders\\hrule …}`;
any other non-empty body is a dropped loss and says so — an empty body asks
for no decoration, which is what an unstyled section already draws. -/
private def sectionRule (src : String) (pos : Pos) : M (Array Raw) := do
  let dropped : M (Array Raw) := do
    unless src.trimAscii.toString.isEmpty do
      say .E0113
        "'\\sectionlinesformat' body is not the rule idiom; it is dropped" pos
        (help := "\\style{section}{ rule = <colour> } declares the section \
rule; \\allow{E0113} accepts the loss")
    return #[]
  match (src.splitOn "\\textcolor {")[1]? with
  | some rest =>
    let color := ((rest.splitOn "}").headD "").trimAscii.toString
    if (src.splitOn "hrule").length > 1 && !color.isEmpty then
      let native := s!"\\style\{section}\{ rule = {color} }"
      became "\\sectionlinesformat" native pos
      synthAt native pos
    else dropped
  | none => dropped

/-- LaTeX's documented sectioning idiom (ltsect.dtx; clsguide, "Defining
new sectioning commands"): a definer whose whole body is one
`\@startsection{name}{level}{indent}{beforeskip}{afterskip}{style}` call
is a declarative rule over an existing heading, not a definition — read
as the engine's `\style`, exactly as `\RedeclareSectionCommand`'s keys
are. A negative beforeskip means only "no indent after the heading"; the
skip used is the whole glue negated (ltsect.dtx: `\@tempskipa
-\@tempskipa`). A negative afterskip declares a run-in heading, which the
engine does not model — named and skipped, the built-in heading stands.
The style group keeps its declarations with TeX's two-letter plain forms
spelled out (plain.tex: `\bf` for `\bfseries`); alignment declarations
configure justification the heading model owns and are not font. -/
private def startSection? (cmd : String) (body : Array Raw) (pos : Pos) :
    M (Option (Array Raw)) := do
  let some i := body.findIdx? (fun r => match r with | .space => false | _ => true)
    | return none
  match body[i]? with
  | some (.ctrl "@startsection" _) =>
    let (args, _) := takeGroups body (i + 1) 6
    if h : args.size = 6 then
      let element := (rawSrc args[0]).trimAscii.toString
      let after := lengthSrc args[4]
      if after.startsWith "-" then
        sayOnce ("ctrl:runin:" ++ cmd) .W0104
          s!"'\\{cmd}' would be a run-in heading (negative \\@startsection \
afterskip), which is not modelled; the redefinition is skipped" pos
        return some #[]
      if element != cmd || !Ir.styleableElements.contains element then
        return none
      let before := lengthSrc args[3]
      let before := if before.startsWith "-" then before.replace "-" "" else before
      let aliases := [("bf", "bfseries"), ("it", "itshape"), ("sc", "scshape"),
        ("sl", "slshape"), ("rm", "rmfamily"), ("sf", "sffamily"), ("tt", "ttfamily")]
      let alignments := ["raggedright", "raggedleft", "centering"]
      let fonts := args[5].filterMap fun r => match r with
        | .ctrl n _ =>
          if alignments.contains n then none
          else some s!"\\{(aliases.lookup n).getD n}"
        | _ => none
      let font := if fonts.isEmpty then ""
        else s!", font = \{{String.join fonts.toList}}"
      let native := s!"\\style\{{element}}\{ before = {before}, after = {after}{font} }"
      became s!"\\{cmd} = \\@startsection\{{element}}" native pos
      return some (← synthAt native pos)
    else return none
  | _ => return none

/-- Rewrite the control sequence `name` given what follows it. Returns the
replacement and how many following elements it consumed, or `none` to leave
the command alone. -/
private def rewriteCtrl (name : String) (pos : Pos) (raws : Array Raw) (start : Nat) :
    M (Option (Array Raw × Nat)) := do
  let consumed ← rewriteCtrlAt name pos raws start
  return consumed.map fun (repl, k) => (repl, k - start)
where
  rewriteCtrlAt (name : String) (pos : Pos) (raws : Array Raw) (start : Nat) :
      M (Option (Array Raw × Nat)) := do
  match name with
  | "usepackage" | "RequirePackage" =>
    -- One dispatch for both spellings: `\RequirePackage` is `\usepackage`
    -- for package writers (ltclass.dtx), and a local `.sty` spliced into
    -- the preamble spells its loads that way.
    if (← get).inDoc then
      -- LaTeX's own rule: "\usepackage can be used only in preamble"
      -- (ltclass.dtx \@onlypreamble) — in the body the placement is the
      -- defect, whatever the package's support, so the W0103 dispatch
      -- below never judges it.
      let (_, j) := takeOpt raws start
      let (_, k) := takeGroups raws j 1
      sayOnce ("ctrl:" ++ name) .W0340
        s!"'\\{name}' is a preamble declaration; in the body it is ignored" pos
        (help := "load the package in the preamble, before '\\begin{document}'")
      return some (#[], k)
    let (opt, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    if args.isEmpty then return none
    let pkgs := (rawSrc (args.getD 0 #[])).splitOn "," |>.map (·.trimAscii.toString)
    let mut out : Array Raw := #[]
    for p in pkgs do
      if p == "geometry" then
        out := out ++ (← geometry (opt.getD "") pos)
      else if p == "beamerposter" then
        out := out ++ (← beamerposter (opt.getD "") pos)
      else if p == "parskip" then
        -- The package sets `\parskip` to half a line plus 2pt and drops the
        -- indent; the half line is what changes the page.
        let native := "\\page{ parskip = 0.6em plus 2pt }"
        became "\\usepackage{parskip}" native pos
        out := out ++ (← synthAt native pos)
      else if (p == "caption" || p == "subcaption") && opt.isSome then
        -- The package options are `\captionsetup` keys (caption manual
        -- §1.3): route them to the one site that judges caption keys, so
        -- `[tableposition=top]` is honoured or named exactly as the
        -- command form is.
        let native := s!"\\captionsetup\{{opt.getD ""}}"
        became s!"\\usepackage[{opt.getD ""}]\{{p}}" native pos
        out := out ++ (← synthAt native pos)
      else if p == "babel" then
        -- babel's package options are its language list, and "the last
        -- language option is the main one" (babel manual §1.2). The main
        -- language becomes document metadata (`\pdfmeta{ language }`);
        -- the locale record then words captions, selects hyphenation
        -- patterns, and shapes `\enquote`. Non-language options carry
        -- `=` and are configuration, skipped as before.
        let names := ((opt.getD "").splitOn ",").map (·.trimAscii.toString)
          |>.filter (fun o => !o.isEmpty && !o.contains '=')
        match names.reverse.head? with
        | some main =>
          let tag := Locale.babelTagOf main
          if (Locale.forTag tag).isSome then
            let native := s!"\\pdfmeta\{ language = \"{tag}\" }"
            became s!"\\usepackage[{main}]\{babel}" native pos
            modify fun st => { st with mainLang := tag }
            out := out ++ (← synthAt native pos)
          else
            say .W0368 s!"no locale for language '{main}'; English \
captions and patterns stand in" pos
              (help := "the engine ships locale records for: en, fr, de")
        | none =>
          became s!"\\{name}\{{p}}" "nothing: the engine does this itself" pos
      else if nativePackages.contains p then
        became s!"\\{name}\{{p}}" "nothing: the engine does this itself" pos
      else
        say .W0103 s!"package '{p}' is not supported; skipped" pos
    return some (out, k)
  | "documentclass" =>
    let (opt, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    let cls := rawSrc (args.getD 0 #[])
    if articleClasses.contains cls || resumeClasses.contains cls then
      let native0 := if resumeClasses.contains cls then "resume" else "article"
      let o := match opt with | some o => s!"[{o}]" | none => ""
      -- A LaTeX class separates paragraphs by indent, not by a skip: its
      -- `\parskip` is zero unless the KOMA `parskip=` option asks for half a
      -- line or a full one. The engine's own default is a skip, so the
      -- class declares what LaTeX would have.
      let komaSkip := (opt.getD "").splitOn "," |>.findSome? fun kv =>
        match (kv.splitOn "=").map (·.trimAscii.toString) with
        | ["parskip", v] =>
          if v.startsWith "full" then some "1.2em plus 0.24em"
          else if v.startsWith "half" then some "0.6em plus 0.12em"
          else if v == "false" || v == "never" then some "0pt"
          else some "0.6em plus 0.12em"
        | ["parskip"] => some "1.2em plus 0.24em"
        | _ => none
      let native := s!"\\documentclass{o}\{{native0}}\\page\{ parskip = {komaSkip.getD "0pt"} }"
      became s!"\\documentclass\{{cls}}" native pos
      return some (← synthAt native pos, k)
    else if cls == "beamer" then
      let o := match opt with | some o => s!"[{o}]" | none => ""
      became "\\documentclass{beamer}" s!"\\documentclass{o}\{slides}" pos
      return some (← synthAt s!"\\documentclass{o}\{slides}" pos, k)
    else return none
  | "babelfont" | "setmainfont" | "setsansfont" | "setmonofont" =>
    -- `\babelfont[lang]{slot}{font}` binds a font per language (babel
    -- manual §1.8). The option parses first — it stands before the slot —
    -- and the binding is then dropped by name (W0369): one Latin body
    -- face covers en/fr/de, and a per-language face buys nothing until a
    -- non-Latin document exists. The unoptioned form is the main font.
    let (langOpt, j0) := if name == "babelfont" then takeOpt raws start else (none, start)
    let (slotArgs, j) := if name == "babelfont" then takeGroups raws j0 1 else (#[], start)
    let (optBefore, j) := takeOpt raws j
    let (args, k) := takeGroups raws j 1
    -- fontspec takes its features before the name or after it.
    let (optAfter, k) := takeOpt raws k
    let slot := match name with
      | "babelfont" => match rawSrc (slotArgs.getD 0 #[]) with
        | "rm" => "body" | "sf" => "sans" | "tt" => "mono" | s => s
      | "setmainfont" => "body" | "setsansfont" => "sans" | _ => "mono"
    let family := rawSrc (args.getD 0 #[])
    -- fontspec features that matter here are the ones that name fonts rather
    -- than shape them: `Path=` says where the fonts live, and the per-variant
    -- faces (`BoldFont=` and siblings) say exactly which file or name serves
    -- each variant. Everything else is a shaping feature and is dropped.
    let feature (k : String) : Option String :=
      ([optBefore, optAfter].filterMap id).findSome? fun opts =>
        (Decl.splitEntries opts).findSome? fun kv =>
          match Decl.splitEntry kv with
          | some (key, v) =>
            if key == k then
              some (if v.startsWith "{" && v.endsWith "}" then
                ((v.drop 1).toString.dropEnd 1).toString.trimAscii.toString
              else v)
            else none
          | none => none
    let dirPart := match feature "Path" with
      | some d => s!"dir = \"{d}\", "
      | none => ""
    let mut parts := #[s!"{slot} = \"{family}\""]
    for (opt, variant) in [("UprightFont", "upright"), ("BoldFont", "bold"),
        ("ItalicFont", "italic"), ("BoldItalicFont", "bolditalic")] do
      if let some f := feature opt then
        -- fontspec's `*` stands for the family name (fontspec manual,
        -- "Choosing additional fonts": "may be replaced by *"):
        -- `UprightFont = *-Medium` under `{Inter}` names "Inter-Medium".
        let f := if f.startsWith "*" then family ++ (f.drop 1).toString else f
        parts := parts.push s!"{slot}.{variant} = \"{f}\""
    if name == "babelfont" then
      if let some l := langOpt then
        say .W0369 s!"'\\babelfont[{l}]' binds a font per language; one \
face serves every language, so the binding is dropped" pos
          (help := "\\fonts{ body = \"...\" } names the face every language uses")
        return some (#[], k)
    let native := s!"\\fonts\{ {dirPart}{String.intercalate ", " parts.toList} }"
    became s!"\\{name}" native pos
    return some (← synthAt native pos, k)
  | "definecolor" =>
    let (args, k) := takeGroups raws start 3
    if h : args.size = 3 then
      let n := rawSrc args[0]
      match ← color (rawSrc args[1]) (rawSrc args[2]) pos with
      | some hex =>
        let native := s!"\\palette\{ {n} = {hex} }"
        became s!"\\definecolor\{{n}}" native pos
        return some (← synthAt native pos, k)
      | none => return some (#[], k)
    else return none
  | "colorlet" =>
    let (args, k) := takeGroups raws start 2
    if h : args.size = 2 then
      -- xcolor's `.` names the current colour (xcolor manual §2.3, the
      -- colour expression grammar); in the preamble that is the initial
      -- colour, black.
      let src := if (rawSrc args[1]).trimAscii.toString == "." then "#000000"
        else rawSrc args[1]
      let native := s!"\\palette\{ {rawSrc args[0]} = {src} }"
      became "\\colorlet" native pos
      return some (← synthAt native pos, k)
    else return none
  | "geometry" | "newgeometry" =>
    -- The command forms: the same keys the package options carry
    -- (geometry manual §5: `\newgeometry` is `\geometry` restricted to
    -- the layout keys). One door for every spelling, so a key is honoured
    -- or named (W0101) identically wherever it was written.
    let (args, k) := takeGroups raws start 1
    if args.isEmpty then return none
    return some (← geometry (rawSrc (args.getD 0 #[])) pos s!"\\{name}", k)
  | "microtypesetup" =>
    -- microtype's switchboard (manual §3.1): `protrusion` and `expansion`
    -- reach the native gates, and `activate` — the manual's shorthand for
    -- both — sets the pair. A key the engine does not perform is dropped
    -- named (W0101), never silently; a bare key means `=true`, as in the
    -- manual.
    let (args, k) := takeGroups raws start 1
    if args.isEmpty then return none
    let mut keys : Array String := #[]
    let mut dropped : Array String := #[]
    for e in Decl.splitEntries (rawSrc (args.getD 0 #[])) do
      match e.splitOn "=" with
      | [] => pure ()
      | key :: v =>
        let key := key.trimAscii.toString
        let v := (String.intercalate "=" v).trimAscii.toString
        let native := if key == "activate" then ["protrusion", "expansion"]
          else if key == "protrusion" || key == "expansion" then [key]
          else []
        if native.isEmpty then
          if !key.isEmpty then dropped := dropped.push key
        else
          match v with
          | "" | "true" | "compatibility" | "nocompatibility" =>
            keys := keys ++ (native.map (s!"{·} = on")).toArray
          | "false" => keys := keys ++ (native.map (s!"{·} = off")).toArray
          | _ => dropped := dropped.push key
    unless dropped.isEmpty do
      say .W0101 s!"microtype keys without a native equivalent were dropped: \
{String.intercalate ", " dropped.toList}" pos
    if keys.isEmpty then return some (#[], k)
    let native := s!"\\page\{ {String.intercalate ", " keys.toList} }"
    became "\\microtypesetup" native pos
    return some (← synthAt native pos, k)
  | "newlength" =>
    -- `\newlength{\x}` allocates a length register at 0pt (usrguide,
    -- "Defining lengths"); the native store is a token, so a later
    -- `\setlength{\x}` and references to `\x` in other lengths resolve.
    let (args, k) := takeGroups raws start 1
    let some n := ctrlName (args.getD 0 #[]) | return none
    let native := s!"\\tokens\{ {n} = 0pt }"
    became s!"\\newlength\{\\{n}}" native pos
    return some (← synthAt native pos, k)
  | "setlength" =>
    let (args, k) := takeGroups raws start 2
    if h : args.size = 2 then
      -- e-TeX's `\dimexpr` division rounds to the nearest multiple (e-TeX
      -- manual §3.5); the native language truncates toward zero as TeX's
      -- `\divide` does. Mapping the spelling would mis-round silently, so
      -- it is refused by name instead.
      if (args[1].any fun r => match r with | .ctrl "dimexpr" _ => true | _ => false)
          && (lengthSrc args[1]).toList.contains '/' then
        say .E0375 "'\\dimexpr' division rounds to nearest; this engine's length \
arithmetic truncates toward zero as TeX's '\\divide' does" pos
          (help := "divide outside '\\dimexpr': '(\\a - \\b) / 2' truncates as TeX does")
        return some (#[], k)
      match ctrlName args[0] with
      | some "abovecaptionskip" =>
        -- The object-side caption gap (classes.dtx `\@makecaption`:
        -- `\abovecaptionskip` stands between the object and its caption):
        -- exactly the engine's `captionsep` token.
        let native := s!"\\tokens\{ captionsep = {lengthSrc args[1]} }"
        became "\\setlength{\\abovecaptionskip}" native pos
        return some (← synthAt native pos, k)
      | some "belowcaptionskip" =>
        -- The caption's text side: in this engine that is the float
        -- separation (`floatsep`), not a caption property; the LaTeX
        -- default here is 0pt for the same reason.
        say .N0102 "'\\belowcaptionskip' is not a knob here: the caption's \
text side is the float separation ('\\tokens{ floatsep = ... }')" pos
        return some (#[], k)
      | some "parskip" =>
        -- TeX's own paragraph glue is a page property here, not a token.
        let native := s!"\\page\{ parskip = {lengthSrc args[1]} }"
        became "\\setlength{\\parskip}" native pos
        return some (← synthAt native pos, k)
      | some n =>
        let native := s!"\\tokens\{ {n} = {lengthSrc args[1]} }"
        became s!"\\setlength\{\\{n}}" native pos
        return some (← synthAt native pos, k)
      | none => return none
    else return none
  | "advance" | "multiply" | "divide" =>
    -- TeX's register arithmetic (TeXbook ch. 24: ⟨advance⟩⟨numeric
    -- variable⟩⟨by⟩⟨value⟩): the engine keeps no registers, so the whole
    -- statement is named and skipped — the `by` and the value go with the
    -- command, never left behind as stray content (a bare `by` in the
    -- preamble was an E0313 cascade from one skipped name).
    let j0 := skipSpaces raws start
    match raws[j0]? with
    | some (.ctrl _ _) =>
      let j1 := skipSpaces raws (j0 + 1)
      let j2 := match raws[j1]? with
        | some (.word "by" _) => skipSpaces raws (j1 + 1)
        | _ => j1
      -- The value: one word (`2pt`), or a register chain of one or two
      -- control words (`\ht\strutbox`).
      let k := match raws[j2]? with
        | some (.word _ _) => j2 + 1
        | some (.ctrl _ _) =>
          match raws[j2 + 1]? with
          | some (.ctrl _ _) => j2 + 2
          | _ => j2 + 1
        | _ => j2
      sayOnce ("ctrl:" ++ name) .W0104
        s!"TeX register arithmetic ('\\{name}') is not supported; skipped" pos
        (demote := styInternal (← get).file name)
      return some (#[], k)
    | _ => return none
  | "NewDocumentCommand" | "newcommand" | "providecommand" | "renewcommand"
  | "DeclareDocumentCommand" | "RenewDocumentCommand" | "DeclareRobustCommand" =>
    -- One arm for the whole definer family. LaTeX's documented triple
    -- (usrguide, "Defining commands": new must not exist, renew must
    -- exist, provide keeps an existing definition) collapses here to the
    -- one policy that changes what a correct document *means*: a
    -- `\providecommand` of a name this document already bound keeps the
    -- first definition, so its body is consumed whole. The two error
    -- halves are LaTeX's to check — kernel and package names are
    -- invisible to this pass, so checking them would misfire on every
    -- `\renewcommand` of a kernel command. The native store stays
    -- last-wins, the layering mechanism.
    let xparse := name.endsWith "DocumentCommand"
    let start := skipStar raws start
    let (nameArgs, j) := takeGroups raws start 1
    let some cmd := ctrlName (nameArgs.getD 0 #[]) | return none
    if !xparse && cmd == "sectionlinesformat" then
      -- `\renewcommand\sectionlinesformat[4]{...}` is the spelling KOMA
      -- documents: the rule idiom, not a definition.
      let (_, j) := takeOpt raws j
      let (args, k) := takeGroups raws j 1
      return some (← sectionRule (rawSrc (args.getD 0 #[])) pos, k)
    let (spec, j) ← if xparse then
        let (a, j) := takeGroups raws j 1
        pure (signature (rawSrc (a.getD 0 #[])), j)
      else
        let (n, j) := takeOpt raws j
        let count := (n.bind String.toNat?).getD 0
        let (dflt, j) := takeOpt raws j
        let spec := if dflt.isSome then "o" ++ String.ofList (List.replicate (count - 1) 'm')
          else String.ofList (List.replicate count 'm')
        pure (signature spec, j)
    -- The sectioning idiom: a body that is one \@startsection call is a
    -- declarative rule over an existing heading, read as \style.
    let js := skipSpaces raws j
    if let some (.group sbody _) := raws[js]? then
      if let some out ← startSection? cmd sbody pos then
        return some (out, js + 1)
    -- The size idiom: a venue class's `\renewcommand\normalsize` whose
    -- body opens with `\@setfontsize\normalsize<size><leading>` (fntguide
    -- §"\@setfontsize"; size10.clo is where `\@xpt`/`\@xipt` get their
    -- values) declares the document's body size and leading. Both are the
    -- page's to carry: the leading lands as the factor over the engine's
    -- 6/5 base (`Ir.leadingMilli`), so a spliced .sty's 10/10.95 sets
    -- baselines at 10.95pt and the rhythm unit follows. The body's
    -- trailing display-skip internals are TeX the engine does not run;
    -- the translation note names what was taken.
    if !xparse && cmd == "normalsize" then
      if let some (.group sbody _) := raws[js]? then
        let b := skipSpaces sbody 0
        if let some (.ctrl "@setfontsize" _) := sbody[b]? then
          let (fsArgs, _) := takeGroups sbody (b + 1) 3
          if h : fsArgs.size ≥ 3 then
            if let (some sz, some ld) := (ptMacroArg fsArgs[1], ptMacroArg fsArgs[2]) then
              if sz > 0 && ld > 0 then
                let factor := (ld * 1000000 + sz * 600) / (sz * 1200)
                let native := s!"\\page\{ fontsize = {milliStr sz}pt, \
leading = {milliStr factor} }"
                became "\\renewcommand{\\normalsize}" native pos
                return some (← synthAt native pos, js + 1)
    if name == "providecommand" && (← get).bound.contains cmd then
      let (_, k) := takeGroups raws j 1
      became s!"\\providecommand\{\\{cmd}}"
        s!"nothing: '\\{cmd}' is already defined and the existing definition is kept" pos
      return some (#[], k)
    modify fun st => { st with
      bound := if st.bound.contains cmd then st.bound else st.bound.push cmd }
    let native := s!"\\define \\{cmd}({spec})"
    became s!"\\{name}\{\\{cmd}}" (native ++ " {...}") pos
    modify fun st => { st with bodyNext := 1 }
    return some (← synthAt native pos, j)
  | "DeclareMathOperator" =>
    -- `\DeclareMathOperator{\f}{name}` declares an operator name: upright,
    -- with an Op atom's spacing (amsldoc §5.1). The native spelling is a
    -- definition whose body is `\operatorname{name}`; math expansion then
    -- renders every use. The starred form's above/below display limits are
    -- not modelled — the operator still sets, its scripts beside it.
    let start := skipStar raws start
    let (args, k) := takeGroups raws start 2
    let some cmd := ctrlName (args.getD 0 #[]) | return none
    if args.size < 2 then return none
    let body := args.getD 1 #[]
    became s!"\\DeclareMathOperator\{\\{cmd}}"
      s!"\\define \\{cmd}() \{\\operatorname\{...}}" pos
    let head ← synthAt s!"\\define \\{cmd}()" pos
    return some (head.push (.group #[.ctrl "operatorname" pos, .group body pos] pos), k)
  | "hypersetup" =>
    let (args, k) := takeGroups raws start 1
    return some (← hypersetup (rawSrc (args.getD 0 #[])) pos, k)
  | "ihead" | "chead" | "ohead" | "ifoot" | "cfoot" | "ofoot"
  | "lhead" | "rhead" | "lfoot" | "rfoot" =>
    let (args, k) := takeGroups raws start 1
    let src := rawSrc (args.getD 0 #[])
    let slot := if name.startsWith "i" || name.startsWith "l" then 0
      else if name.startsWith "c" then 1 else 2
    modify fun st =>
      let st := if st.head.isEmpty && st.foot.isEmpty then { st with runPos := pos } else st
      if name.endsWith "head" then
        { st with head := (st.head.filter (·.1 != slot)).push (slot, src) }
      else
        { st with foot := (st.foot.filter (·.1 != slot)).push (slot, src) }
    return some (#[], k)
  | "fancyhead" | "fancyfoot" | "fancyhf" =>
    -- fancyhdr's primary interface (manual §2): `[places]` crosses L/C/R
    -- with E/O (even/odd). The engine has one page sequence, so E and O
    -- collapse onto the slot letter, said once; no `[places]` means every
    -- field, and an empty field clears its slots — both as the manual
    -- defines (`\fancyhf{}` is its own idiom for clearing the style).
    -- Slots land in the same gathered fields as `\lhead`'s family, so the
    -- same-slot replace policy is one policy.
    let (opt, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    let src := rawSrc (args.getD 0 #[])
    let mut slots : Array Nat := #[]
    let mut evenOdd := false
    for e in (opt.getD "LCR").splitOn "," do
      for c in e.toList do
        let c := c.toUpper
        if c == 'L' && !slots.contains 0 then slots := slots.push 0
        else if c == 'C' && !slots.contains 1 then slots := slots.push 1
        else if c == 'R' && !slots.contains 2 then slots := slots.push 2
        else if c == 'E' || c == 'O' then evenOdd := true
    if evenOdd then
      sayOnce "fancyhdr:evenodd" .N0102
        "even and odd pages are one sequence here; the field applies to every page" pos
    let toHead := name != "fancyfoot"
    let toFoot := name != "fancyhead"
    modify fun st =>
      let st := if st.head.isEmpty && st.foot.isEmpty then { st with runPos := pos } else st
      let put (parts : Array (Nat × String)) : Array (Nat × String) :=
        slots.foldl (init := parts) fun parts slot =>
          let parts := parts.filter (·.1 != slot)
          if src.trimAscii.toString.isEmpty then parts else parts.push (slot, src)
      { st with
        head := if toHead then put st.head else st.head
        foot := if toFoot then put st.foot else st.foot }
    return some (#[], k)
  | "pagestyle" =>
    let (args, k) := takeGroups raws start 1
    let v := (rawSrc (args.getD 0 #[])).trimAscii.toString
    match v with
    | "fancy" | "scrheadings" =>
      -- The styles that mean "the declared running fields apply" — which
      -- they already do here: gathered fields land as `\runninghead` /
      -- `\runningfoot` by themselves. Agreement, not a missing model (the
      -- old warning said "not modelled" about exactly what is modelled).
      became s!"\\pagestyle\{{v}}" "nothing: declared running fields apply by themselves" pos
      return some (#[], k)
    | "plain" =>
      -- article's own initial style (classes.dtx: article.cls sets
      -- \pagestyle{plain}): the centred page number in the foot, which
      -- \page{ numbers = on } spells natively — already the flow
      -- default, and the explicit form takes control under a class
      -- whose record declines it.
      became "\\pagestyle{plain}" "\\page{ numbers = on }" pos
      return some (← synthAt "\\page{ numbers = on }" pos, k)
    | "empty" =>
      modify fun st => { st with head := #[], foot := #[] }
      became "\\pagestyle{empty}" "\\page{ numbers = off }, and no running fields" pos
      return some (← synthAt "\\page{ numbers = off }" pos, k)
    | _ =>
      sayOnce "ctrl:pagestyle" .W0104
        s!"'\\pagestyle\{{v}}' names running furniture the engine does not model; ignored" pos
        (help := "plain, empty, and fancy are modelled; \\runninghead / \\runningfoot \
declare the furniture directly")
      return some (#[], k)
  | "thispagestyle" =>
    -- Only the opening page can be meant from the preamble or the document's
    -- first line; anywhere else it would need a page model we do not have.
    let (args, k) := takeGroups raws start 1
    if rawSrc (args.getD 0 #[]) == "empty" then
      modify fun st => { st with runFrom := 2 }
      became "\\thispagestyle{empty}" "\\runninghead[from = 2]{...}" pos
    return some (#[], k)
  | "linespread" =>
    let (args, k) := takeGroups raws start 1
    let native := s!"\\page\{ leading = {rawSrc (args.getD 0 #[])} }"
    became "\\linespread" native pos
    return some (← synthAt native pos, k)
  | "setstretch" =>
    -- setspace's parameterised form is \linespread by another name
    -- (setspace.sty: both set \baselinestretch).
    let (args, k) := takeGroups raws start 1
    if args.isEmpty then return none
    let native := s!"\\page\{ leading = {rawSrc (args.getD 0 #[])} }"
    became "\\setstretch" native pos
    return some (← synthAt native pos, k)
  | "singlespacing" | "onehalfspacing" | "doublespacing" =>
    -- setspace's named stretches, at the values its source sets for the
    -- 10pt base size the engine defaults to (setspace.sty:
    -- \onehalfspacing = \setstretch{1.25}, \doublespacing =
    -- \setstretch{1.667} under \@ptsize 0).
    let v := match name with
      | "singlespacing" => "1"
      | "onehalfspacing" => "1.25"
      | _ => "1.667"
    let native := s!"\\page\{ leading = {v} }"
    became s!"\\{name}" native pos
    return some (← synthAt native pos, start)
  | "selectlanguage" =>
    -- babel's mid-document switch: from here on, in flow order (babel
    -- manual §1.5). The marker is unforgeable (`@` never lexes into a
    -- control word); elaboration turns it into the language attribute,
    -- which hyphenation and both artifacts read.
    let (args, k) := takeGroups raws start 1
    if args.isEmpty then return none
    let lname := rawSrc (args.getD 0 #[])
    let tag := Locale.babelTagOf lname
    if (Locale.forTag tag).isNone then
      say .W0368 s!"no locale for language '{lname}'; English captions \
and patterns stand in" pos
        (help := "the engine ships locale records for: en, fr, de")
    modify fun st => { st with mainLang := tag }
    became s!"\\selectlanguage\{{lname}}" s!"the '{tag}' language attribute" pos
    return some (#[.ctrl ("@lang:" ++ tag) pos], k)
  | "foreignlanguage" =>
    -- One run in another language (babel manual §1.5): the content group
    -- carries the attribute. babel's optional argument holds locale
    -- modifiers the engine has no reader for; the language still lands.
    let (_, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 2
    if h : args.size = 2 then
      let lname := rawSrc args[0]
      let tag := Locale.babelTagOf lname
      if (Locale.forTag tag).isNone then
        say .W0368 s!"no locale for language '{lname}'; English captions \
and patterns stand in" pos
          (help := "the engine ships locale records for: en, fr, de")
      became s!"\\foreignlanguage\{{lname}}" s!"the '{tag}' language attribute" pos
      return some (#[.group (#[Raw.ctrl ("@lang:" ++ tag) pos] ++ args[1]) pos], k)
    else return none
  | "enquote" =>
    -- csquotes' quoting command: typographic quotes around the content,
    -- single for the starred form (csquotes manual §3.1). The delimiters
    -- are locale data (babel ini `delimiters.quotes`): « » under french,
    -- „ “ under german; the starred (inner) form takes the locale's inner
    -- pair. Nesting-aware inner quotes are not modelled: a nested
    -- \enquote repeats its own pair.
    let j := skipStar raws start
    let starred := j != start
    let k := skipSpaces raws j
    match raws[k]? with
    | some (g@(.group _ _)) =>
      let loc := (Locale.forTag (← get).mainLang).getD Locale.en
      let (o, c) := if starred then (loc.quoteInnerOpen, loc.quoteInnerClose)
        else (loc.quoteOpen, loc.quoteClose)
      became "\\enquote" s!"{o}...{c}" pos
      return some (#[.word o pos, g, .word c pos], k + 1)
    | _ => return none
  | "color" =>
    -- `\color{n}` colours to the end of the group (xcolor manual §2.6.4).
    -- The marker keeps the spelling distinct from a bare palette name:
    -- inline it declares like one, but at the flow's top level it is the
    -- document's ink, and only the explicit \color form may claim that.
    -- `@` never lexes into a control word, so no document can forge it.
    let (args, k) := takeGroups raws start 1
    let n := rawSrc (args.getD 0 #[])
    became s!"\\color\{{n}}" s!"\\{n}" pos
    return some (#[.ctrl ("@ink:" ++ n) pos], k)
  | "vspace" =>
    let start := skipStar raws start
    let (_, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    let native := s!"\\block[before = {lengthSrc (args.getD 0 #[])}]\{}"
    became "\\vspace" native pos
    return some (← synthAt native pos, k)
  | "vfill" =>
    -- \vfill is \vspace{\fill} (ltspace.dtx): fil glue between blocks.
    let native := "\\block[before = fill]{}"
    became "\\vfill" native pos
    return some (← synthAt native pos, start)
  | "newpage" | "clearpage" =>
    -- One page model: with no floats to flush, \clearpage and \newpage are
    -- the declared boundary \pagebreak names.
    became s!"\\{name}" "\\pagebreak" pos
    return some (#[.ctrl "pagebreak" pos], start)
  | "pagebreak" =>
    -- LaTeX's [0-4] demand level tunes a penalty this engine's breaker
    -- does not weigh: every \pagebreak is taken whole.
    let (opt, j) := takeOpt raws start
    if opt.isSome then
      say .N0102 "'\\pagebreak' demand levels are ignored: the break is taken" pos
    return some (#[.ctrl "pagebreak" pos], j)
  | "thepage" => return some (#[.ctrl "pagenumber" pos], start)
  | "today" =>
    -- A date is an input, and the artifact is a function of the document
    -- and its fonts alone: core reads no clock, or two builds of one
    -- source would disagree. Refused deliberately, naming what the author
    -- can write, instead of falling through as a generic unknown command.
    sayOnce "ctrl:today" .W0104
      "'\\today' asks for the day the document is built; the engine reads no \
clock, so nothing is inserted" pos
      (help := "write the date as text where it should appear; \\allow{W0104} accepts the skip")
    return some (#[], start)
  | "ul" =>
    -- soul's plain underline; the native draws it from the font's metrics
    -- and skips descenders, which is what \varul existed to fake.
    became "\\ul" "\\underline" pos
    return some (#[.ctrl "underline" pos], start)
  | "varul" =>
    -- \varul<depth>[raise][thickness]{text}, the xparse spelling built on
    -- soul. The options tune a hand-drawn rule; the native reads the font's
    -- own underline metrics, so they are dropped.
    let mut j := skipSpaces raws start
    if let some (.word w _) := raws[j]? then
      if w.startsWith "<" && w.endsWith ">" then
        j := j + 1
    let (_, j1) := takeOpt raws j
    let (_, j2) := takeOpt raws j1
    became "\\varul" "\\underline" pos
    return some (#[.ctrl "underline" pos], j2)
  | "IfValueT" | "IfValueTF" => return some (#[.ctrl "ifgiven" pos], start)
  | "ExplSyntaxOn" =>
    -- expl3 is TeX's programming layer. Nothing in it is document content,
    -- so the block is skipped whole rather than one primitive at a time.
    let mut k := start
    for j in [start:raws.size] do
      k := j + 1
      if let some (.ctrl "ExplSyntaxOff" _) := raws[j]? then break
    say .W0106 "expl3 code (\\ExplSyntaxOn … \\ExplSyntaxOff) is not supported; skipped" pos
    return some (#[], k)
  | "textbar" => return some (#[.word "|" pos], start)
  | "textperiodcentered" => return some (#[.ctrl "middot" pos], start)
  | "textendash" => return some (#[.ctrl "endash" pos], start)
  | "textemdash" => return some (#[.ctrl "emdash" pos], start)
  | "textbackslash" => return some (#[.word "\\" pos], start)
  | "textasciitilde" => return some (#[.word "~" pos], start)
  | "setkomafont" =>
    let (args, k) := takeGroups raws start 2
    if h : args.size = 2 then
      let element := rawSrc args[0]
      if Ir.styleableElements.contains element then
        -- The font spec is inline content and travels as a group, not text,
        -- so its own idioms (\\color{x}) are still rewritten by the walk.
        let native := s!"\\style\{{element}}"
        became s!"\\setkomafont\{{element}}" (native ++ "{ font = {...} }") pos
        let font : Raw := .group #[.word "font" pos, .space, .sym '=' pos, .space,
          .group args[1] pos] pos
        return some ((← synthAt native pos).push font, k)
      else
        say .W0111 s!"'\\setkomafont\{{element}}' names no styleable element; ignored" pos
          (help := "\\style{element}{ font = {...} } styles the elements the engine draws")
        return some (#[], k)
    else return none
  | "RedeclareSectionCommand" =>
    let (opt, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    let element := rawSrc (args.getD 0 #[])
    let mut keys : Array String := #[]
    for e in Decl.splitEntries (opt.getD "") do
      match e.splitOn "=" with
      | ["beforeskip", v] => keys := keys.push s!"before = {lengthOfTeX v}"
      | ["afterskip", v] => keys := keys.push s!"after = {lengthOfTeX v}"
      | _ => pure ()
    if keys.isEmpty || !Ir.styleableElements.contains element then return some (#[], k)
    let native := s!"\\style\{{element}}\{ {String.intercalate ", " keys.toList} }"
    became s!"\\RedeclareSectionCommand\{{element}}" native pos
    return some (← synthAt native pos, k)
  | "setlist" =>
    let (opt, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    let element := (opt.getD "itemize").trimAscii.toString
    let mut keys : Array String := #[]
    let mut marker : Option String := none
    for e in Decl.splitEntries (rawSrc (args.getD 0 #[])) do
      match e.splitOn "=" with
      | ["leftmargin", v] => keys := keys.push s!"indent = {lengthOfTeX v}"
      | ["itemsep", v] => keys := keys.push s!"gap = {lengthOfTeX v}"
      | ["topsep", v] => keys := keys.push s!"before = {lengthOfTeX v}"
      | "label" :: v => marker := some (String.intercalate "=" v).trimAscii.toString
      | _ => pure ()
    if let some m := marker then keys := keys.push s!"marker = {m}"
    if keys.isEmpty || !Ir.styleableElements.contains element then return some (#[], k)
    let native := s!"\\style\{{element}}\{ {String.intercalate ", " keys.toList} }"
    became s!"\\setlist[{element}]" native pos
    return some (← synthAt native pos, k)
  | "sectionlinesformat" =>
    let (_, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    return some (← sectionRule (rawSrc (args.getD 0 #[])) pos, k)
  | "setmathfont" =>
    -- fontspec's math sibling: the named face fills the math slot, and a
    -- `Path=` rides into `dir` exactly as `\setmainfont`'s does.
    let (optBefore, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    let (optAfter, k) := takeOpt raws k
    let family := rawSrc (args.getD 0 #[])
    let path : Option String :=
      ([optBefore, optAfter].filterMap id).findSome? fun opts =>
        (Decl.splitEntries opts).findSome? fun kv =>
          match Decl.splitEntry kv with
          | some ("Path", v) =>
            some (if v.startsWith "{" && v.endsWith "}" then
              ((v.drop 1).toString.dropEnd 1).toString.trimAscii.toString
            else v)
          | _ => none
    let dirPart := match path with
      | some d => s!"dir = \"{d}\", "
      | none => ""
    let native := s!"\\fonts\{ {dirPart}math = \"{family}\" }"
    became "\\setmathfont" native pos
    return some (← synthAt native pos, k)
  | "directlua" =>
    let (_, k) := takeGroups raws start 1
    -- A deliberate refusal, not a gap: Lua is another engine's extension
    -- hook, and running it is off the table by design. The help names the
    -- intent declaration that silences the warning.
    sayOnce "ctrl:directlua" .W0104
      "'\\directlua' is Lua code for luatex; the engine does not run Lua, so it is skipped" pos
      (help := "\\allow{W0104} accepts the skip")
    return some (#[], k)
  | "def" | "edef" | "gdef" | "xdef" =>
    -- The declarative/programmable line. A plain `\def\x{...}` — an
    -- undelimited parameter text `#1..#n` and a body — declares exactly
    -- what `\define` declares, and rewrites onto it (`\gdef` too: the
    -- store here is flat). `\edef`/`\xdef` expand at definition time, and
    -- a delimited parameter text is a scanning program: both are
    -- expansion-time TeX, refused by name (W0357) — the termination
    -- design's boundary, not a gap.
    let expanding := name == "edef" || name == "xdef"
    let j := skipSpaces raws start
    let cmd? := match raws[j]? with
      | some (.ctrl c _) => some c
      | _ => none
    -- The parameter text: everything between the name and the body group.
    let mut k := j + 1
    let mut params : Array Raw := #[]
    let mut found := false
    if cmd?.isSome then
      for j2 in [k:raws.size] do
        match raws[j2]? with
        | some (.group _ _) => found := true; k := j2; break
        | some r => params := params.push r; k := j2 + 1
        | none => break
    let ps := params.filter fun r => match r with | .space => false | _ => true
    let undelimited : Bool := Id.run do
      let mut n := 0
      let mut i2 := 0
      for _ in [0:ps.size] do
        match ps[i2]?, ps[i2 + 1]? with
        | some (Raw.sym '#' _), some (Raw.word w _) =>
          if w == toString (n + 1) then
            n := n + 1
            i2 := i2 + 2
          else return false
        | none, _ => break
        | _, _ => return false
      return i2 == ps.size
    match cmd? with
    | some cmd =>
      if found && !expanding && undelimited then
        let n := ps.size / 2
        let spec := String.ofList (List.replicate n 'm')
        modify fun st => { st with
          bound := if st.bound.contains cmd then st.bound else st.bound.push cmd }
        let native := s!"\\define \\{cmd}({signature spec})"
        became s!"\\{name}\{\\{cmd}}" (native ++ " {...}") pos
        modify fun st => { st with bodyNext := 1 }
        return some (← synthAt native pos, k)
      else
        -- Consume through the body group, so the definition never leaks
        -- into the document as stray content.
        let k2 := if found then k + 1 else k
        let demote := styInternal (← get).file name
        if expanding then
          sayOnce ("ctrl:" ++ name) .W0357
            s!"'\\{name}' defines by expanding at definition time; the engine has no \
expansion step, so the definition is skipped" pos
            (help := "\\define \\name(...) {body} declares typed commands") demote
        else
          sayOnce "ctrl:def-delimited" .W0357
            s!"'\\{name}' with a delimited parameter text is a TeX scanning program; \
the definition is skipped" pos
            (help := "\\define \\name(...) {body} declares typed commands") demote
        return some (#[], k2)
    | none =>
      sayOnce "ctrl:def" .W0357 s!"TeX '\\{name}' is not supported; skipped" pos
        (help := "\\define \\name(...) {body} declares typed commands")
        (demote := styInternal (← get).file name)
      return some (#[], start)
  | "newenvironment" | "renewenvironment" =>
    -- `\newenvironment{name}[n][default]{begin}{end}` is the native
    -- `\defineenv{name}(a1: content, ...) {begin} {end}`. The two body
    -- groups stay in the stream and are announced as macro bodies, so `#k`
    -- becomes `\ak` in each and idioms inside them translate as usual.
    let (args, j) := takeGroups raws (skipStar raws start) 1
    let envName := rawSrc (args.getD 0 #[])
    let (count, j) := takeOpt raws j
    let (dflt, j) := takeOpt raws j
    let n := (count.bind String.toNat?).getD 0
    let spec := if dflt.isSome then "o" ++ String.ofList (List.replicate (n - 1) 'm')
      else String.ofList (List.replicate n 'm')
    let native := s!"\\defineenv\{{envName}}({signature spec})"
    became s!"\\{name}\{{envName}}" (native ++ " {begin} {end}") pos
    modify fun st => { st with bodyNext := 2 }
    return some (← synthAt native pos, j)
  | "ifdefined" | "ifcsname" | "ifx" =>
    -- A TeX conditional is configuration for machinery that is not here.
    -- Skipped whole, both branches: elaborating either would only warn
    -- about the constructs inside it one by one.
    let mut k := start
    for j in [start:raws.size] do
      k := j + 1
      if let some (.ctrl "fi" _) := raws[j]? then break
    sayOnce "ctrl:ifdefined" .W0104
      s!"TeX conditional ('\\{name}' … '\\fi') is not supported; skipped whole" pos
    return some (#[], k)
  | "theme" =>
    -- The native spelling turns the themed mappings on exactly as
    -- `\usetheme` does. Without this the compat walk read a natively-themed
    -- document as unthemed and rewrote `\alert` to bare `\textbf`: the
    -- bundle declared an alert role no use could reach.
    let (args, _) := takeGroups raws start 1
    let tname := (rawSrc (args.getD 0 #[])).trimAscii.toString
    if (Theme.find? tname).isSome then
      modify fun st => { st with themed := true }
    return none
  | "alert" =>
    -- Themed, alert is the theme's colour AND bold: colour alone would be
    -- the only signal distinguishing the run, which WCAG 2.2 SC 1.4.1
    -- forbids (metropolis itself colours only; the divergence is
    -- deliberate). Unthemed there is no alert colour and bold stands in.
    if (← get).themed then
      let (args, k) := takeGroups raws start 1
      match args[0]? with
      | some body =>
        became "\\alert" "\\textcolor{alert}{\\textbf ...}" pos
        return some ((← synthAt "\\textcolor{alert}" pos).push
          (.group #[.ctrl "textbf" pos, .group body pos] pos), k)
      | none =>
        became "\\alert" "\\textcolor{alert}" pos
        return some (← synthAt "\\textcolor{alert}" pos, start)
    else
      became "\\alert" "\\textbf" pos
      return some (#[.ctrl "textbf" pos], start)
  | "setbeamertemplate" =>
    -- `frame footer` is the one template with a native meaning: its body
    -- is the per-frame footer note. The body group STAYS in the stream —
    -- the walk still rewrites what is inside it (a wrapper's `#1`
    -- included) and `\framefoot` takes it at elaboration.
    let (args, j) := takeGroups raws start 1
    let element := (rawSrc (args.getD 0 #[])).trimAscii.toString
    if element == "frame footer" then
      became "\\setbeamertemplate{frame footer}" "\\framefoot{...}" pos
      return some (← synthAt "\\framefoot" pos, j)
    else
      let (_, j) := takeOpt raws j
      let (bodyArgs, k) := takeGroups raws j 1
      -- A template body that carries content (footline, headline) is a
      -- dropped loss, an error the document can accept; an empty or absent
      -- body is configuration and warns.
      if (rawSrc (bodyArgs.getD 0 #[])).trimAscii.toString.isEmpty then
        sayOnce "beamer:setbeamertemplate" .W0104
          "'\\setbeamertemplate' is beamer configuration the engine does not have; skipped" pos
          (help := beamerNative.lookup "setbeamertemplate")
      else
        say .E0111
          s!"'\\setbeamertemplate\{{element}}' is dropped with its template body, which carries content" pos
          (help := ((beamerNative.lookup "setbeamertemplate").getD "") ++
            "; \\allow{E0111} accepts the loss")
      return some (#[], k)
  | "usetheme" =>
    let (_, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    let tname := (rawSrc (args.getD 0 #[])).trimAscii.toString
    -- moloch is the maintained fork of metropolis (and `m` was that
    -- theme's original name): a deck asking for either spelling gets the
    -- bundle the engine ships, named in the note.
    let tname := if tname == "metropolis" || tname == "m" then "moloch" else tname
    let native := s!"\\theme\{{tname}}"
    became "\\usetheme" native pos
    -- Only a theme the engine ships turns the themed mappings on: an
    -- unknown name leaves the document unthemed (W0314 says so), and
    -- \alert keeps its unthemed bold stand-in.
    if (Theme.find? tname).isSome then
      modify fun st => { st with themed := true }
    return some (← synthAt native pos, k)
  | "titlegraphic" =>
    -- Declared visual content for the title page, not configuration: the
    -- engine has nowhere to place it yet, so a non-empty declaration is a
    -- dropped loss; an empty one clears what does not exist and warns.
    let (args, k) := takeGroups raws start 1
    if (rawSrc (args.getD 0 #[])).trimAscii.toString.isEmpty then
      sayOnce "beamer:titlegraphic" .W0104
        "'\\titlegraphic{}' clears beamer configuration the engine does not have; skipped" pos
    else
      say .E0112
        "'\\titlegraphic' declares title-page content the engine does not place; the content is dropped" pos
        (help := "\\logo places an image on running pages; \\allow{E0112} accepts the loss")
    return some (#[], k)
  | "nolinkurl" =>
    -- Its group stays in the stream: the URL renders as its own text.
    became "\\nolinkurl" "the URL as plain text" pos
    return some (#[], start)
  | "multicolumn" =>
    -- `\multicolumn{n}{align}{text}`: spans are not modelled — the cell's
    -- text lands in its own single cell, and the short row is padded with
    -- a W0337 naming it. The span count and alignment spec are dropped.
    let (gs, k) := takeGroups raws start 3
    match gs with
    | #[_, _, text] => return some (#[.group text pos], k)
    | _ => return none
  | "bigskip" | "medskip" | "smallskip" =>
    let native := match name with
      | "bigskip" => "\\block[before = 12pt plus 4pt minus 4pt]{}"
      | "medskip" => "\\block[before = 6pt plus 2pt minus 2pt]{}"
      | _ => "\\block[before = 3pt plus 1pt minus 1pt]{}"
    became s!"\\{name}" native pos
    return some (← synthAt native pos, start)
  | "usefonttheme" =>
    -- beamer's `professionalfonts` theme turns beamer's font substitution
    -- off and keeps the document's declared fonts — the only behaviour this
    -- engine has, so the ask is agreement, not missing configuration.
    -- Every other font theme would change fonts, and warns with the native
    -- spelling.
    let (_, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    if (rawSrc (args.getD 0 #[])).trimAscii.toString == "professionalfonts" then
      became "\\usefonttheme{professionalfonts}"
        "nothing: the engine always uses the declared fonts" pos
    else
      sayOnce "beamer:usefonttheme" .W0104
        "'\\usefonttheme' is beamer configuration the engine does not have; skipped" pos
        (help := beamerNative.lookup "usefonttheme")
    return some (#[], k)
  | "setbeameroption" =>
    -- `hide notes` asks for notes kept out of the delivered pages, which
    -- is what `\note` already is here: a side channel, absent from the PDF
    -- and hidden in the HTML. Agreement, no warning. Everything else
    -- (show notes, a second screen) asks for a rendering the engine does
    -- not have.
    let (_, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    if (rawSrc (args.getD 0 #[])).trimAscii.toString == "hide notes" then
      became "\\setbeameroption{hide notes}"
        "nothing: notes never enter the delivered pages" pos
    else
      sayOnce "beamer:setbeameroption" .W0104
        "'\\setbeameroption' is beamer configuration the engine does not have; skipped" pos
        (help := "a theme is a token bundle here: \\theme selects one, and \\palette \
and \\tokens declare the design directly")
    return some (#[], k)
  | "setbeamercovered" =>
    -- beamer's default covering is invisible and `transparent` makes it
    -- show dimmed; this engine's covering is dim-not-hide always (PLAN
    -- M5), so `transparent` asks for what already happens — agreement, not
    -- missing configuration, and no warning. `transparent=<n>` shows
    -- covered text at n% opaqueness (beamer manual, \setbeamercovered:
    -- 0 transparent .. 100 opaque; 15 is the default): exactly the
    -- engine's covered fraction, so the two spellings are one idea —
    -- `\palette{ covered = n% }`, each covered colour kept at n% of
    -- itself over the page. Everything else (invisible, dynamic,
    -- still/again covered) asks for hiding or per-slide opacity the
    -- engine deliberately does not do.
    let (args, k) := takeGroups raws start 1
    let src := (rawSrc (args.getD 0 #[])).trimAscii.toString
    if src == "transparent" then
      became "\\setbeamercovered{transparent}"
        "the engine's own covering (dim-not-hide)" pos
      return some (#[], k)
    let pct? : Option Nat :=
      if src.startsWith "transparent=" then
        ((src.drop "transparent=".length).toString.trimAscii.toString).toNat?
      else none
    match pct? with
    | some n =>
      if 1 ≤ n && n ≤ 99 then
        let native := s!"\\palette\{ covered = {n}\\% }"
        became "\\setbeamercovered" native pos
        return some (← synthAt native pos, k)
      else
        sayOnce "beamer:setbeamercovered" .W0104
          s!"'\\setbeamercovered\{{src}}' asks for {if n == 0 then "invisible" else "undimmed"} \
covered content; the engine always dims (dim-not-hide)" pos
          (help := "\\palette{ covered = <n>% } sets the covered fraction")
        return some (#[], k)
    | none =>
      sayOnce "beamer:setbeamercovered" .W0104
        s!"'\\setbeamercovered\{{src}}' is not modelled; covered content always \
dims (dim-not-hide), it is never hidden" pos
        (help := "\\palette{ covered = <n>% } sets the covered fraction; 'transparent' \
and 'transparent=<n>' are understood")
      return some (#[], k)
  | _ =>
    match beamerConfig.lookup name with
    | some n =>
      let (_, j) := takeOpt raws start
      let (_, k) := takeGroups raws j n
      sayOnce ("beamer:" ++ name) .W0104
        s!"'\\{name}' is beamer configuration the engine does not have; skipped" pos
        (help := (beamerNative.lookup name).getD
          "a theme is a token bundle here: \\theme selects one, and \\palette \
and \\tokens declare the design directly")
      return some (#[], k)
    | none =>
    match configSkip.lookup name with
    | some (n, msg, help) =>
      let (_, k) := takeGroups raws start n
      sayOnce ("ctrl:" ++ name) .W0104 msg pos (help := help)
      return some (#[], k)
    | none =>
    match meaningFree.lookup name with
    | some n =>
      let (_, k) := takeGroups raws start n
      return some (#[], k)
    | none => return none

mutual

/-- Walk `raws`. The list is `raws` from index `i` on and only drives the
recursion; the array gives a rewrite O(1) access to its arguments, and `out`
accumulates so the result is built in one pass -- prepending to the recursive
result would copy it at every step. `skip` counts elements a rewrite already
consumed; they fall away one per step, which keeps this total without fuel. -/
-- conserves: none — the rewrite walk's whole job is replacement: arms
-- consume configuration and synthesize the native spelling their N0100
-- note names, so a census equality over the tree is false by design. The
-- conservation contract lives per arm — the replacement elaborates to the
-- document its note names — held by `compatConservationChecks` (an
-- executable oracle; the theorem over the monadic walk waits on the
-- applyDecl fold extraction PLAN names for T1).
private def rewriteList (inBody : Bool) (raws : Array Raw) (out : Array Raw) :
    List Raw → Nat → Nat → M (Array Raw)
  | [], _, _ => pure out
  | _ :: rest, i, skip + 1 => rewriteList inBody raws out rest (i + 1) skip
  | .ctrl "define" pos :: rest, i, 0 => do
    modify fun st => { st with bodyNext := 1 }
    rewriteList inBody raws (out.push (.ctrl "define" pos)) rest (i + 1) 0
  | .ctrl name pos :: rest, i, 0 => do
    match ← rewriteCtrl name pos raws (i + 1) with
    | some (repl, consumed) => rewriteList inBody raws (out ++ repl) rest (i + 1) consumed
    | none => rewriteList inBody raws (out.push (.ctrl name pos)) rest (i + 1) 0
  -- `#k` is the native parameter `\ak`. The digits may be glued to text
  -- (`#1,`), so the word is split. Outside a body `#` is literal: a colour.
  | .sym '#' p :: .word w wp :: rest, i, 0 => do
    let digits := w.toList.takeWhile Char.isDigit
    let tail := String.ofList (w.toList.drop digits.length)
    if !inBody || digits.isEmpty then
      rewriteList inBody raws ((out.push (.sym '#' p)).push (.word w wp)) rest (i + 2) 0
    else
      let param : Raw := .ctrl ("a" ++ String.ofList digits) p
      let out := if tail.isEmpty then out.push param else (out.push param).push (.word tail wp)
      rewriteList inBody raws out rest (i + 2) 0
  | r :: rest, i, 0 => do
    rewriteList inBody raws (out.push (← rewriteRaw inBody r)) rest (i + 1) 0

/-- Descend into a group or environment. Split from the list walk so the
recursion is structural on `Raw`: the body is a field of the head, not a tail
of the list. -/
private def rewriteRaw (inBody : Bool) : Raw → M Raw
  | .group body p => do
    -- A group is a macro body when a definition announced one. The count is
    -- zeroed for the descent and restored one lower on the way out, so a
    -- definition inside the body manages its own following group without
    -- stealing `\newenvironment`'s second half.
    let saved := (← get).bodyNext
    modify fun st => { st with bodyNext := 0 }
    let body' ← rewriteList (inBody || saved > 0) body #[] body.toList 0 0
    modify fun st => { st with bodyNext := saved - 1 }
    return .group body' p
  | .env n body p => do
    -- An `\input` wrapper switches the file its diagnostics name.
    match Parse.inputEnvFile? n with
    | some f =>
      let saved := (← get).file
      modify fun st => { st with file := f }
      let body' ← rewriteList inBody body #[] body.toList 0 0
      modify fun st => { st with file := saved }
      return .env n body' p
    | none =>
      if n == "otherlanguage" || n == "otherlanguage*" then
        -- The environment form of the switch: the body takes the language
        -- attribute; the starred form differs only in date handling the
        -- engine does not model. The first group is the language.
        let body' ← rewriteList inBody body #[] body.toList 0 0
        let (langArg, j) := takeGroups body' 0 1
        let lname := rawSrc (langArg.getD 0 #[])
        let tag := Locale.babelTagOf lname
        if (Locale.forTag tag).isNone then
          say .W0368 s!"no locale for language '{lname}'; English captions \
and patterns stand in" p
            (help := "the engine ships locale records for: en, fr, de")
        became s!"\\begin\{{n}}\{{lname}}" s!"the '{tag}' language attribute" p
        return .group (#[Raw.ctrl ("@lang:" ++ tag) p] ++ body'.extract j body'.size) p
      else if n == "document" then
        -- Inside the document environment a preamble declaration is a
        -- placement defect; the flag is what the `\usepackage` arm reads.
        modify fun st => { st with inDoc := true }
        let body' ← rewriteList inBody body #[] body.toList 0 0
        modify fun st => { st with inDoc := false }
        return .env n body' p
      else
        return .env n (← rewriteList inBody body #[] body.toList 0 0) p
  | r => pure r

end

/-- Emit the gathered running content as one declaration each. -/
private def flushRunning : M (Array Raw) := do
  let st ← get
  let line (parts : Array (Nat × String)) : String :=
    let at' (k : Nat) := (parts.filter (·.1 == k)).map (·.2) |>.toList |> String.intercalate " "
    s!"{at' 0} \\hfill {at' 1} \\hfill {at' 2}"
  let mut out : Array Raw := #[]
  let opt := if st.runFrom > 1 then s!"[from = {st.runFrom}]" else ""
  unless st.head.isEmpty do
    let native := s!"\\runninghead{opt}\{{line st.head}}"
    became "\\ihead / \\chead / \\ohead" native st.runPos
    out := out ++ (← synthAt native st.runPos)
  unless st.foot.isEmpty do
    let native := s!"\\runningfoot{opt}\{{line st.foot}}"
    became "\\ifoot / \\cfoot / \\ofoot" native st.runPos
    out := out ++ (← synthAt native st.runPos)
  -- `\thispagestyle{empty}` with no gathered field of its own still owes
  -- its gate: the opening page carries no furniture — the class-default
  -- page number included — and the run starts at `runFrom`. The
  -- empty-content spelling moves only the gate (`Elab`'s gate-only rule),
  -- so it cannot clear a declared line or suppress the default elsewhere.
  if st.runFrom > 1 && st.head.isEmpty then
    out := out ++ (← synthAt s!"\\runninghead[from = {st.runFrom}]\{}" st.runPos)
  if st.runFrom > 1 && st.foot.isEmpty then
    out := out ++ (← synthAt s!"\\runningfoot[from = {st.runFrom}]\{}" st.runPos)
  return out

/-- Rewrite a whole parsed document. The gathered running content lands just
before `\begin{document}`, where a declaration belongs. -/
def rewrite (file : String) (raws : Array Raw) : Array Raw × Array Diag :=
  let go : M (Array Raw) := do
    let raws ← condList raws #[] [] raws.toList 0
    -- After the conditionals: only live `\AtBeginDocument` bodies unwrap.
    let raws ← unwrapBeginHookList #[] raws.toList
    let out ← rewriteList false raws #[] raws.toList 0 0
    let running ← flushRunning
    let running ← rewriteList false running #[] running.toList 0 0
    let isBody : Raw → Bool
      | .env "document" _ _ => true
      | _ => false
    return match out.findIdx? isBody with
      | some i => out.extract 0 i ++ running ++ out.extract i out.size
      | none => out ++ running
  let (out, st) := go.run { file := file }
  (out, st.diags)

/-! `\\usepackage{p}` where `p.sty` exists beside the document is LaTeX's
own rule made literal (ltfiles.dtx `\\@onefilewithoptions`: find `p.sty` on
the input path and read it): the file splices into the preamble as an
`\\input` fragment, and every construct inside gets exactly the treatment
it would get written in the document — honoured through an existing arm,
or named where it stands with the `.sty`'s own positions (the input
wrapper carries the file name). Reading the file is the driver's effect
(`Main.expandLocalSty`); the splice and the option machinery are here,
pure. Where the file does not exist, the CTAN dispatch (W0103) applies
unchanged. -/

mutual

/-- One level of the candidate scan: the list drives the recursion, the
array gives argument access, `skip` counts elements a match already
consumed (`rewriteList`'s shape). -/
private def styCandList (raws : Array Raw) (out : Array String) :
    List Raw → Nat → Nat → Array String
  | [], _, _ => out
  | _ :: rest, i, skip + 1 => styCandList raws out rest (i + 1) skip
  | .ctrl "usepackage" _ :: rest, i, 0
  | .ctrl "RequirePackage" _ :: rest, i, 0 =>
    let (_, j) := takeOpt raws (i + 1)
    let (args, k) := takeGroups raws j 1
    let out := ((rawSrc (args.getD 0 #[])).splitOn ",").foldl (init := out) fun out p =>
      let p := p.trimAscii.toString
      if p.isEmpty || nativePackages.contains p || out.contains p then out
      else out.push p
    styCandList raws out rest (i + 1) (k - (i + 1))
  | r :: rest, i, 0 => styCandList raws (styCandRaw out r) rest (i + 1) 0

/-- Descend into an `\\input` wrapper — a `\\usepackage` in an `\\input`'ed
preamble file, or a `\\RequirePackage` in an already spliced `.sty`, asks
exactly as a top-level one does. The document environment is not a
wrapper, so a body-position `\\usepackage` is never a candidate: its
placement refusal is `rewriteCtrl`'s. -/
private def styCandRaw (out : Array String) : Raw → Array String
  | .env n body _ =>
    if (Parse.inputEnvFile? n).isSome then styCandList body out body.toList 0 0
    else out
  | _ => out

end

/-- The package names the preamble asks for — at any `\\input` depth — that
the engine does not know: the candidates a local `.sty` beside the
document may answer. -/
def localStyCandidates (raws : Array Raw) : Array String :=
  styCandList raws #[] raws.toList 0 0

/-- LaTeX's package option machinery, the minimum (ltclass.dtx):
`\\DeclareOption{name}{body}` binds a body to an option name,
`\\ExecuteOptions{list}` runs the named bodies (the defaults idiom), and
`\\ProcessOptions` runs the bodies of the options the `\\usepackage`
passed, in declaration order, after which the machinery is spent.
`\\ProvidesPackage`/`\\NeedsTeXFormat` identify the file and produce
nothing. A `\\DeclareOption*` (the catch-all) is dropped here and its
absence named downstream only if an option needed it; option bodies are
usually one flag-setter (`\\@xtrue`), which the conditional pass already
resolves. -/
def resolveStyOptions (passed : List String) (raws : Array Raw) : Array Raw := Id.run do
  let mut out : Array Raw := #[]
  let mut declared : Array (String × Array Raw) := #[]
  let mut i := 0
  for _ in [0:raws.size] do
    if h : i < raws.size then
      match raws[i] with
      | .ctrl "DeclareOption" _ =>
        let j := skipStar raws (i + 1)
        let (args, k) := takeGroups raws j 2
        if h2 : args.size = 2 then
          declared := declared.push ((rawSrc args[0]).trimAscii.toString, args[1])
        i := max k (i + 1)
      | .ctrl "ExecuteOptions" _ =>
        let (args, k) := takeGroups raws (i + 1) 1
        for o in (rawSrc (args.getD 0 #[])).splitOn "," do
          if let some (_, body) := declared.find? (·.1 == o.trimAscii.toString) then
            out := out ++ body
        i := max k (i + 1)
      | .ctrl "ProcessOptions" _ =>
        for (nm, body) in declared do
          if passed.contains nm then
            out := out ++ body
        let j := skipSpaces raws (i + 1)
        i := match raws[j]? with
          | some (.ctrl "relax" _) => j + 1
          | _ => i + 1
      | .ctrl "ProvidesPackage" _ | .ctrl "NeedsTeXFormat" _ =>
        let (_, k) := takeGroups raws (i + 1) 1
        let (_, k2) := takeOpt raws k
        i := max k2 (i + 1)
      | r =>
        out := out.push r
        i := i + 1
  return (out : Array Raw)

/-- The replacement for one `\\usepackage`/`\\RequirePackage` at `i`, given
the style files read: the raws standing in its place, the splice records,
and the index past its arguments — `none` when nothing it names is a local
style file, leaving the command to the CTAN dispatch. -/
private def spliceUse (stys : Array (String × Array Raw)) (raws : Array Raw)
    (cn : String) (pos : Pos) (i : Nat) :
    Option (Array Raw × Array (String × Option String × Pos) × Nat) := Id.run do
  if stys.isEmpty then return none
  let (opt, j) := takeOpt raws (i + 1)
  let (args, k) := takeGroups raws j 1
  if args.isEmpty then return none
  let pkgs := (rawSrc (args.getD 0 #[])).splitOn "," |>.map (·.trimAscii.toString)
  let passed := ((opt.getD "").splitOn ",").map (·.trimAscii.toString)
  let mut keep : Array String := #[]
  let mut splice : Array Raw := #[]
  let mut recs : Array (String × Option String × Pos) := #[]
  for p in pkgs do
    match stys.find? (·.1 == p) with
    | some (_, sraws) =>
      splice := splice.push
        (.env (Parse.inputEnv (p ++ ".sty")) (resolveStyOptions passed sraws) pos)
      recs := recs.push (p ++ ".sty", none, pos)
    | none => keep := keep.push p
  if recs.isEmpty then return none
  let mut out : Array Raw := #[]
  unless keep.isEmpty do
    out := out.push (.ctrl cn pos)
    for r in raws.extract (i + 1) j do
      out := out.push r
    out := out.push (.group #[.word (String.intercalate "," keep.toList) pos] pos)
  return some (out ++ splice, recs, k)

mutual

/-- One level of the splice: the list drives the recursion, the array gives
argument access, `skip` counts elements a replacement already consumed
(`rewriteList`'s shape). -/
-- conserves: none — replacement is the walk's job: a `\usepackage` of a
-- local file becomes that file's content.
private def applyStyList (stys : Array (String × Array Raw)) (raws : Array Raw)
    (out : Array Raw) (recs : Array (String × Option String × Pos)) :
    List Raw → Nat → Nat → Array Raw × Array (String × Option String × Pos)
  | [], _, _ => (out, recs)
  | _ :: rest, i, skip + 1 => applyStyList stys raws out recs rest (i + 1) skip
  | .ctrl cn pos :: rest, i, 0 =>
    if cn == "usepackage" || cn == "RequirePackage" then
      match spliceUse stys raws cn pos i with
      | some (repl, rs, k) =>
        applyStyList stys raws (out ++ repl) (recs ++ rs) rest (i + 1) (k - (i + 1))
      | none => applyStyList stys raws (out.push (.ctrl cn pos)) recs rest (i + 1) 0
    else
      applyStyList stys raws (out.push (.ctrl cn pos)) recs rest (i + 1) 0
  | r :: rest, i, 0 =>
    let (r', rs) := applyStyRaw stys r
    applyStyList stys raws (out.push r') (recs ++ rs) rest (i + 1) 0

/-- Descend into an `\\input` wrapper, splicing inside it as at the top
level — `\\input` parity. A record from inside a wrapper carries the
wrapper's file, so its N0020 names the `\\RequirePackage`'s own file; the
innermost wrapper fills it first and deeper nesting keeps it. The
document environment is not a wrapper: a body-position `\\usepackage` is
never spliced (its placement refusal is `rewriteCtrl`'s). -/
private def applyStyRaw (stys : Array (String × Array Raw)) :
    Raw → Raw × Array (String × Option String × Pos)
  | .env n body p =>
    if (Parse.inputEnvFile? n).isSome then
      let (body', rs) := applyStyList stys body #[] #[] body.toList 0 0
      (.env n body' p, rs.map fun (s, f0, pos) =>
        (s, f0 <|> Parse.inputEnvFile? n, pos))
    else (.env n body p, #[])
  | r => (r, #[])

end

/-- Splice the local style files the driver found: each `\\usepackage` of
one — at any `\\input` depth — becomes the file's own content, options
resolved (`resolveStyOptions`), wrapped as that file's input fragment so
every downstream diagnostic names the `.sty` and its line. The file's
constructs are then honoured or named individually by the same passes a
document goes through — no second rule set. Returns the splice records
(file, enclosing file when not the document itself, position); the read
is named once per record (N0020), built after elaboration (`styRead`),
when the honoured/named counts exist. -/
def applyLocalSty (raws : Array Raw) (stys : Array (String × Array Raw)) :
    Array Raw × Array (String × Option String × Pos) :=
  applyStyList stys raws #[] #[] raws.toList 0 0

private theorem spliceUse_empty (raws : Array Raw) (cn : String) (pos : Pos) (i : Nat) :
    spliceUse #[] raws cn pos i = none := rfl

mutual

private theorem applyStyList_empty :
    ∀ (raws out : Array Raw) (recs : Array (String × Option String × Pos))
      (l : List Raw) (i : Nat),
      applyStyList #[] raws out recs l i 0 = (out ++ l.toArray, recs)
  | _, out, recs, [], _ => by
    simp [applyStyList]
  | raws, out, recs, r :: rest, i => by
    cases r with
    | ctrl cn pos =>
      rw [applyStyList]
      split
      · rw [spliceUse_empty]
        dsimp only
        rw [applyStyList_empty raws _ recs rest (i + 1)]
        simp
      · rw [applyStyList_empty raws _ recs rest (i + 1)]
        simp
    | _ =>
      rw [applyStyList, applyStyRaw_empty]
      · dsimp only
        rw [applyStyList_empty raws _ (recs ++ #[]) rest (i + 1)]
        simp
      all_goals simp

private theorem applyStyRaw_empty : ∀ (r : Raw), applyStyRaw #[] r = (r, #[])
  | .env n body p => by
    rw [applyStyRaw]
    split
    · rw [applyStyList_empty]
      simp
    · rfl
  | .word .. | .space | .par .. | .ctrl .. | .sym .. | .group .. | .math .. | .verb .. => rfl

end

/-- The splice with nothing to splice is the identity — no change to the
tree, no record: the substitution statement's degenerate half, stated so
the descending walk itself can never perturb a document, and the shape
suffix registry's `_id`. The full substitution — each preamble-position
`\\usepackage` of a read file replaced by that file's input wrapper — is
`applyLocalSty`'s own definition; downstream, elaboration equality with a
hand-spliced document is definitional because the preamble fold treats
every input wrapper uniformly (`Elab.elabDoc`'s `@file:` markers). -/
theorem applyLocalSty_id (raws : Array Raw) : applyLocalSty raws #[] = (raws, #[]) := by
  rw [applyLocalSty, applyStyList_empty]
  simp

/-- What a spliced `.sty` yielded, counted after elaboration: a construct
was honoured when its translation note (N0100) carries the file, named
when a warning does, and a TeX internal refused when a demoted refusal
does — a note that kept its W0301/W0357 code is the demotion's signature,
and at this point in the run nothing else makes one (`\allow` acceptance
resolves later, in the driver). -/
def styCounts (sty : String) (diags : Array Diag) : Nat × Nat × Nat :=
  let mine := diags.filter fun d => d.span.any (·.file == sty)
  ((mine.filter (·.code == "N0100")).size,
   (mine.filter (·.severity == .warning)).size,
   (mine.filter fun d =>
     d.severity == .note && (d.code == "W0301" || d.code == "W0357")).size)

/-- The one N0020 construction — the note that says the file was looked
at, and how much of it took. Built after elaboration, from the splice
records `applyLocalSty` returns: the counts do not exist before it. The
spelling is compact — three counts and a long file name must fit the
message-length lint. -/
def styRead (docFile sty : String) (pos : Pos) (diags : Array Diag) : Diag :=
  let (honoured, named, refused) := styCounts sty diags
  Diag.of .N0020
    (s!"'{sty}' beside the document is read into the preamble — " ++
     s!"honoured: {honoured}, named: {named}, TeX internals refused: {refused}")
    (some ⟨docFile, pos⟩)

end LeanTex.Core.Compat
