module

public import LeanTex.Core.Lex
public import LeanTex.Core.Parse
public import LeanTex.Core.PackageImports
import LeanTex.Core.Theme
import LeanTex.Core.Decl
public import LeanTex.Core.Ir
import LeanTex.Core.BeamerColor
import LeanTex.Core.TitleTemplate
import LeanTex.Core.BibStyle
public import LeanTex.Core.Tcolorbox
import LeanTex.Core.LoopProgress

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

/-- Package interfaces the engine handles natively. Seeing one is a note,
not a warning: nothing was lost at the `\usepackage` line — a construct one
of these packages provides that the engine cannot render is named where it
is used, never at the load (`tikzpicture` renders its subset and W0334 or
E0333 names each shape outside it; `appendix`'s mark and its environment
are the sectioning walk's own, and its contents-page apparatus is W0301
where it stands, as `\nicefrac` and `\multirow` are when
a document actually uses them). `xurl` is `url` with better breaking;
`amsfonts` is a subset of what `amssymb`/`unicode-math` already provide;
`caption`/`subcaption` land on the caption path, their option interface
judged at `\captionsetup` (honoured or W0354, never silent). `animate`
lowers only whole multipage PDF requests with authored SVG companions;
playback loss is W0110 at every use, unsupported source selection W0307,
and package-wide defaults are named rather than silently discarded. -/
public def nativePackages : List String :=
  ["geometry", "hyperref", "xcolor", "color", "microtype", "enumitem", "babel",
   "beamerposter", "paracol", "tabularx",
   "fontspec", "url", "xurl", "scrlayer-scrpage", "inputenc", "fontenc", "lmodern",
   "amsmath", "amssymb", "amsfonts", "unicode-math", "parskip", "titlesec", "fancyhdr",
   "textcomp", "csquotes", "polyglossia", "graphicx", "booktabs", "array",
   "calc", "etoolbox", "xparse", "kvoptions", "setspace", "soul", "tikz",
   "caption", "subcaption", "nicefrac", "multirow", "crop",
   "appendixnumberbeamer", "natbib",
   "times", "mathptmx", "palatino", "mathpazo", "helvet", "courier",
   "libertine", "carlito", "xspace", "float", "biblatex", "appendix",
   "cleveref", "listings", "minted", "siunitx",
   "algorithm2e", "algorithmicx", "algpseudocode", "algorithm", "lineno", "environ", "amsthm",
   "cancel", "animate", "markdown", "ulem"]

/-- Beamer's colour elements, each mapped onto the engine's palette roles:
the role its `fg=` declares and the role its `bg=` declares. An empty role
is a side the engine has nowhere to put, and its value is *named* rather
than dropped.

**The element names are beamer's own, not invented here**: they are the
element list beamer's default colour theme sets
(beamercolorthemedefault.sty, which names every element beamer itself
colours, documented as the colour-element list of the beamer user guide's
"Colors" part), plus the moloch lineage's own additions
(beamercolorthememoloch.sty: `progress bar` and its two placements,
`standout`, `title separator`). Sourcing matters more here than in most
tables: a key beamer never writes is a row that can never fire, and two
rows spelled `block alerted title` — beamer writes `block title
alerted` — sat here dropping every alerted and example block title a theme
declared.

Where several beamer elements share one engine role, the engine has one
piece of furniture where beamer has several names for it, and the last
declaration wins: `frametitle` and `headline` are the same title band (the
poster lineage draws it under the second name), the three `progress bar`
placements inherit the base bar without sharing their overrides. Only the
section placement has a native PDF site; head/foot progress is named as
unsupported. `footline` and `page number in head/foot` share the footer
ink. `background canvas` has a ground and no ink: beamer's default canvas
template reads only its `bg`, painting it as a full-page rule
(beamerouterthemedefault.sty, `\defbeamertemplate*{background canvas}`), so
it is the page's `bg`, and in the body the ground of the frames after it. -/
private def beamerColorRoles : List (String × String × String) :=
  BeamerColor.roles

/-- Beamer's font elements, mapped onto the engine's styleable element and
the `\style` key that carries the font: the author line is the title page's
`author-font`, everything else its element's `font`.

**The element names are beamer's own**: beamerfontthemedefault.sty's element
list (the font-element list of the beamer user guide's "Fonts" part), plus
the moloch lineage's additions from beamerfontthememoloch.sty (`section
title`, `standout`). Where beamer's name and the engine's furniture name
differ, the furniture is the same: beamer's `section title` is the section
page's heading, its `title` and `author` the title page's two lines.

Deliberately absent, and therefore named rather than guessed: `normal text`
is the *document's* font, which is `\fonts` and not an element style;
beamer's list elements name a marker font where the engine's list style
names the item's, so mapping them would restyle the wrong thing; and
`block title`, `footline`, `headline`, `caption`, `date`, `institute`,
`subtitle` and `framesubtitle` have no styleable element here at all. -/
private def beamerFontElements : List (String × String × String) :=
  [("frametitle", "frametitle", "font"),
   ("standout", "standout", "font"),
   ("section title", "sectionpage", "font"),
   ("title", "titlepage", "font"),
   ("author", "titlepage", "author-font"),
   ("abstract title", "abstract", "font")]

/-- Beamer's font axes in selection order (`beamerbasefont.sty`,
`\beamer@usebeamerfont`): each declaration replaces its named fields, and
selection runs size, shape, series, family regardless of declaration order.
`parent` is inheritance the engine does not model and names where it stands. -/
private def beamerFontKeys : List String := ["size", "shape", "series", "family"]

/-- Classes that are an `article` with different defaults. -/
private def articleClasses : List String :=
  ["scrartcl", "scrreprt", "scrbook", "report", "book", "memoir", "letter"]

/-- Résumé classes: the same flow model with the résumé genre's contract —
`moderncv` and `res` map onto the native `resume` class, as `beamer` maps
onto `slides`. -/
private def resumeClasses : List String :=
  ["moderncv", "res"]

/-- Font-selection packages: each package's whole documented effect is
naming families for the generic slots — psnfss documentation ("Using
common PostScript fonts with LaTeX", §2, tables 1 and 2: `times` and
`palatino` set rm/sf/tt whole, `helvet` and `courier` one slot each,
`mathptmx`/`mathpazo` set rm and the math alphabet); the carlito and
libertine package READMEs name their families the same way. The faces
land as their TeX Gyre successors (tex-gyre README: Termes for Times,
Heros for Helvetica, Cursor for Courier, Pagella for Palatino) — the
OpenType faces a TeX Live tree actually carries — and the math packages
take the matching TeX Gyre math face. -/
private def fontPackages : List (String × String) :=
  [("times", "body = \"TeX Gyre Termes\", sans = \"TeX Gyre Heros\", mono = \"TeX Gyre Cursor\""),
   ("mathptmx", "body = \"TeX Gyre Termes\", math = \"TeX Gyre Termes Math\""),
   ("palatino", "body = \"TeX Gyre Pagella\", sans = \"TeX Gyre Heros\", mono = \"TeX Gyre Cursor\""),
   ("mathpazo", "body = \"TeX Gyre Pagella\", math = \"TeX Gyre Pagella Math\""),
   ("helvet", "sans = \"TeX Gyre Heros\""),
   ("courier", "mono = \"TeX Gyre Cursor\""),
   ("libertine", "body = \"Linux Libertine O\", sans = \"Linux Biolinum O\""),
   ("carlito", "sans = \"Carlito\"")]

/-- Commands that configure TeX's own machinery and change nothing this
engine models. An entry carries the reason its drop is the construct's
full meaning here, emitted as the translation note (N0100, "→ nothing:
why") — the accounting the silence guard reads, so an earned no-op is
never wordless (`rewriteCtrl_accounts`). Defended entry by entry: catcode
machinery has no counterpart here (`makeatletter`, `makeatother`,
`relax`); the LaTeX diagnostic family addresses the author through TeX's
own channels and contributes no document ink — `\PackageInfo` and its
class and generic variants write the transcript, the `Warning` and `Error`
spellings write `\@unused`, the terminal and transcript both
(latex.ltx:8773-8947, from lterror.dtx §"Error handling and tracing"), and
this engine has that channel in its own diagnostics; `frenchspacing`/`nonfrenchspacing`
toggle inter-sentence space
the engine sets uniformly either way; lineno's `linenomath`
pair wraps displays that are numbered like every galley line already
(the recorded divergence in testdata/compat-index/lineno.txt);
`selectfont` commits NFSS declarations that apply where they stand here;
`noindent` suppresses a first-line indent no paragraph here carries —
paragraphs are set space-separated, with no indent in any class
(`Ir.Block.quote` records the same fact for `\listparindent`), so the
ask is met before it is made; were a first-line indent ever declared,
this entry would become an arm emitting the paragraph's suppression.
An entry whose drop is NOT its full meaning carries `none`: it stays
consumed, and the dispatcher's guard names it (W0387,
`\allow`-acceptable) instead of this table earning it silence it has
not paid for — the `Error` spellings are exactly that case. Their groups
must be consumed, or a style's error text ships as ink (the defect the
warning rows fixed), but an error is a signal and not a no-op, so the
drop is named rather than earned silence. Table rules
(`midrule`, `toprule`, …) are NOT here: they are the table elaborator's
vocabulary and must reach it. -/
public def meaningFree : List (String × Nat × Option String) :=
  [("makeatletter", 0, some "@-names are always readable here"),
   ("makeatother", 0, some "@-names are always readable here"),
   ("relax", 0, some "it means do nothing"),
   ("PackageWarning", 2,
    some "package diagnostics address TeX's log, not the document"),
   ("PackageWarningNoLine", 2,
    some "package diagnostics address TeX's log, not the document"),
   ("PackageInfo", 2,
    some "package diagnostics address TeX's log, not the document"),
   ("PackageNote", 2,
    some "package diagnostics address TeX's log, not the document"),
   ("PackageNoteNoLine", 2,
    some "package diagnostics address TeX's log, not the document"),
   ("ClassWarning", 2,
    some "class diagnostics address TeX's log, not the document"),
   ("ClassWarningNoLine", 2,
    some "class diagnostics address TeX's log, not the document"),
   ("ClassInfo", 2,
    some "class diagnostics address TeX's log, not the document"),
   ("ClassNote", 2,
    some "class diagnostics address TeX's log, not the document"),
   ("ClassNoteNoLine", 2,
    some "class diagnostics address TeX's log, not the document"),
   ("GenericWarning", 2,
    some "package diagnostics address TeX's log, not the document"),
   ("GenericInfo", 2,
    some "package diagnostics address TeX's log, not the document"),
   ("MessageBreak", 0, some "a line break in a log message, not in the document"),
   ("@latex@warning", 1,
    some "kernel diagnostics address TeX's log, not the document"),
   ("@latex@warning@no@line", 1,
    some "kernel diagnostics address TeX's log, not the document"),
   ("@latex@info", 1,
    some "kernel diagnostics address TeX's log, not the document"),
   ("@latex@info@no@line", 1,
    some "kernel diagnostics address TeX's log, not the document"),
   ("@latex@note", 1,
    some "kernel diagnostics address TeX's log, not the document"),
   ("@latex@note@no@line", 1,
    some "kernel diagnostics address TeX's log, not the document"),
   -- The `Error` spellings: consumed so their text never ships as ink, but
   -- an error is a signal, so the drop is named (W0387) rather than earned
   -- as silence. Arities are LaTeX's own (latex.ltx:8799, 8845, 8871, 8913).
   ("PackageError", 3, none),
   ("ClassError", 3, none),
   ("GenericError", 4, none),
   ("@latex@error", 2, none),
   ("noindent", 0, some "no paragraph carries a first-line indent here"),
   ("frenchspacing", 0, some "inter-sentence space is uniform here either way"),
   ("nonfrenchspacing", 0, some "inter-sentence space is uniform here either way"),
   ("selectfont", 0, some "font declarations apply where they stand"),
   ("linenomath", 0, some "display math lines are numbered like every galley line"),
   -- natbib's \shortcites{keys} exempts keys from longnamesfirst's full
   -- first citations; the engine sets every citation short, which is what
   -- it asks, and names the option itself (W0101).
   ("shortcites", 1, some "citations are set short throughout, which is what it asks"),
   ("endlinenomath", 0, some "display math lines are numbered like every galley line")]

/-- Declarations whose loss is real — justification, breaking tolerance,
hyphenation language, page furniture — skipped with a warning that names
what changed, never silently: they used to sit in the silent list under a
comment claiming they say nothing about the document, and they do. Each
entry: arguments consumed, the message, the help. -/
public def configSkip : List (String × Nat × String × Option String) :=
  [-- The four ragged-setting declarations are not here: the block walk gives
   -- the rest of the scope the setting it declares, on the side it declares
   -- (Ir.Block.ragged carries the flush side).
   ("sloppy", 0,
    "'\\sloppy' loosens TeX's line-breaking tolerance; the breaker keeps \
its own and an overfull line warns by itself", none)]

/-- Where a LaTeX length parameter's value goes, decided by what LaTeX's
own code does with it and by which engine site reads it. -/
public inductive ParamSite where
  /-- A page property: `\page{ key = ... }`. -/
  | page (key : String)
  /-- A token an engine site reads under this name. -/
  | token (name : String)
  /-- `\leftmargin` at list depth `level`: the class's `\@list` for that
  depth reads `\leftmargin<level>` into it at every list (size10.clo). -/
  | listIndent (level : Nat)
  /-- `\normalsize`, which `\begin{document}` runs, sets it again (size10.clo,
  measured under lualatex): a preamble value never reaches the body, where
  `body` is its site. -/
  | sizeReset (body : ParamSite)
  /-- `\list` or the class's `\@listi` sets it again at every list
  (ltlists.dtx, size10.clo): a value set outside a list reaches no list. -/
  | listReset
  /-- LaTeX reads it where `what` says; no engine site does. -/
  | unmodelled (what : String)
  deriving Repr, BEq

/-- The kernel's list environments, each a `\list` whose own settings
follow its level's parameters (ltlists.dtx). -/
private def listEnvs : List String := ["itemize", "enumerate", "description"]

/-- Environments whose bodies the elaborator reads as table cells. -/
public def tableEnvs : List String := ["tabular", "tabular*", "tabularx"]

/-- Math-mode entry environments (latex.ltx, amsmath.sty). Their bodies
belong to the math parser, just as a `Raw.math` body does.
`beamerTemplateChecks` quantifies over the elaborator's entry catalogues. -/
private def mathEnvs : List String :=
  ["equation", "equation*", "displaymath", "align", "align*", "gather", "gather*"]

/-- The kernel and booktabs length parameters, each with its site. A name
not here is a length of the document's own: a token of its name. -/
public def paramSites : List (String × ParamSite) :=
  [("parskip", .page "parskip"),
   ("textwidth", .page "textwidth"),
   ("headsep", .page "headsep"),
   ("footskip", .page "footskip"),
   ("abovecaptionskip", .token "captionsep"),
   ("topsep", .token "topsep"),
   ("floatsep", .token "floatsep"),
   ("footins", .token "footins"),
   ("tabcolsep", .token "tabcolsep"),
   ("heavyrulewidth", .token "heavyrulewidth"),
   ("lightrulewidth", .token "lightrulewidth"),
   ("cmidrulewidth", .token "cmidrulewidth"),
   ("cmidrulekern", .token "cmidrulekern"),
   ("aboverulesep", .token "aboverulesep"),
   ("belowrulesep", .token "belowrulesep"),
   ("abovetopsep", .token "abovetopsep"),
   ("belowbottomsep", .token "belowbottomsep"),
   ("doublerulesep", .token "doublerulesep"),
   ("leftmargini", .listIndent 1), ("leftmarginii", .listIndent 2),
   ("leftmarginiii", .listIndent 3), ("leftmarginiv", .listIndent 4),
   ("leftmarginv", .listIndent 5), ("leftmarginvi", .listIndent 6),
   ("abovedisplayskip", .sizeReset (.token "abovedisplayskip")),
   ("belowdisplayskip", .sizeReset (.token "belowdisplayskip")),
   ("abovedisplayshortskip", .sizeReset (.token "abovedisplayshortskip")),
   ("belowdisplayshortskip", .sizeReset (.token "belowdisplayshortskip")),
   ("baselineskip", .sizeReset (.unmodelled
      "sets the leading; the leading here is the page's")),
   ("leftmargin", .listReset), ("itemsep", .listReset), ("parsep", .listReset),
   ("itemindent", .listReset), ("listparindent", .listReset), ("rightmargin", .listReset),
   ("parindent", .unmodelled "indents a paragraph's first line; paragraphs here are set flush"),
   -- The class's `\partopsep`, which only a level whose `\@list` sets its
   -- own leaves behind (size10.clo's `\@listiii`): the one resolving site
   -- spends a declared value (`Ir.partopsepFor`).
   ("partopsep", .token "partopsep"),
   ("labelsep", .unmodelled "separates a list label from its item; the gap here is half an em"),
   ("labelwidth", .unmodelled "boxes a list label; a label here sets at its own width"),
   ("footnotesep", .unmodelled "struts a footnote's first line; the strut here follows the type"),
   ("columnsep", .token "columnsep"),
   ("arraycolsep", .unmodelled "pads an array's columns; the padding here is half an em"),
   ("jot", .unmodelled "adds space between an alignment's rows, which no site here reads"),
   ("fboxsep", .unmodelled "pads a framed box, which no site here reads"),
   ("fboxrule", .unmodelled "rules a framed box, which no site here reads"),
   ("arrayrulewidth", .unmodelled "sets a table rule's thickness, which no site here reads"),
   ("unitlength", .unmodelled "scales a picture environment, which no site here reads")]

/-- Is `n` a parameter `\normalsize` sets again (`ParamSite.sizeReset`)? -/
private def sizeReset (n : String) : Bool :=
  match paramSites.lookup n with
  | some (.sizeReset _) => true
  | _ => false

/-- Beamer configuration commands: how many `{...}` arguments each carries.
The engine has no beamer templating layer, so each is skipped whole — the
construct, its options, and its arguments — with one warning naming it (and
its native spelling, where one exists). What must never happen is the
arguments leaking into elaboration as stray content (that was an E0313
cascade per construct). `\usetheme` is not here: it rewrites to `\theme`.
Neither is `\setbeamertemplate`: `frame footer` has a native meaning
(`\framefoot`) and its own arm; every other template skips there. And
neither are `\usefonttheme` and `\setbeameroption`, whose own arms silence
the one argument each that asks for what the engine already does. And
neither are `\setbeamercolor` and `\setbeamerfont`: each element beamer
names is a `\palette` entry or a `\style` key, and each has its own
translating arm. -/
private def beamerConfig : List (String × Nat) :=
  [("usecolortheme", 1),
   ("useinnertheme", 1),
   ("useoutertheme", 1),
   ("metroset", 1),
   ("beamertemplatenavigationsymbolsempty", 0)]

/-- The native spelling a skipped beamer construct now has, named in its
warning's help: a warning the author can act on beats a dead end. -/
public def beamerNative : List (String × String) :=
  [("usecolortheme", "\\theme{name} selects a token bundle; \\palette overrides its entries"),
   ("usefonttheme", "\\fonts selects families; \\style{element}{ font = {...} } styles one element"),
   ("setbeamercolor", "declare the colour with \\palette{ name = #RRGGBB }"),
   ("setbeamerfont", "declare it with \\style{element}{ font = {...} }"),
   ("metroset", "\\theme selects a token bundle; \\tokens and \\palette declare \
its entries directly"),
   ("setbeamertemplate", "'frame footer' translates to \\framefoot{...}; \\style{element}{...} \
styles elements; \\runningfoot sets a document footer"),
   ("addtobeamertemplate", "put \\smallskip, \\medskip or \\bigskip at a block's body start; \
\\framefoot sets a frame footer")]

/-- Classes that produce a presentation: `beamer` (which rewrites to
`slides`) and `slides` itself. What a beamer mode specification is read
against — beamer's article mode keeps a frame the presentation omits. -/
public def presentationClasses : List String := ["beamer", "slides"]

/-- Beamer's class options load the two AMS packages together unless the
`noamsthm` key occurs. Its value is immaterial, as in Beamer's keyval handler
(`beamer.cls` and `beamerbaseoptions.sty`, Beamer 3.77).
The native slides class has no implicit TeX package dependencies. -/
public def classPackages (cls : String) (options : List String) : List String :=
  let disabled := options.any fun option =>
    let key := ((option.splitOn "=").head!).trimAscii.toString
    let key := if key.startsWith "{" && key.endsWith "}" then
      ((key.drop 1).toString.dropEnd 1).toString else key
    String.ofList (key.toList.filter (!·.isWhitespace)) == "noamsthm"
  if cls == "beamer" && !disabled then ["amsmath", "amsthm"] else []

/-- The class's AMS support is one decision, shared by package queries and
native package admission. -/
public theorem classPackages_ams_agree (cls : String) (options : List String) :
    ("amsmath" ∈ classPackages cls options) ↔
      ("amsthm" ∈ classPackages cls options) := by
  dsimp only [classPackages]
  split <;> simp

/-- beamer's theme-loading family, and the file each member asks the input
path for. `\usetheme{X}` **is** `\usepackage{beamerthemeX}` — beamer defines
the whole family through the package loader (beamerbasethemes.sty), so the
only thing that differs between the five slots is the prefix. The candidate
scan and the splice both read this one list, so a slot named here is a slot
both honour and neither can drift from the other
(`themeAsking_candidates`). The package dispatch reads it too, through
`themeSlotOfPackage?`: the identity runs in both directions, so the file
name a theme writes to inherit another resolves to the slot it names
(`themeSpellingChecks`). -/
@[expose] public def themeAsking : List (String × String) :=
  [("usetheme", "beamertheme"),
   ("usecolortheme", "beamercolortheme"),
   ("usefonttheme", "beamerfonttheme"),
   ("useinnertheme", "beamerinnertheme"),
   ("useoutertheme", "beameroutertheme")]

/-- moloch is the maintained fork of metropolis, and `m` was that theme's
original name (moloch README): a deck asking for any of the three gets the
bundle the engine ships. One function because three spellings reach the
same bundle and two surfaces ask — the `\usetheme` slot and the
`beamertheme<name>` package name — and an alias honoured on one surface
only is the drift this closes. -/
private def themeAlias (nm : String) : String :=
  if nm == "metropolis" || nm == "m" then "moloch" else nm

/-- beamer's file-name spelling of a theme-family member, resolved to the
slot it names, that slot's prefix, and the theme name: `beamerthemeX` is
`\usetheme{X}`, `beamercolorthemeX` is `\usecolortheme{X}`, and so for each
slot. `themeAsking` read backwards — the same identity, so neither spelling
can mean something the other does not. The prefixes are mutually exclusive
(they differ at the character after `beamer`), so the first match is the
only match. -/
public def themeSlotOfPackage? (p : String) : Option (String × String × String) :=
  themeAsking.findSome? fun (slot, pre) =>
    if p.startsWith pre && p.length > pre.length then
      some (slot, pre, (p.drop pre.length).toString)
    else none

/-- The kernel's box commands, as the two numbers that tell them apart: how
many `[...]` runs stand before the content, and how many mandatory `{...}`
groups stand before the content group. `\\mbox{text}` declares no box;
`\\makebox[width][pos]{text}` declares one optionally (latex.ltx,
`\\@makebox`); `\\parbox[pos][height][inner-pos]{width}{text}` declares one
always (latex.ltx, `\\@iiiparbox`), and its width is a *dimension in a brace
group* — which is why the unknown-command recovery, whose rule is "keep the
braced arguments as text", set a width as prose beside a label. A further box
command is a row here, never an arm of its own. -/
public def boxShape : List (String × Nat × Nat) :=
  [("mbox", 0, 0), ("makebox", 2, 0), ("parbox", 3, 1)]

/-- Where a deferred declaration replays. A hook is a deferred declaration,
and every hook LaTeX documents names one of these points; the engine has one
deferral mechanism and each hook is a row in `deferredHooks`, never an arm of
its own.

`endPreamble` is the last position of the preamble, `beginDocument` the
instant `\\begin{document}` opens — the seam, whose two sides this engine
realizes structurally: declarations before the `document` environment,
content inside it. -/
private inductive DeferPoint where
  | endPreamble
  | beginDocument
deriving BEq, Repr

/-- The deferral table: one row per hook. `\\AtBeginDocument` (ltfiles.dtx,
the begindocument hook) replays at `\\begin{document}`;
`\\AtEndPreamble` (etoolbox manual §3) replays at the end of the preamble.
A further hook costs a row here and nothing else. -/
private def deferredHooks : List (String × DeferPoint) :=
  [("AtBeginDocument", .beginDocument), ("AtEndPreamble", .endPreamble)]

/-- The native declarations the *preamble* reads and the body refuses, so a
hook body's declaration half rides to the seam's preamble side rather than
being named misplaced. It restates `Elab.declCtrl ++ Elab.runningCtrl`,
which sits above this module and cannot be imported here; the restatement is
not allowed to drift — `hookSeamChecks` fails the moment the two disagree,
in either direction. -/
public def hookPreambleSide : List String :=
  ["page", "pdfmeta", "assert", "fonts", "palette", "tokens", "style", "output",
   "theme", "chrome", "pictures", "allow", "runninghead", "runningfoot"]

/-- The native declarations a compatibility help text may name, as the
vocabulary the translation sweep reads. `hookPreambleSide` is the preamble
half — it already restates the elaborator's declaration set — and
`framefoot` is the one body-level declaration a compat help names, the
per-frame footer `\setbeamertemplate{frame footer}` translates into. The
sweep requires every help text to name something in here
(`translationOwedChecks`), so a help naming a declaration this list does not
carry fails rather than being skipped. -/
public def nativeDeclarations : List String := hookPreambleSide ++ ["framefoot"]

/-- **Constructs whose help text names an engine declaration and which the
engine nevertheless does not translate, each with the reason it cannot.**

The invariant behind the list: *a construct whose diagnostic names its own
translation is translated, not dropped.* A help text naming a mechanical
translation is a translation the engine should perform — every fact needed is
in the source, and telling the author to do it by hand is the engine
declining work it could do. Seventeen sites in one theme of the private
reference corpus accumulated behind two such help texts before anyone counted
them, and both are now translated (`beamerColorRoles`, `beamerFontElements`).

A row here is a *declared* exception, never a silence: it says why the named
declaration cannot receive this construct. `translationOwedChecks` closes the
list against `beamerNative` in both directions — a help text that names a
declaration either translates, with a witness, or lands here with its
reason — so the next seventeen cannot accumulate unnoticed. -/
public def translationRefused : List (String × String) :=
  [("usecolortheme", "a token bundle is whole here: the engine installs a \
palette, tokens and styles together, so it has nothing that receives a \
colour-only sub-theme. The bundle of that name, where one is shipped, \
already carries the colours"),
   ("usefonttheme", "a font theme is a substitution policy, not a family \
list: it renames what beamer's own elements select. The engine has one \
policy — keep the document's declared fonts — which is what \
'professionalfonts' asks for, and that spelling its arm agrees with"),
   ("metroset", "the keys are the theme's own option vocabulary, not engine \
tokens; each would need its own mapping, and the shipped bundle of that \
lineage already carries the design the options adjust"),
   ("addtobeamertemplate", "only preamble block-begin additions of the \
standard skips translate; arbitrary template injections have no native \
receiver. Where a refused body carries content its loss is E0111's, \
which is a dropped body and not a style key")]

/-- A definition the conditional pass can read: its replacement text and the
two prefixes its meaning carries, `\long` and e-TeX's `\protected`, which
`\ifx` compares beside the text (TeXbook chapter 20: a `\long` macro and its
short twin are different meanings). An optional command is an outer wrapper
holding its default and the name of a separately scoped inner definition
(latex.ltx, `\@argdef`): a `\let` alias retains its default while following
redefinitions of that inner text. `live`: the use must read a copied
meaning, select an optional argument or execute a conditional, flag setting
or definition, itself or through a macro it uses, so the pass expands it
where it is used.
`serial` orders bindings, `textSerial` their replacement texts. A `\let`
makes a new binding but copies the text's identity. Expansion descends
these two orders: the copy can execute inside an older macro without
hiding bindings that macro already sees. -/
private structure CondVal where
  raws : Array Raw
  long : Bool
  prot : Bool
  arity : Nat := 0
  optional : Option (String × Array Raw) := none
  live : Bool := false
  serial : Nat := 0
  textSerial : Nat := 0

/-- One change the conditional pass made to its definition state, with what
it replaced (`none`: the name was not bound, or the flag not declared). -/
private inductive CondUndo where
  | bind (n : String) (prev : Option (Option CondVal))
  | flag (n : String) (prev : Option Bool)

/-- Where the definition state stood when a group or environment opened: the
save stack's height, the globals made so far, the picture's own names. -/
private structure CondMark where
  undo : Nat
  globals : Nat
  picBound : Nat
  primitives : Nat

/-- A preamble definition of `name` (the one stamped `serial`) whose text,
the group at `pos` in `file`, went out without what only a use decides. The
elaborator reads such a text itself where no use the pass sees stands — a
built-in's redefinition and the macros it reaches, read at the preamble's
end — so the pass settles it there, against the state in force then. -/
private structure CondPending where
  name : String
  serial : Nat
  file : String
  pos : Pos

/-- Package/class declarations read by `condList`, and separate reservations
for bodies admitted by the loader. The first declaration's options stand;
an input wrapper without its originating package call carries `none`.
`passed` holds each `\PassOptionsToPackage` list in flow order. Repeated
body admissions use `PackageImports.admit`, including the kernel's option
clash comparison (latex.ltx, `\@onefilewithoptions`). -/
private structure LoadSet where
  pkgs : Array (String × Option (Array String)) := #[]
  passed : Array (String × Array String) := #[]
  /-- Bodies already admitted, including local files still executing.
  Merely recording a declaration in `pkgs` does not reserve its body. -/
  imports : PackageImports.Loads := []
  /-- Native rewriting consumes the executed stream later. Replaying option
  passes here keeps a late pass from altering an earlier native load. -/
  rewritePassed : Array (String × Array String) := #[]
  /-- Class option passes are likewise replayed at their execution point. -/
  rewriteClassPassed : Array (String × Array String) := #[]
  cls : Option (String × Array String) := none
  clsPassed : Array (String × Array String) := #[]
  deriving Repr, BEq, Inhabited

/-- One TeX parameter assignment, as TeX scans it (TeXbook ch. 24:
⟨variable⟩[=]⟨value⟩, and `\advance`⟨variable⟩[by]⟨value⟩): the parameter,
whether the value adds to it, and the raws of the value. -/
private structure TexAssign where
  name : String
  add : Bool
  value : Array Raw
  deriving Repr

/-- hyperref's link colouring as its options accumulate — the package's
options, then each `\hypersetup` (hyperref.sty's `colorlinks`, `hidelinks`,
`linkcolor`, `urlcolor`, `citecolor`, `allcolors`); the colours default to
hyperref's red, magenta and green. -/
private structure LinkSetup where
  colorlinks : Bool := false
  link : String := "red"
  url : String := "magenta"
  cite : String := "green"
  deriving Repr

/-- One hyperref key read into the setup; `none` for a key that sets no link
colour. -/
private def LinkSetup.read (l : LinkSetup) (k v : String) : Option LinkSetup :=
  match k with
  | "colorlinks" => some { l with colorlinks := v != "false" }
  | "hidelinks" => some { l with colorlinks := false }
  | "linkcolor" => some { l with link := v }
  | "urlcolor" => some { l with url := v }
  | "citecolor" => some { l with cite := v }
  | "allcolors" => some { l with link := v, url := v, cite := v }
  | _ => none

/-- The setup as the declarations the elaborator reads: each link kind's
`\style{…}{ color = … }` under `colorlinks`, nothing otherwise — without it
hyperref's `\Hy@colorlink` paints nothing, and a link keeps the running
colour. -/
private def LinkSetup.native (l : LinkSetup) : String :=
  if l.colorlinks then
    s!"\\style\{link}\{ color = {l.link} }\\style\{url}\{ color = {l.url} }" ++
      s!"\\style\{cite}\{ color = {l.cite} }"
  else ""

/-- Written tokens indexed before execution; generated commands inherit the
written call's coordinates and therefore its spelling. -/
public abbrev SourceTriggers := Std.HashMap (String × Nat × Nat) String

/-- Only original source boundaries may index written tokens. A normalized
fragment's fallback coordinates can coincide with an unrelated written token. -/
@[expose] public def SourceTriggers.writtenAt (sources : SourceTriggers) (file : String)
    (pos : Pos) : Option String :=
  if pos.sourceMapped then sources[(file, pos.line, pos.col)]? else none

/-- Restore a downstream diagnostic's written trigger from lexical evidence,
retaining an explicit trigger when no source token owns its span. -/
@[expose] public def SourceTriggers.attribute (sources : SourceTriggers) (d : Diag) : Diag :=
  { d with trigger := (d.span.bind fun s =>
      sources.writtenAt s.file s.pos).orElse (fun _ => d.trigger) }

/-- Attribution changes presentation only, including for accepted or scoped
records; every other diagnostic field is exactly the input field. -/
public theorem SourceTriggers.attribute_record_exact (sources : SourceTriggers) (d : Diag) :
    { sources.attribute d with trigger := d.trigger } = d := by rfl

/-- Reapplying the same lexical evidence cannot change a diagnostic again. -/
public theorem SourceTriggers.attribute_fixed_point (sources : SourceTriggers) (d : Diag) :
    sources.attribute (sources.attribute d) = sources.attribute d := by
  unfold SourceTriggers.attribute
  cases d.span.bind (fun s => sources.writtenAt s.file s.pos) <;> simp

/-- Failed source mapping cannot borrow any token from the index, regardless
of its contents; all diagnostic fields, including explicit evidence, survive. -/
public theorem SourceTriggers.attribute_unmapped_id (sources : SourceTriggers) (d : Diag)
    (h : ∀ s, d.span = some s → s.pos.sourceMapped = false) :
    sources.attribute d = d := by
  have absent : (d.span.bind fun s => sources.writtenAt s.file s.pos) = none := by
    cases hs : d.span with
    | none => simp
    | some s => simp [SourceTriggers.writtenAt, h s hs]
  unfold SourceTriggers.attribute
  rw [absent]
  rfl

mutual

/-- Capture lexical evidence before compatibility consumes or synthesizes
commands. Input wrappers change only their contents' filename. A desugared
Markdown command has no lexical evidence, so its generated TeX spelling is
never reported as authored. Environments keep the literal opening control
word, without reconstructing braces or whitespace the parser consumed.
Math keeps its recorded opener, never a spelling inferred from display mode.
Words and symbols need the same original evidence: their rendered values can
be normalized or synthesized and cannot establish what the author wrote. -/
-- conserves: none — an index of the parsed surface, before IR exists.
private def sourceTriggers (file : String) (acc : SourceTriggers) :
    List Raw → SourceTriggers
  | [] => acc
  | r :: rest => sourceTriggers file (sourceTrigger file acc r) rest

private def sourceTrigger (file : String) (acc : SourceTriggers) : Raw → SourceTriggers
  | .ctrl _ p | .verb _ _ p | .word _ p | .sym _ p =>
    match p.command with
    | some command => acc.insertIfNew (file, p.line, p.col) command
    | none => acc
  | .group body _ => sourceTriggers file acc body.toList
  | .math _ body p =>
    let acc := match p.command with
      | some command => acc.insertIfNew (file, p.line, p.col) command
      | none => acc
    sourceTriggers file acc body.toList
  | .env n body p =>
    match Parse.inputEnvFile? n with
    | some child => sourceTriggers child acc body.toList
    | none =>
      let acc := match p.command with
        | some command => acc.insertIfNew (file, p.line, p.col) command
        | none => acc
      sourceTriggers file acc body.toList
  | .space | .par _ => acc

end

/-- A file read reached by the bounded macro evaluator. The filename is
already bound by the call's arguments; stored definitions and unselected
branches produce no request. The driver supplies parsed surface tokens. -/
public structure InputRequest where
  command : String
  file : String
  pos : Pos
  /-- The call token's position, distinct from a macro's attributed use site. -/
  callPos : Pos
  /-- The executed operand slice. Filename, options and the style-file
  candidate scan all read this one value. -/
  operands : Array Raw
  deriving Repr, BEq

/-- An actual reader call and whether it supplied parsed input. This does
not infer filesystem success from a diagnostic or from a source scan. -/
public structure InputAttempt where
  request : InputRequest
  answered : Bool
  deriving Repr, BEq

private structure St where
  file : String
  diags : Array Diag := #[]
  sourceTriggers : SourceTriggers := {}
  inputAttempts : Array InputAttempt := #[]
  /-- Running-content slots gathered across `\ihead`/`\chead`/`\ohead`,
  landing as one declaration once the preamble ends. Slot 0 inner, 1 centre,
  2 outer — one entry per slot: a same-slot repeat replaces, as fancyhdr
  defines it (fancyhdr manual §2: `\lhead` *redefines* the field). -/
  head : Array (Nat × String) := #[]
  foot : Array (Nat × String) := #[]
  runPos : Pos := { line := 1, col := 1 }
  runFrom : Nat := 1
  /-- article.cls resets the counter after titlepage only in oneside mode.
  Its unstarred `\ProcessOptions` applies `twoside` after `oneside` when
  both are present, irrespective of their order in the option list. -/
  titlepageReset : Bool := true
  /-- Upcoming groups that are macro bodies, where `#k` names a parameter:
  one for a `\define`/`\newcommand` body, two for `\newenvironment`'s begin
  and end halves. Scoped: descending into a group consumes one and shields
  the count from the group's own definitions. -/
  bodyNext : Nat := 0
  /-- environ's environments whose code never places `\BODY`, with the
  signature letters their arguments read: each use keeps its arguments
  and drops the body, which environ collects and discards. -/
  discardEnvs : Array (String × String) := #[]
  /-- The first of paracol's two column shares, in per mille. The package's
  `\columnratio` is global and its final column receives the remainder
  (`paracol.sty`, `\pcol@setcolwidth@r`). -/
  paracolRatio : Nat := 500
  /-- Switching commands belong to the enclosing paracol flow. Its close
  splits them after the ordinary rewrite has read local length settings. -/
  inParacol : Bool := false
  /-- A `\usetheme` was seen: `\alert` then maps to the theme's alert colour
  rather than the unthemed bold stand-in. -/
  themed : Bool := false
  /-- The declared class produces a presentation. What a beamer *mode*
  specification is read against: `<presentation:0>` suppresses a frame only
  where the artifact is the presentation it addresses — beamer's article mode
  keeps exactly those frames, so a class-blind reading deletes content. -/
  deck : Bool := false
  /-- The font slots (`body`, `sans`, `mono`) a fontspec or babel declaration
  has named so far, in preamble order: whether a package that measures its
  lengths as it loads measured them in Latin Modern or in a declared face. -/
  facesDeclared : Array String := #[]
  /-- The main language's BCP 47 tag, from babel's package options (last
  language option = main, babel's rule): what `\enquote` reads its quote
  delimiters through. A `\selectlanguage` outside the body leaves it:
  `\begin{document}` selects the main language again. -/
  mainLang : String := "en"
  /-- Inside the document environment: where a preamble declaration —
  `\usepackage` first among them — is a placement defect (W0340), never
  a support question (W0103). -/
  inDoc : Bool := false
  /-- Inside a definition body, the group a definition announced through
  `bodyNext`: what a construct there means is decided where the command is
  used, never where it is defined. The walk's `inBody` flag, as state, so
  an arm can read it. -/
  inDef : Bool := false
  /-- Replaying a `\begin{document}` hook body, whose content `seamSplit`
  routes to the body side: a construct there reaches the body although
  `inDoc` is false for the replay. -/
  seam : Bool := false
  /-- Inside a brace group of the walk: an argument (a `\title`, an
  `\author`, a running-head field, a definition body) or a scope of its
  own. A declaration there ends with the group, and its text is set
  wherever the group is set; only one outside every group stays in force
  until `\begin{document}`. -/
  inGroup : Bool := false
  /-- The walk is inside a list environment's body, where a list parameter
  assigned there spaces that one list (ltlists.dtx: `\list` runs the level's
  parameters, then the environment's own settings). -/
  inList : Bool := false
  /-- The rewrite is of a whole document — its stream holds the `document`
  environment — rather than of a value's text re-read on its own, whose top
  level is inline content (`preambleProper`). -/
  wholeDoc : Bool := false
  /-- The file the rewrite was asked for: a site in any other stands in an
  included file, and moves with that file's wrapper. -/
  docFile : String := ""
  /-- Counter commands the preamble's top level holds, in order, moved to
  where the body starts: what they set holds there (ltcounts.dtx). -/
  preCounters : Array Raw := #[]
  /-- The list levels whose parameter macro (`\@listi` …) the preamble
  redefined as parameter assignments, with where each was defined. -/
  listDefs : Array (Nat × Pos × Array TexAssign) := #[]
  /-- The document's `\normalsize` leaves `\@listi` as the preamble set it:
  a class's own does `\let\@listi\@listI` (size10.clo), and
  `\begin{document}` runs it, so a preamble `\@listi` stands only when a
  redefined `\normalsize` omits that. -/
  listiKept : Bool := false
  /-- The preamble's assignments to a parameter a list level sets again
  (`listReset`), with the spelling, file and site each was written at: what
  they reach is known only at the preamble's end. -/
  listResets : Array (String × String × String × Pos) := #[]
  /-- At the top level of a `tabular` body, where the elaborator's tabular
  arm reads every element itself: a `\multicolumn` there is its to set as a
  span, so the walk keeps the construct whole. A group or another
  environment inside the body hides it again. -/
  tableTop : Bool := false
  /-- At the top level of a definition body, the group a definition
  announced (`bodyNext`): a `\multicolumn` opening it opens the cell a use
  at a cell's head stands in. A group or an environment inside the body
  hides it again. -/
  defTop : Bool := false
  /-- The lengths as the preamble left them, taken where the document
  environment opens: what the list levels' styles, declarations of the
  preamble, are judged against. -/
  preLens : Option (Array (String × String)) := none
  /-- The text block's measure is one the elaborator can read in the
  preamble: false under a flow class (the default class included) until
  the page declares a measure (`margin`, `hmargin`, `textwidth`), since
  that class settles its text block after the preamble. -/
  measureKnown : Bool := false
  /-- The declared class's page model is the flow model (the default
  class's): its text block is the engine's, never the one LaTeX's class
  computed at load, so a preamble value naming the class's line width has
  no reading here. -/
  flowPage : Bool := true
  /-- Constructs already warned about: forty frames sharing one unsupported
  idiom are one problem, not forty. -/
  warned : Array String := #[]
  /-- Every control word the conditional pass has seen bound, with the
  parameterless value when one is readable: presence is what `\ifdefined`
  reads, the value what `\ifnum`, `\ifodd`, `\ifcase` and `\ifx` read, at
  the site that reads them. `none` is a name bound in a way no value can be
  read from — a parameter text, an expanding definer over unread names, a
  `\let` to a name with no readable value. Groups restore the meanings
  they opened with; only global definitions outlive them. -/
  binds : Std.HashMap String (Option CondVal) := {}
  /-- `\newif` flags by base name (`\newif\ifshowdetail` records
  `showdetail`, initially false — plain TeX's `\newif` sets `\iffalse`)
  with the value the last `\Xtrue`/`\Xfalse` gave. Scoped like a value. -/
  flags : Std.HashMap String Bool := {}
  /-- The save stack (tex.web §268): each change to `binds` and `flags`, with
  what it replaced, so the close of the group the change was made in
  undoes it. It holds only what changed, so a group costs what it binds. -/
  undo : Array CondUndo := #[]
  /-- Every global definition, in the order made (`\gdef`, `\xdef`,
  `\global`): what outlives the group it was made in. -/
  globals : Array (String × Option CondVal) := #[]
  /-- Live primitive group pairs; their save marks cross macro and input
  boundaries just as the tokens do. Brace groups restore this stack too. -/
  primitiveScopes : Array (String × CondMark) := #[]
  /-- The names the picture being walked binds for itself — a `\foreach`
  variable, a `\pgfmathsetmacro` target. pgf binds them in the picture's
  own scope, so a test that reads one is the picture's to evaluate. -/
  picBound : Array String := #[]
  /-- Definitions the conditional pass has recorded, the clock `CondVal.serial`
  reads. -/
  serial : Nat := 0
  macroClock : Nat := 0
  /-- Where the macro being expanded by the conditional pass is used: the
  site its decisions are named at, since that is where TeX makes them. -/
  useSite : Option Pos := none
  /-- The conditional pass is inside a picture: a document macro there is
  read at the picture's own site, so the pass puts the value in force there
  into the picture rather than leave the walk a table for the whole
  document. -/
  inPicture : Bool := false
  /-- A prepared title becomes inline content. Execute readable definitions
  without emitting their syntax, and expand local uses before its scope closes. -/
  materializeTitle : Bool := false
  /-- The document body has begun: a definition made from here on is read
  by the elaborator where it is made, not at the preamble's end. -/
  condInDoc : Bool := false
  /-- Collection has ended. A hook met during replay is read in place,
  with the existing placement diagnostic, never collected a second time. -/
  condReplaying : Bool := false
  /-- The opening `\ignorespaces` scan (latex.ltx, `\document`): expand
  readable commands and discard spaces until a nonexpandable token stands.
  This stops before compatibility can remove that token. -/
  ignoreSpaces : Bool := false
  /-- Preamble definitions whose live texts the elaborator may read itself,
  settled against the state at the preamble's end (`condSettle`). -/
  pending : Array CondPending := #[]
  /-- The macro whose definition is being settled, when it is: its
  decisions are named as the definition's, not a use's. -/
  settling : Option String := none
  /-- The conditional pass reads a spliced file's own top level, the list
  where a live `\endinput` ends the file. -/
  fileTop : Bool := false
  /-- The value source each length holds as the rewrite last set it
  (`\newlength`, `\setlength`, register arithmetic): what an `\advance` of
  it is evaluated from. -/
  lens : Array (String × String) := #[]
  /-- Token sites assigned directly in this scope. Their opening values
  are captured by the elaborator, where native declarations have resolved. -/
  localLengths : Array String := #[]
  /-- Command names the rewrite walk has bound so far, in document order:
  what `\providecommand` and `\ProvideDocumentCommand` read. Separate from
  `binds`, which the conditional pass fills for the whole document
  before any rewrite runs — a policy about "before this point" cannot
  read a whole-document set. -/
  bound : Array String := #[]
  /-- biblatex's declared resources (`\addbibresource`), preamble state the
  `\printbibliography` arm reads: the natbib door (`\bibliography`) takes
  its file where the list prints, biblatex names it where it is loaded. -/
  bibResources : Array String := #[]
  /-- The record name biblatex's style option mapped to, emitted as
  `\bibliographystyle` beside the `\bibliography` the print site
  synthesizes — the style is read anywhere before the list, and the
  preamble elaborator does not take it. -/
  bibStyle : Option String := none
  /-- hyperref's link colouring as its options have declared it so far. -/
  links : LinkSetup := {}
  /-- Names the caller declares the engine renders or reserves: what
  the provision definers' keep-existing policy reads for commands this
  document did not bind — every one of them *is* defined, in LaTeX and
  here, so a provide of one is LaTeX's documented no-op. -/
  provideKeeps : List String := []
  /-- State mutations performed through `write`, counted: with `diags.size`,
  what the dispatcher's silence guard reads (`account`, W0387) — a consumed
  construct either produced tokens, said something, or wrote state. The
  counter reads intent, not effect: an idempotent write (a header field set
  to what it already held) still counts as understood, which is why no
  `BEq St` is needed. Monotone: only `write` touches it, only upward. -/
  writes : Nat := 0
  /-- The boundary door as this document declares it: open (the default)
  unless a `\pictures{ tool = none }` refusal stands. Read once at
  `rewrite`'s entry (`boundaryRefused`); the `\usepackage` dispatch is the
  consumer — a picture package's load rides to the boundary only through
  an open door. -/
  boundaryOpen : Bool := true
  /-- Hook bodies collected by the one deferral pass, in declaration order
  with the point each replays at and the file it was declared in. LaTeX runs
  a hook's bodies in the order they were declared (ltfiles.dtx appends to the
  hook's token list), so the order here is the order they replay in. The file
  travels with the body because the replay happens in its own pass: what the
  engine refuses inside a `.sty`'s hook is still named at the `.sty`. -/
  deferred : Array (DeferPoint × String × Pos × Array Raw) := #[]
  /-- The loads the shared conditional walk has read so far (`condList`). -/
  loads : LoadSet := {}
  /-- Native spacers appended to the ordinary block-begin template in the
  preamble. Applied after rewriting, including to blocks in definitions
  made before the addition: beamer reads its template when a block opens. -/
  beamerBlockBegin : Array Raw := #[]
  /-- Local field definitions shared by native element styles and template
  font selection. A nonstarred declaration replaces only supplied fields;
  a starred declaration starts empty (`beamerbasefont.sty`). -/
  beamerFonts : Array (String × List (String × String)) := #[]
  /-- A global numbered footer is read at the document seam, after its font
  declarations. Keeping the last body also handles end-preamble hooks. -/
  beamerFootline : Option (String × Pos × Array Raw) := none
  /-- Preamble group primitives stay flat for the declaration reader.
  Save the same font and footer fields that brace groups restore. -/
  beamerScopes : List (String × Array (String × List (String × String)) ×
    Option (String × Pos × Array Raw)) := []
  /-- Successful captures, including local assignments whose values were
  restored. Only these justify removing an otherwise empty preamble group. -/
  beamerCaptures : Nat := 0

private abbrev M := StateM St

/-- The actual call offered to the driver's existing candidate and splice
readers. Its command is the request's command; operands stay parsed syntax. -/
@[expose] public def InputRequest.call (request : InputRequest) : Array Raw :=
  #[.ctrl request.command request.callPos] ++ request.operands

/-- The execution state at a file read. Only `resumeInput` can run a
fragment against it; the driver carries it without inspecting meanings. -/
public structure InputContext where
  private state : St

/-- Completed reads, including reads made while an answer was resumed.
An enclosing call is recorded after those nested reads return. -/
public def InputContext.inputAttempts (context : InputContext) : Array InputAttempt :=
  context.state.inputAttempts

/-- File effects cross the core boundary as requests and parsed answers.
The answer runs in the requesting context, so its definitions and flag
changes are visible to the caller's next token. `none` leaves the original
call for ordinary compatibility dispatch, as when no local style exists. -/
public abbrev InputReader (m : Type → Type) :=
  InputRequest → InputContext → m (Option (Array Raw) × InputContext)

/-- Accept the reader's answer without changing its syntax or diagnostic
state. The receipt records the exact call, after any reads inside it. -/
public def finishInput (request : InputRequest)
    (response : Option (Array Raw) × InputContext) :
    Option (Array Raw) × InputContext :=
  (response.1, { state := { response.2.state with
    inputAttempts := response.2.inputAttempts.push ⟨request, response.1.isSome⟩ } })

/-- The evaluator's file-effect door. Every recorded receipt is made here
from the request passed to the reader and the answer it actually returned. -/
public def dispatchInput [Monad m] (reader : InputReader m) (request : InputRequest)
    (context : InputContext) : m (Option (Array Raw) × InputContext) := do
  return finishInput request (← reader request context)

public theorem finishInput_answer_exact (request : InputRequest)
    (response : Option (Array Raw) × InputContext) :
    (finishInput request response).1 = response.1 := by rfl

public theorem finishInput_attempts_exact (request : InputRequest)
    (response : Option (Array Raw) × InputContext) :
    (finishInput request response).2.inputAttempts =
      response.2.inputAttempts.push ⟨request, response.1.isSome⟩ := by rfl

/-- The effectful production door calls the supplied reader exactly once.
There is no second candidate scan, replay or guessed answer in its receipt. -/
public theorem dispatchInput_reader_exact [Monad m] (reader : InputReader m)
    (request : InputRequest) (context : InputContext) :
    dispatchInput reader request context = (do
      let response ← reader request context
      pure (finishInput request response)) := by rfl

private abbrev EvalM (m : Type → Type) := StateT St m

private instance [Monad m] : MonadLift M (EvalM m) where
  monadLift act := fun st => pure (act st)

private theorem evalLift_id {α : Type} (act : M α) :
    (liftM act : EvalM Id α) = act := by rfl

private theorem state_array_forIn_empty {α β : Type} (init : β)
    (step : α → β → M (ForInStep β)) :
    (forIn (#[] : Array α) init step : M β) = pure init := by
  rw [← Array.forIn_toList]
  rfl

/-- The one door for a state mutation: `f`, then the `writes` bump the
dispatcher's silence guard reads. Every `modify`/`set` in this file outside
`say`/`write`/`account` is rejected by the pre-commit hook, so an arm
cannot mutate state invisibly to the guard. -/
private def write (f : St → St) : M Unit :=
  modify fun st => { f st with writes := st.writes + 1 }

private theorem write_eq (f : St → St) :
    write f = fun st => ((), { f st with writes := st.writes + 1 }) := by rfl

/-- Beamer's font and template definitions are local TeX assignments.
Input wrappers do not introduce a scope; groups and environments do. -/
private def closeBeamerScope (saved : St) (result : α × St) : α × St :=
  (result.1, (write fun st => { st with
    beamerFonts := saved.beamerFonts
    beamerFootline := saved.beamerFootline
    beamerScopes := saved.beamerScopes }) result.2 |>.2)

private def withBeamerScope (act : M α) : M α := fun st =>
  closeBeamerScope st (act st)

/-- `\begin{document}` runs `\normalsize`, which resets the size-owned
lengths. This is the state transition the document body really enters. -/
private def openDocumentBody : M Unit :=
  write fun st =>
    let lens := st.lens.filter fun e => !sizeReset e.1
    { st with inDoc := true, lens := lens, preLens := st.preLens.orElse fun _ => some lens }

private def closeDocumentBody (pos : Pos) (result : Array Raw × St) : Raw × St :=
  (.env "document" result.1 pos,
    (write fun st => { st with inDoc := false }) result.2 |>.2)

/-- The document environment's body call and return. Keeping that boundary
explicit lets a consumed control be followed through its actual enclosing
environment without unfolding unrelated environment interpreters. -/
private def rewriteDocumentBody (body : M (Array Raw)) (pos : Pos) : M Raw := fun st =>
  closeDocumentBody pos (body (openDocumentBody st).2)

/-- The TeX82 primitive control words — a closed, documented list (Knuth,
The TeXbook, Appendix I marks each primitive in its index; canonically the
`primitive` initialisations in tex.web). One half of the `texInternal`
boundary; the `@`-name convention is the other. -/
public def texPrimitives : Array String := #[
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
public def texInternal (name : String) : Bool :=
  name.contains '@' || texPrimitives.contains name

/-- Is this control word a LaTeX internal whose `{...}` arguments are code —
the names whose arguments package code drops (`Elab.recoverPackageCmd`)?
`@` is a letter only while a package or class file is read, or after
`\makeatletter`: latex.ltx's `\@onefilewithoptions` runs `\makeatletter`
before the load, and `\@pushfilename` saves the category code that
`\@popfilename` restores. A control word holding one is therefore the
kernel's or a package's own implementation, and the groups after it are its
operands: names, option lists, definition bodies, tests. The engine does not
run that code, and set as text it is code on the page. The one kind of
internal that sets an operand, the kernel's `\@firstofone` and its kin, is
the exception, and it is not read yet. The TeX82 primitives, `texInternal`'s
other half, are not in it: `\hbox`, `\uppercase` and `\discretionary` set
their groups. -/
public def codeInternal (name : String) : Bool :=
  name.contains '@'

/-- Is a site in `file` package code — a style or class file the document
loads — rather than the document's own text? The splice names every span of
a local `.sty` by its file (the input wrapper), and a hook such a file
registers replays inside that wrapper (`rewrite`), so the file a site stands
in is the boundary. A class file would be `.cls`; none is read today. -/
public def packageFile (file : String) : Bool :=
  file.endsWith ".sty" || file.endsWith ".cls"

/-- A refusal of `name` at a site in `file` demotes exactly when the site is
inside package code — the only door a `.sty` span enters by is the splice
(`\input` reads `.tex`) — and the name is a TeX internal. The author can act
on a per-line warning in their own files; in a venue's style file they
cannot, and N0020 already names that file once. -/
public def styInternal (file name : String) : Bool :=
  packageFile file && texInternal name

/-- Attribute a diagnostic by its source site, preserving an explicit trigger. -/
public def SourceTriggers.atSource (sources : SourceTriggers) (file : String)
    (pos : Pos) (d : Diag) : Diag :=
  { d with trigger := d.trigger.orElse fun _ => sources.writtenAt file pos }

/-- Immediate attribution has the same failed-mapping boundary as delayed
attribution: an unavailable original coordinate leaves the record untouched. -/
public theorem SourceTriggers.atSource_unmapped_id (sources : SourceTriggers) (file : String)
    (pos : Pos) (d : Diag) (h : pos.sourceMapped = false) :
    sources.atSource file pos d = d := by
  simp [SourceTriggers.atSource, SourceTriggers.writtenAt, h]

private def atSource (st : St) (pos : Pos) (d : Diag) : Diag :=
  st.sourceTriggers.atSource st.file pos d

/-- Source attribution changes only the trigger, for every diagnostic;
the loss, acceptance policy, census and output scope retain their record. -/
public theorem atSource_record_exact (sources : SourceTriggers) (file : String)
    (pos : Pos) (d : Diag) :
    { sources.atSource file pos d with trigger := d.trigger } = d := by rfl

/-- The one door a diagnostic lands through here: a push, never a write —
the silence guard reads `diags.size` growth on its own. `subject` is the
census key of the loss, so "this loss is named" stays a lookup and
`Diag.tallySites` can count its sites. -/
private def say (code : DiagCode) (msg : String) (pos : Pos) (help : Option String := none)
    (demote : Bool := false) (subject : Option String := none)
    (refused : Option String := none) : M Unit :=
  modify fun st => { st with
    diags := st.diags.push (
      let d := atSource st pos (Diag.of code msg (some ⟨st.file, pos⟩) help subject refused)
      if demote then d.demote else d) }

/-- Keys are namespaced (`ctrl:`, `spec:`, `beamer:`), never bare names: the
catch-all `beamer:` key set grows with `beamerConfig`, and a flat space would
let a future entry claim a literal arm's key and silence it.

Once per construct, counted per site: the first occurrence carries the
message and the help, every later one rides beside it as a note with the
same code, the same words and the same structured `subject`, and
`Diag.tallySites` puts the total on the visible line. The suppression that
used to happen here spent one key for every site of a construct, so a
document losing a macro at twenty-nine places reported one. -/
private def sayOnce (key : String) (code : DiagCode) (msg : String) (pos : Pos)
    (help : Option String := none) (demote : Bool := false) : M Unit := do
  let first := !(← get).warned.contains key
  if first then
    write fun st => { st with warned := st.warned.push key }
  else
    -- The repeat is accounted as a write too, so the silence guard (W0387)
    -- does not re-name per repeat what once-per-construct says once.
    write id
  say code msg pos (if first then help else none) (demote || !first) (subject := some key)

/-- The one line a `\multicolumn` that does not open a tabular cell prints,
from either door that meets one (this walk, the tabular arm): every shape
loses the same thing. -/
public def multicolumnMisplaced : String :=
  "'\\multicolumn' opens no tabular cell here: its text stays in place, without its \
span or alignment"

public def multicolumnMisplacedHelp : String :=
  "write \\multicolumn first in a tabular cell"

/-- Every translation is one note in the same shape, so `-v` reads as a list
of things the document could say directly. -/
private def became (what native : String) (pos : Pos)
    (subject : Option String := none) : M Unit :=
  say .N0100 s!"'{what}' → {native}" pos (subject := subject)

/-- A construct that reads to nothing: the translation note, whose target is
no effect with its reason, keyed `ctrl:nothing:<key>`. The key is what keeps
a discard from reading as a translation onto a native construct — `became`
carries no subject by default, so the two were one shape to every consumer
that reads `Diag.subject`. `key` is the control word, sub-keyed by the
argument that decided the discard where one did (`usepackage:url`,
`providecommand:x`), or else by the argument its message names
(`selectlanguage:french`), so every site of one key reads one message and
`Diag.tallySites` counts the sites of one discard and never lumps two. -/
private def discard (what why key : String) (pos : Pos) : M Unit :=
  became what s!"nothing: {why}" pos (subject := some ("ctrl:nothing:" ++ key))

/-- Log controls' accounting reads their descriptor, never their arguments. -/
private def meaningFreeReport (name : String) (pos : Pos) (note : Option String) : M Unit :=
  match note with
  | some why => discard s!"\\{name}" why name pos
  | none => pure ()

private def configSkipReport (name : String) (pos : Pos)
    (msg : String) (help : Option String) : M Unit :=
  sayOnce ("ctrl:" ++ name) .W0104 msg pos (help := help)

/-- The preamble proper: the preamble's top level. That is outside the
document environment, outside a `\begin{document}` hook's replay (routed to
the body), and outside every brace group of the walk — a definition body,
read where the command is used, and any argument, which is set where its
command sets it: a `\title` at `\maketitle`, a running-head field on its
pages. Only there does a declaration stay in force until
`\begin{document}` with no text set under it, and `\begin{document}`
resets the font series and babel's language (measured against lualatex),
so an arm that would declare one there discards it instead. Inside a group
the construct keeps its body meaning, as lualatex gives it in the title,
the author, the date and a running head. -/
private def preambleProper : M Bool := do
  let st ← get
  return !st.inDoc && !st.inDef && !st.seam && !st.inGroup

/-- The preamble proper of a whole document. A value's text re-read on its
own (a style's font template, a KOMA font argument) is inline content at its
top level, never a preamble, so what LaTeX's `\begin{document}` resets —
the size a `\large` there declares — is discarded only here. -/
private def docPreamble : M Bool := do
  return (← get).wholeDoc && (← preambleProper)

/-- The top-level brace groups of a feature value:
`{l}{n}{*-Light}` → `#["l", "n", "*-Light"]`. Text outside any group is
dropped; unbalanced closers saturate at depth zero. -/
private def braceGroups (s : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur : Array Char := #[]
  let mut depth := 0
  for c in s.toList do
    if c == '{' then
      if depth != 0 then cur := cur.push c
      depth := depth + 1
    else if c == '}' then
      depth := depth - 1
      if depth == 0 then
        out := out.push (String.ofList cur.toList)
        cur := #[]
      else if depth != 0 then
        cur := cur.push c
    else if depth != 0 then
      cur := cur.push c
  return out

/-- `size` and `size*` assign the same beamer field. -/
private def beamerFontAxis (key : String) : String :=
  if key == "size*" then "size" else key

/-- Keep empty values: they clear one field. Split only outer commas, and
remove a whole value's bracing without stripping `size*`'s operands. -/
private def beamerFontUpdate (old : List (String × String)) (src : String) :
    List (String × String) := Id.run do
  let mut fields := old
  for entry in Decl.splitEntries src do
    match entry.splitOn "=" with
    | key :: value :: rest =>
      let key := key.trimAscii.toString
      let value := (String.intercalate "=" (value :: rest)).trimAscii.toString
      let value := if key != "size*" then
          match (braceGroups value).toList with
          | [inner] => if value == "{" ++ inner ++ "}" then inner.trimAscii.toString else value
          | _ => value
        else value
      fields := (key, value) :: fields.filter (fun e => beamerFontAxis e.1 != beamerFontAxis key)
    | _ => pure ()
  return fields

/-- Native font commands select the stored fields in beamer's order. -/
private def beamerFontCommands (fields : List (String × String)) : String :=
  String.join (beamerFontKeys.map fun axis =>
    match fields.find? (fun e => beamerFontAxis e.1 == axis) with
    | some ("size*", value) =>
      let gs := braceGroups value
      if gs.size == 2 then s!"\\fontsize\{{gs[0]!}}\{{gs[1]!}}\\selectfont" else ""
    | some (_, value) => value
    | none => "")

/-- The title-template reader carries measured size and leading separately.
The other axes use the same selection order as native element styles. -/
private def beamerTemplateFont (element : String) (fields : List (String × String)) :
    TitleTemplate.Font := Id.run do
  let mut font : TitleTemplate.Font :=
    { cmds := beamerFontCommands (fields.filter fun e => beamerFontAxis e.1 != "size") }
  match fields.find? (fun e => beamerFontAxis e.1 == "size") with
  | some ("size*", value) =>
    let gs := braceGroups value
    font := { font with size := gs[0]?, leading := gs[1]? }
    if gs.size < 2 then
      font := { font with unread := font.unread.push s!"'size*' of '{element}'" }
    if gs.size > 2 then
      font := { font with unread := font.unread.push s!"extra size fields of '{element}'" }
  | some (_, value) =>
    let name := if value.startsWith "\\" then (value.drop 1).toString else value
    match TitleTemplate.beamerSizes.lookup name with
    | some (size, leading) => font := { font with size := some size, leading := some leading }
    | none => font := { font with cmds := value ++ font.cmds }
  | none => pure ()
  for (key, _) in fields do
    unless beamerFontKeys.contains (beamerFontAxis key) do
      font := { font with unread := font.unread.push s!"'{key}' of '{element}'" }
  return font

/-- One `FontFace = {series}{shape}{font}` entry, validated: the native
`slot.<series>[.italic] = "face"` part it becomes, or `none` after a
warning naming exactly what could not be honoured — a shape off the
upright/italic model, a feature list in place of a name, a value that is
no series. The slanted shape sets italic, the substitution NFSS itself
makes when a face has no slanted shape; a width half is honoured for its
weight and named for its width, as `\fontseries`'s is. -/
private def fontFacePart (family slot v : String) (pos : Pos) :
    M (Option String) := do
  match (braceGroups v).toList with
  | [code, shape, f] =>
    match Ir.Weight.parseSeries code.trimAscii.toString,
        shape.trimAscii.toString with
    | some (w, width), sh =>
      let ital := sh == "it" || sh == "sl"
      if !(sh == "n" || ital) then
        sayOnce ("fontface:shape:" ++ sh) .W0104
          s!"'FontFace' names the '{sh}' shape; the face model \
carries upright and italic only, so this declaration is skipped" pos
        return none
      if f.contains '=' then
        sayOnce "fontface:features" .W0104
          s!"'FontFace = \{{code}}\{{sh}}...' gives a feature list \
in place of a font name; only named faces are read, so this declaration \
is skipped" pos
        return none
      if !width.isEmpty then
        sayOnce ("fontface:width:" ++ width) .W0104
          s!"'FontFace = \{{code}}...' also asks for the \
'{width}' width; there is no width axis, so only the weight is honoured" pos
      -- fontspec's `*` stands for the family name, as in `UprightFont`.
      let f := if f.startsWith "*" then family ++ (f.drop 1).toString else f
      let ext := if ital then ".italic" else ""
      return some s!"{slot}.{w.series}{ext} = \"{f}\""
    | none, _ =>
      sayOnce ("fontface:series:" ++ code) .W0104
        s!"'FontFace = \{{code}}...' names no NFSS series; \
this declaration is skipped" pos
      return none
  | _ =>
    sayOnce "fontface:form" .W0104
      "'FontFace' is read as {series}{shape}{font name}; \
another form is skipped" pos
    return none

private def synth (s : String) : M (Array Raw) := do
  let file := (← get).file
  return (Parse.parse file (Lex.lex file s).1).1

mutual

/-- Relocate token sites without changing their spelling. Group delimiters
can retain the distinct identities that `condPatchRaw` matches; they emit
no compatibility diagnostic. An input wrapper owns another file's sites. -/
public def rebase (mapPos : Pos → Pos) (groups : Bool) : Raw → Raw
  | .word s p => .word s (mapPos p)
  | .space => .space
  | .par p => .par (mapPos p)
  | .ctrl n p => .ctrl n (mapPos p)
  | .sym c p => .sym c (mapPos p)
  | .group body p =>
    .group (rebaseList mapPos groups body.toList).toArray (if groups then mapPos p else p)
  | .math d body p => .math d (rebaseList mapPos groups body.toList).toArray (mapPos p)
  | .env n body p => .env n
      (if (Parse.inputEnvFile? n).isSome then body else (rebaseList mapPos groups body.toList).toArray)
      (mapPos p)
  | .verb env s p => .verb env s (mapPos p)

private def rebaseList (mapPos : Pos → Pos) (groups : Bool) : List Raw → List Raw
  | [] => []
  | r :: rest => rebase mapPos groups r :: rebaseList mapPos groups rest

end

mutual

private theorem rebaseArray_source (mapPos : Pos → Pos) (groups : Bool) (raws : Array Raw) :
    rawSrc (rebaseList mapPos groups raws.toList).toArray = rawSrc raws := by
  simp only [rawSrc]
  rw [rebaseList_source]

private theorem rebaseList_source (mapPos : Pos → Pos) (groups : Bool) (rs : List Raw) :
    rawSrcList (rebaseList mapPos groups rs) = rawSrcList rs := by
  cases rs with
  | nil => rfl
  | cons r rest =>
    simp only [rebaseList, rawSrcList]
    rw [rebase_source, rebaseList_source]

/-- Source relocation preserves every token's spelling and boundary,
including nested groups, math and file wrappers. -/
private theorem rebase_source (mapPos : Pos → Pos) (groups : Bool) (r : Raw) :
    rawSrcOne (rebase mapPos groups r) = rawSrcOne r := by
  cases r with
  | env n body p =>
    simp only [rebase]
    split <;> simp only [rawSrcOne, rebaseArray_source]
  | _ => simp only [rebase, rawSrcOne, rebaseArray_source]

end

/-- Source relocation preserves the written token spelling, including nested
groups and file wrappers. The relocation implementation stays opaque. -/
public theorem rebase_source_exact (mapPos : Pos → Pos) (groups : Bool) (r : Raw) :
    rawSrcOne (rebase mapPos groups r) = rawSrcOne r :=
  rebase_source mapPos groups r

private def synthAt (s : String) (pos : Pos) : M (Array Raw) := do
  return (← synth s).map (rebase (fun _ => pos) true)

mutual

-- conserves: none — a surface token comparison key, not an IR rewrite.
/-- Replacement-token identity for `\ifx` (TeXbook chapter 20). Positions
and word chunk boundaries are parser details; spaces and groups are tokens.
A blank line is the control sequence `\par`, also when written explicitly.
Keep this key separate from source printing, which trims whitespace. -/
private def macroTokens (out : Array Raw) : List Raw → Array Raw
  | [] => out
  | .word s _ :: rest =>
    macroTokens (s.toList.foldl
      (fun acc c => acc.push (.word (String.singleton c) {})) out) rest
  | r :: rest => macroTokens (out.push (macroToken r)) rest

private def macroToken : Raw → Raw
  | .word s _ => .word s {}
  | .space => .space
  | .par _ => .ctrl "par" {}
  | .ctrl n _ => .ctrl n {}
  | .sym c _ => .sym c {}
  | .group body _ => .group (macroTokens #[] body.toList) {}
  | .math d body _ => .math d (macroTokens #[] body.toList) {}
  | .env n body _ => .env n (macroTokens #[] body.toList) {}
  | .verb env s _ => .verb env s {}

end

/-- One optional `[...]` argument, keeping its tokens inert. Groups are
opaque to the delimiter scan; an ungrouped `[` does not nest (latex.ltx,
`\@ifnextchar` and `\@argdef`). -/
private def takeRawOpt (raws : Array Raw) (i : Nat) : Option (Array Raw) × Nat := Id.run do
  let j := skipSpaces raws i
  match raws[j]? with
  | some (.sym '[' _) =>
    let mut k := j + 1
    let mut inner : Array Raw := #[]
    for _ in [k:raws.size + 1] do
      match raws[k]? with
      | some (.sym ']' _) => return (some inner, k + 1)
      | some r => inner := inner.push r; k := k + 1
      | none => break
    return (none, i)
  | _ => (none, i)

/-- One optional `[...]` argument, as source text for configuration keys. -/
public def takeOpt (raws : Array Raw) (i : Nat) : Option String × Nat :=
  let (arg, stop) := takeRawOpt raws i
  (arg.map rawSrc, stop)

/-- TeX removes one enclosing group from a delimited argument, exactly
when that group is the whole argument (TeXbook chapter 20). LaTeX reads a
default this way at definition time, then passes it intact on omission. -/
private def ungroupArg (raws : Array Raw) : Array Raw :=
  match raws.toList with
  | [.group body _] => body
  | _ => raws

/-- Up to `n` optional `[...]` runs, and whether any of them was there. The
box commands differ only in how many their signature allows, so the count is
a number read from `boxShape` rather than a repeated call per arm. -/
private def takeOpts (raws : Array Raw) (i n : Nat) : Bool × Nat := Id.run do
  let mut j := i
  let mut any := false
  for _ in [0:n] do
    let (o, j') := takeOpt raws j
    if o.isSome then any := true
    j := j'
  return (any, j)

/-- Consecutive arguments in the raw source, with whitespace skipped only
before an argument. Contents are arbitrary and never inspected. This is a
progress contract: each constructor consumes one argument, and its endpoint
is the next raw index, not a count of loop iterations. -/
public inductive GroupPrefix (raws : Array Raw) : Nat → List (Array Raw) → Nat → Prop
  | nil {i} : GroupPrefix raws i [] i
  | group {i body p args stop} :
      raws[skipSpaces raws i]? = some (.group body p) →
      GroupPrefix raws (skipSpaces raws i + 1) args stop →
      GroupPrefix raws i (body :: args) stop
  | ctrl {i name p args stop} :
      raws[skipSpaces raws i]? = some (.ctrl name p) →
      GroupPrefix raws (skipSpaces raws i + 1) args stop →
      GroupPrefix raws i (#[.ctrl name p] :: args) stop

/-- The argument loop's step, exposed for its progress proof. The equation
`takeGroups_loop_exact` checks that this reads the actual loop, including its
early exit; the implementation is not restated as a fold. -/
private def takeGroupsStep (raws : Array Raw) (s : Array (Array Raw) × Nat) :
    Id (ForInStep (Array (Array Raw) × Nat)) :=
  let k := skipSpaces raws s.2
  match raws[k]? with
  | some (.group body _) => pure (.yield (s.1.push body, k + 1))
  | some (r@(.ctrl _ _)) => pure (.yield (s.1.push #[r], k + 1))
  | _ => pure (.done s)

/-- Up to `n` brace groups or bare control words (`\newcommand\x`).
Other raws stop the reader without consuming them or their leading spaces.
Character-token arguments use `takeRawArgs` instead. -/
public def takeGroups (raws : Array Raw) (i n : Nat) : Array (Array Raw) × Nat := Id.run do
  let mut out : Array (Array Raw) := #[]
  let mut j := i
  for _ in [0:n] do
    let k := skipSpaces raws j
    match raws[k]? with
    | some (.group body _) => out := out.push body; j := k + 1
    | some (r@(.ctrl _ _)) => out := out.push #[r]; j := k + 1
    | _ => break
  return (out, j)

/-- Filename read from the same executed call the local-style reader sees. -/
@[expose] public def InputRequest.name (request : InputRequest) : String :=
  rawSrc ((takeGroups request.call (takeOpt request.call 1).2 1).1.getD 0 #[])

/-- Options read from the same executed call as the filename. -/
@[expose] public def InputRequest.options (request : InputRequest) : String :=
  ((takeOpt request.call 1).1.getD "").trimAscii.toString

/-- The scalar loading calls in one executed request, in source order.
Duplicates are retained: the admission gate, not a candidate scan, decides
whether their bodies run. Options and positions remain parsed syntax. -/
public def InputRequest.packageCalls (request : InputRequest) :
    Array (String × Array Raw) :=
  if request.command == "usepackage" || request.command == "RequirePackage" then
    let head := request.call.extract 0 (takeOpt request.call 1).2
    ((request.name.splitOn ",").map (·.trimAscii.toString)).toArray.map fun name =>
      (name, head.push (.group #[.word name request.pos] request.pos))
  else if let some pre := themeAsking.lookup request.command then
    #[(pre ++ request.name.trimAscii.toString, request.call)]
  else #[]

private theorem takeGroups_loop_exact (raws : Array Raw) (i n : Nat) :
    takeGroups raws i n = (forIn [0:n] (#[], i) (fun _ => takeGroupsStep raws)).run := by rfl

private theorem GroupPrefix.yields {raws : Array Raw} {i args stop}
    (h : GroupPrefix raws i args stop) (out : Array (Array Raw)) :
    Loop.Yields (takeGroupsStep raws) (out, i) args.length (out ++ args.toArray, stop) := by
  induction h generalizing out with
  | nil => simpa using (Loop.Yields.nil (a := (out, _)) (step := takeGroupsStep raws))
  | @group i body p args stop h _ ih =>
    apply Loop.Yields.cons (b := (out.push body, skipSpaces raws i + 1))
    · simp [takeGroupsStep, h]
    · simpa using ih (out.push body)
  | @ctrl i name p args stop h _ ih =>
    apply Loop.Yields.cons (b := (out.push #[.ctrl name p], skipSpaces raws i + 1))
    · simp [takeGroupsStep, h]
    · simpa using ih (out.push #[.ctrl name p])

/-- The actual loop consumes exactly the declared number of consecutive
arguments, for arbitrary source contents, starting index and suffix. The
premise describes source raws, not the result of the reader under proof. -/
public theorem takeGroups_prefix_exact {raws : Array Raw} {i args stop}
    (h : GroupPrefix raws i args stop) :
    takeGroups raws i args.length = (args.toArray, stop) := by
  rw [takeGroups_loop_exact, Std.Legacy.Range.forIn_eq_forIn_range']
  simpa using Loop.forIn_yields_exact (h.yields #[])
    (List.range' 0 args.length) (by simp)

/-- When a non-argument follows a shorter prefix, breaking leaves the
cursor before that boundary's whitespace and preserves every remaining raw.
This covers arbitrary budgets, including malformed and truncated input. -/
public theorem takeGroups_stopped_exact {raws : Array Raw} {i args stop n}
    (h : GroupPrefix raws i args stop) (hn : args.length < n)
    (hstop : ∀ body p, raws[skipSpaces raws stop]? ≠ some (.group body p))
    (hctrl : ∀ name p, raws[skipSpaces raws stop]? ≠ some (.ctrl name p)) :
    takeGroups raws i n = (args.toArray, stop) := by
  have hs : (takeGroupsStep raws (args.toArray, stop)).run =
      .done (args.toArray, stop) := by
    simp [takeGroupsStep]
  have hy := h.yields #[]
  simp only [Array.empty_append] at hy
  have hd := hy.stops (Loop.Stops.done hs)
  rw [takeGroups_loop_exact]
  exact Loop.forIn_range_stops_exact hd n (by omega)

/-- Undelimited TeX arguments: a group or one token each. A lexer word
can hold several character arguments. The index owns that whole word and
the caller receives its unconsumed tail. Hooks and live macro calls share
this boundary. -/
private def takeRawArgs (raws : Array Raw) (i count : Nat) :
    Array (Array Raw) × Nat × Array Raw := Id.run do
  let mut args : Array (Array Raw) := #[]
  let mut j := i
  let mut tail : Array Raw := #[]
  for _ in [0:count] do
    if args.size == count then break
    let k := skipSpaces raws j
    match raws[k]? with
    | some (.group body _) => args := args.push body; j := k + 1
    | some (.word s p) =>
      let cs := s.toList
      let n := min (count - args.size) cs.length
      let mut pos := p
      for c in cs.take n do
        args := args.push #[.word c.toString pos]
        pos := pos.next false
      let rest := String.ofList (cs.drop n)
      if !rest.isEmpty then tail := #[.word rest pos]
      j := k + 1
    | some (r@(.ctrl _ _)) | some (r@(.sym _ _)) | some (r@(.par _)) =>
      args := args.push #[r]; j := k + 1
    | _ => break
  return (args, j, tail)

/-- etoolbox's `\apptocmd` reads four arguments through the shared reader. -/
private def takeHookArgs (raws : Array Raw) (i : Nat) :
    Array (Array Raw) × Nat × Array Raw :=
  takeRawArgs raws i 4

/-- The canonical undelimited parameter text `#1` through `#9`
(TeXbook chapter 20), shared by value reading and translation. Spaces
inside this text are delimiters; the lexer already discards the space
that merely ends a control word. -/
private def undelimitedArity (params : Array Raw) : Option Nat :=
  read params.toList 0
where
  read : List Raw → Nat → Option Nat
    | [], n => some n
    | .sym '#' _ :: .word w _ :: rest, n =>
      if n < 9 && w == toString (n + 1) then read rest (n + 1) else none
    | _, _ => none

mutual

-- conserves: none — substitutes arguments for parameter tokens, preserving
-- the surrounding surface structure; this is not an IR rewrite.
/-- Bind parameters before executing replacement text. `#10` is argument
one followed by `0`; `##` quotes one parameter token for a nested
definition (TeXbook chapter 20). Substituted arguments are not scanned
again by this binding, and verbatim text is opaque. -/
private def bindRawArgsList (args : Array (Array Raw)) (out : Array Raw) :
    List Raw → Array Raw
  | [] => out
  | .sym '#' p :: .sym '#' _ :: rest =>
    bindRawArgsList args (out.push (.sym '#' p)) rest
  | .sym '#' p :: .word w q :: rest =>
    match w.toList with
    | c :: cs =>
      if c >= '1' && c <= '9' then
        match args[c.toNat - '1'.toNat]? with
        | some body =>
          let out := out ++ body
          let out := if cs.isEmpty then out
            else out.push (.word (String.ofList cs) (q.next false))
          bindRawArgsList args out rest
        | none => bindRawArgsList args ((out.push (.sym '#' p)).push (.word w q)) rest
      else bindRawArgsList args ((out.push (.sym '#' p)).push (.word w q)) rest
    | [] => bindRawArgsList args ((out.push (.sym '#' p)).push (.word w q)) rest
  | r :: rest => bindRawArgsList args (out.push (bindRawArgsRaw args r)) rest

private def bindRawArgsRaw (args : Array (Array Raw)) : Raw → Raw
  | .group body p => .group (bindRawArgsList args #[] body.toList) p
  | .env n body p => .env n (bindRawArgsList args #[] body.toList) p
  | .math d body p => .math d (bindRawArgsList args #[] body.toList) p
  | .word w p => .word w p
  | .space => .space
  | .par p => .par p
  | .ctrl n p => .ctrl n p
  | .sym c p => .sym c p
  | .verb e s p => .verb e s p

end

/-- `\tikz`'s one-command form from `i`: the raws up to and including the
first `;` a top-level word carries — where TikZ's path parser ends the
command (pgfmanual §12.2.2) — with the rest of that word handed back as
text, and the index after it. Nothing when no `;` closes the command before
the paragraph ends: the form is then not one this reader can bound. -/
private def tikzCommand (raws : Array Raw) (i : Nat) : Option (Array Raw × Array Raw × Nat) := Id.run do
  let mut out : Array Raw := #[]
  for k in [i:raws.size] do
    match raws[k]? with
    | some (.word s p) =>
      match s.splitOn ";" with
      | before :: after :: more =>
        let rest := String.intercalate ";" (after :: more)
        return some (out.push (.word (before ++ ";") p),
          if rest.isEmpty then #[] else #[.word rest p], k + 1)
      | _ => out := out.push (.word s p)
    | some (.par _) => return none
    | some r => out := out.push r
    | none => return none
  return none

/-- A saved native meaning carries a reserved control name through macro
execution. Decoding happens only at native dispatch, after document-name
lookup: TeX's \let copies the meaning, so a later definition of the source
name cannot change it (TeXbook ch. 20). A control word cannot contain a space. -/
public def overlayName (name : String) : String :=
  if name.startsWith "overlay native " then (name.drop "overlay native ".length).toString
  else name

private def overlayNativeName (name : String) : String :=
  let native := overlayName name
  "overlay native " ++ native

private def overlayTitled (name : String) : Bool :=
  ["block", "alertblock", "exampleblock"].contains name

/-- The numbered-selector surface shared by compatibility and elaboration.
`args` counts ordinary arguments before the last selector slot. Zero means
prefix-only. Beamer's font wrappers, colour declarations and uncover/visible
have only that slot; only/alt and newcommand<> wrappers also have a final
slot (beamerbaseoverlay.sty, only/alt and beamer@parseargs). -/
private def overlayArity? (name : String) : Option (Nat × Bool) :=
  let name := overlayName name
  if ["alert", "emph", "titled overlay"].contains name then some (1, true)
  else if ["hyperlink", "hypertarget"].contains name then some (2, true)
  else if name == "only" then some (1, false)
  else if name == "alt" then some (2, false)
  else if ["uncover", "visible", "onslide", "item", "textcolor", "color",
      "textrm", "textsf", "texttt", "textmd", "textbf", "textup", "textit",
      "textsl", "textsc", "textnormal", "underline", "uline", "sout"].contains name
    then some (0, false)
  else none

/-- A closed selector consumes whole raws through `stop`; a suffix of its
last word remains caller text in `tail`. Only whitespace is normalized here:
Ir.overlayRange remains the sole numbered-membership parser, and unsupported
mode, relative and action spellings still reach its W0105 caller. -/
private structure OverlaySelector where
  word : Raw
  stop : Nat
  tail : Array Raw := #[]

/-- Read `<...>` across lexer and substituted-argument fragments. Beamer's
master decoder expands fragments and removes spaces (beamerbasedecode.sty,
beamer@masterdecode); no argument group or paragraph can be consumed here.
Before an ordinary argument, newcommand<> accepts repeated selectors and the
last one wins (beamer@foundspec). `many` reads that slot without consuming any
text after its last complete selector. -/
private def overlaySelector? (raws : Array Raw) (start : Nat)
    (many : Bool := false) : Option OverlaySelector := Id.run do
  let some (.word first pos) := raws[start]? | return none
  unless first.startsWith "<" do return none
  let mut text := ""
  let mut selectorPos := pos
  let mut opened := true
  let mut selected : Option OverlaySelector := none
  for k in [start:raws.size] do
    match raws[k]? with
    | some (.word s p) =>
      for (c, ci) in s.toList.zipIdx do
        if !opened then
          if c == '<' then
            text := "<"
            selectorPos := { p with col := p.col + ci }
            opened := true
          else if !c.isWhitespace then return selected
        else
          text := text.push c
          if c == '>' then
            let tail := (s.drop (ci + 1)).toString
            selected := some {
              word := .word (String.ofList (text.toList.filter (!·.isWhitespace))) selectorPos
              stop := k + 1
              tail := if tail.isEmpty then #[] else
                #[.word tail { p with col := p.col + ci + 1 }] }
            if !many then return selected
            opened := false
    | some .space => pure ()
    | some (.ctrl n _) =>
      if opened then
        text := text ++ "\\" ++ n
      else return selected
    | some (.sym '#' _) => return selected -- an unbound definer parameter is not a selector yet
    | some (.sym c _) =>
      if opened then text := text.push c else return selected
    | _ => return selected
  return selected

/-- Read the canonical word produced by overlaySelector?, including refused
selectors. Recognizing the boundary never certifies numbered membership. -/
public def overlayWord? : Raw → Option String
  | .word w _ => if w.startsWith "<" && w.endsWith ">" then some w else none
  | _ => none

private structure OverlayWindow where
  name : String
  head : Nat
  left : Nat
  middle : Bool
  passed : Bool := false
  selected : Bool := false
  labelDepth : Nat := 0
  labelDone : Bool := false

private def OverlayWindow.accepts (w : OverlayWindow) : Bool :=
  w.labelDepth == 0 && (!w.passed || w.left == 0 || w.middle)

/-- Only newcommand<> continues looking after a selector, until its ordinary
arguments end. Only/alt and prefix-only wrappers finish at their first one. -/
private def OverlayWindow.afterSelector (w : OverlayWindow) : Option OverlayWindow :=
  if w.middle && w.left > 0 then some { w with selected := true } else none


/-- Item labels have a second selector slot after the bracketed label
(beamer@itemreverse). Label text is opaque to this window, including nested
brackets; selectors inside its groups still use their own native windows. -/
private def overlayNext (pending : Option OverlayWindow) (r : Raw)
    (head : Nat) : Option OverlayWindow :=
  if let some w := pending then
    if w.labelDepth > 0 then
      some { w with labelDepth := match r with
        | .sym '[' _ => w.labelDepth + 1
        | .sym ']' _ => w.labelDepth - 1
        | _ => w.labelDepth }
    else if w.name == "item" && !w.labelDone && (r matches .sym '[' _) then
      some { w with labelDepth := 1, labelDone := true }
    else advance
  else advance
where
  advance := match r with
    | .ctrl n _ => (overlayArity? n).map fun (arity, middle) =>
        { name := overlayName n, head, left := arity, middle }
    | .space => pending.filter fun w => !w.passed || w.left > 0 || w.name == "item"
    | .group _ _ => pending.bind fun w =>
        if w.left == 0 then none else some { w with left := w.left - 1, passed := true }
    | .word "" _ => pending
    | _ => none

private def overlayVariantName (w : OverlayWindow) (text : String) : Option String :=
  if w.name == "onslide" && !w.passed then
    if text.startsWith "*" then some "only"
    else if text.startsWith "+" then some "visible"
    else none
  else none

/-- Beamer routes onslide* to only, and onslide+ to visible. Both visible
and the ordinary onslide retain this engine's declared dim-cover policy.
The sign is outside the selector; <+> itself remains relative and refused. -/
private def overlayVariant (pending : Option OverlayWindow) (acc : Array Raw)
    (r : Raw) : Option OverlayWindow × Array Raw × Raw :=
  match pending, r with
  | some w, .word text p =>
    if let some name := overlayVariantName w text then
      let (name, pos) := match acc[w.head]? with
        | some (.ctrl n q) => (if n == overlayName n then name else overlayNativeName name, q)
        | _ => (name, p)
      let acc := acc.set! w.head (.ctrl name pos)
      let next := overlayNext none (.ctrl name pos) w.head
      (next, acc, .word (text.drop 1).toString { p with col := p.col + 1 })
    else (pending, acc, r)
  | _, _ => (pending, acc, r)

mutual

/-- Normalize only advertised selector slots, after macro execution. Moving
an accepted final selector to the head lets every spelling share its native
handler. A final selector is adjacent, as beamer@ifnextcharospec requires. -/
-- conserves: none — a surface boundary walk; no IR content has been elaborated.
private def overlayInputsList (raws : Array Raw) (pending : Option OverlayWindow)
    (acc : Array Raw) : List Raw → Nat → Nat → Array Raw
  | [], _, _ => acc
  | _ :: rest, i, skip + 1 => overlayInputsList raws pending acc rest (i + 1) skip
  | r :: rest, i, 0 =>
    let (pending, acc, r) := overlayVariant pending acc (overlayInputsRaw r)
    let selected := pending.filter (·.accepts) |>.bind fun w =>
      overlaySelector? (raws.set! i r) i (w.middle && w.left > 0)
    match selected, pending with
    | some s, some w =>
      let acc := (acc.extract 0 (w.head + 1)).push s.word ++
        acc.extract (w.head + 1 + if w.selected then 1 else 0) acc.size ++ s.tail
      let pending := if s.tail.isEmpty then w.afterSelector else none
      overlayInputsList raws pending acc rest (i + 1) (s.stop - (i + 1))
    | _, _ =>
      let next := overlayNext pending r acc.size
      overlayInputsList raws next (acc.push r) rest (i + 1) 0

private def overlayInputsRaw : Raw → Raw
  | .group body p => .group (overlayInputsList body none #[] body.toList 0 0) p
  | .env n body p =>
    if overlayTitled n then
      let head := Raw.ctrl "titled overlay" p
      let rs := overlayInputsList body (overlayNext none head 0) #[head] body.toList 0 0
      .env n (rs.extract 1 rs.size) p
    else .env n (overlayInputsList body none #[] body.toList 0 0) p
  | .math d body p => .math d body p
  | .word w p => .word w p
  | .space => .space
  | .par p => .par p
  | .ctrl n p => .ctrl n p
  | .sym c p => .sym c p
  | .verb env s p => .verb env s p

end

/-- The shared source boundary, before compatibility routing and the one
elaborator. Macro execution must precede this pass. -/
public def overlayInputs (raws : Array Raw) : Array Raw :=
  overlayInputsList raws none #[] raws.toList 0 0

private structure OverlayScan where
  pending : Option OverlayWindow := none
  opened : Bool := false

private def OverlayScan.step (scan : OverlayScan) (r : Raw) : OverlayScan := Id.run do
  let mut pending := scan.pending
  let mut opened := scan.opened
  match r with
  | .word text p =>
    let mut s := text
    if !opened then
      if let some name := pending.bind (overlayVariantName · text) then
        pending := overlayNext none (.ctrl name p) 0
        s := (text.drop 1).toString
    if !opened && !pending.any (·.accepts) then
      pending := overlayNext pending r 0
    else
      for c in s.toList do
        if opened then
          if c == '>' then
            opened := false
            pending := pending.bind OverlayWindow.afterSelector
        else if c == '<' && pending.any (·.accepts) then
          opened := true
        else if c.isWhitespace then
          pending := overlayNext pending .space 0
        else pending := none
  | .ctrl _ _ | .sym _ _ | .space =>
    if !opened then pending := overlayNext pending r 0
  | _ =>
    opened := false
    pending := overlayNext pending r 0
  return { pending, opened }

/-- The selector cursor belongs to the emitted prefix. Its invariant makes
macro splices and ordinary tokens resume the same scan, without replaying
all earlier output at every control. -/
private structure OverlayPrefix where
  raws : Array Raw
  scan : OverlayScan
  scan_exact : scan = raws.foldl OverlayScan.step {}

private def OverlayPrefix.ofArray (raws : Array Raw) : OverlayPrefix :=
  ⟨raws, raws.foldl OverlayScan.step {}, rfl⟩

private def OverlayPrefix.push (out : OverlayPrefix) (r : Raw) : OverlayPrefix :=
  ⟨out.raws.push r, out.scan.step r, by simp [← out.scan_exact]⟩

private def OverlayPrefix.append (out : OverlayPrefix) (rs : Array Raw) : OverlayPrefix :=
  ⟨out.raws ++ rs, rs.foldl OverlayScan.step out.scan, by
    simp [← out.scan_exact]⟩

private instance : HAppend OverlayPrefix (Array Raw) OverlayPrefix := ⟨OverlayPrefix.append⟩

/-- The alert style around a body, one spelling for both `\alert` forms:
themed, the theme's alert colour AND bold — colour alone would be the only
signal distinguishing the run, which WCAG 2.2 SC 1.4.1 forbids (metropolis
itself colours only; the divergence is deliberate); unthemed there is no
alert colour and bold stands in. The bold is a declaration, as beamer's
`alerted text` font is: `\textbf` would also set a text command's italic
corrections at the run's edges, which beamer's `\alert` does not. -/
public def alertStyled (themed : Bool) (body : Array Raw) (pos : Pos) : Array Raw :=
  if themed then
    #[.ctrl "textcolor" pos, .group #[.word "alert" pos] pos,
      .group (#[.ctrl "bfseries" pos] ++ body) pos]
  else #[.group (#[.ctrl "bfseries" pos] ++ body) pos]

/-- An unforgeable command name: a control word cannot contain a space.
The marker asks Elab for a conditional style over one elaborated body. -/
public def alertMark (themed : Bool) : String :=
  if themed then "alert themed" else "alert plain"

/-- A conditional alert carries its body once. The compatibility walk leaves
the body group in its original stream, so its own commands are rewritten once
as well. Tests.overlayInputChecks observes the note numbers and label effects
on shipped pages and the full typed HTML, rather than inferring conservation
from two raw alternatives. -/
public def alertOverlay (themed : Bool) (spec : Raw) (body : Array Raw) (pos : Pos) : Array Raw :=
  #[.ctrl (alertMark themed) pos, spec, .group body pos]

/-- The raw boundary carries one body group; effect conservation is checked
at elaboration's artifacts, where footnotes and labels have meanings. -/
public theorem alertOverlay_exact (themed : Bool) (spec : Raw) (body : Array Raw) (pos : Pos) :
    alertOverlay themed spec body pos =
      #[.ctrl (alertMark themed) pos, spec, .group body pos] := by rfl

/-- The style is requested by one marker, without a second raw body. -/
public theorem alertOverlay_styled_exact (themed : Bool) (spec : Raw) (body : Array Raw)
    (pos : Pos) :
    (alertOverlay themed spec body pos)[0]? = some (.ctrl (alertMark themed) pos) := by rfl

/-- The single body stays untouched until its one elaboration. -/
public theorem alertOverlay_plain_exact (themed : Bool) (spec : Raw) (body : Array Raw)
    (pos : Pos) :
    (alertOverlay themed spec body pos)[2]? = some (.group body pos) := by rfl

/-- Numbered membership is decided by the elaborator's common reader. -/
public theorem alertOverlay_spec_id (themed : Bool) (spec : Raw) (body : Array Raw) (pos : Pos) :
    (alertOverlay themed spec body pos)[1]? = some spec := by rfl

/-- The boundary's set-line vocabulary: with the boundary open (the
default) these preamble lines are the standalone's, collected as written
and consumed silently — the real TikZ reads them where the engine's subset
cannot. A declared refusal (`\pictures{ tool = none }`) makes them unknown
commands again. Colours are not on this list: `\definecolor` folds into
the palette, and the palette is the one resolving site — the request
carries the roles a picture mentions with their resolved values
(`Ir.paletteDecls`), so a `\definecolor` and its `\palette` spelling
state one request (the conservation oracle holds them equal). -/
public def boundaryCtrls : List String :=
  ["usetikzlibrary", "tikzset", "gtrset", "pgfplotsset"]

/-- The set lines the engine reads *itself*: their key lists address the
picture machinery, and the engine has picture machinery of its own
(`Picture.readStyleList` takes the `/.style` definitions out of a
`\tikzset`). Such a line is therefore never the sentence's and never an
unknown command, whichever renderer ends up drawing — it still rides to
the boundary as well (`boundaryCtrls` keeps it), because a picture the
subset draws nothing of is drawn there and needs the same definitions.
A subset of `boundaryCtrls`. -/
public def nativeSetCtrls : List String := ["tikzset"]

/-- Picture packages, whose whole meaning is drawing: with the boundary
open (the default), their loads belong to the boundary standalone's
preamble (`boundaryDecls` carries each with its options) rather than being
W0103's named loss — the real TeX at the edge is what reads them. A closed
list, extended when a document brings the next one; a package with body
commands outside pictures does not belong here. -/
public def boundaryPkgs : List String := ["genealogytree", "pgfplots", "circuitikz"]

/-- The document refused the boundary: a `\pictures` block declaring
`tool = none`. Read over the unrewritten preamble exactly as
`boundaryDecls` reads its lines (order-free, `\input` wrappers spliced);
the one consumer is the `\usepackage` dispatch, which must know whether a
picture package's load rides to the boundary or is W0103's named loss.
The elaborator reads the same declaration through `scanDecls`. -/
private def boundaryRefused (raws0 : Array Raw) : Bool := Id.run do
  let mut raws := raws0
  let mut i := 0
  repeat
    if h : i < raws.size then
      match raws[i] with
      | .env "document" _ _ => break
      | .env n wrapped _ =>
        if (Parse.inputEnvFile? n).isSome then
          raws := raws.extract 0 i ++ wrapped ++ raws.extract (i + 1) raws.size
        else
          i := i + 1
      | .ctrl "pictures" _ =>
        let (args, k) := takeGroups raws (i + 1) 1
        let refused := (Decl.splitEntries (rawSrc (args.getD 0 #[]))).any fun e =>
          match Decl.splitEntry e with
          | some ("tool", v) => v.trimAscii.toString == "none"
          | _ => false
        if refused then return true
        i := max k (i + 1)
      | _ => i := i + 1
    else
      break
  return false

/-- The picture environments whose bodies ride to the boundary verbatim.
A set line written *inside* one is already that standalone's, so the
collector does not hoist it: hoisting would scope one picture's styling to
every other picture in the document. -/
public def pictureEnvs : List String := ["tikzpicture", "external"]

/-- The control words the picture walk gives a meaning of its own — its
statement heads, `\else` and `\fi` (`Picture.walkCtrls`, which a test holds
equal to this list). The conditional pass puts no document macro of such a
name into a picture: the walk names it where it stands. -/
public def picWalkCtrls : List String :=
  ["fill", "node", "draw", "path", "foreach", "pgfmathsetmacro",
   "pgfmathtruncatemacro", "else", "fi"]

/-- What one tree walk collects for the renderers of a document's
pictures: `pre` is the boundary standalone's preamble, as written; `sets`
is the same collection read natively — one entry per `nativeSetCtrls`
line, its key list beside the span of the line that wrote it: the line's
own file, which an `\input` wrapper names, as it names the file the
elaborator reads the line in (`tikzsetKeys_input_exact`). One accumulator,
so the two readings cannot disagree about which definitions reached a
picture. -/
public structure BoundaryScan where
  pre : String := ""
  sets : Array (Span × Array Raw) := #[]

mutual

/-- One level of the boundary-declaration walk. The list drives the
recursion; the array gives `takeOpt`/`takeGroups` O(1) access to the
siblings a set line's arguments are, and `skip` counts the siblings a
line already consumed so its argument group is never walked as content.
The accumulator carries both readings of the same collection — the
standalone's preamble text and the native key lists — so the two can
never disagree about which lines a picture's renderer was handed. It
accumulates, so the standalone's preamble is built in one pass in source
order. -/
-- conserves: none — the walk's result is the standalone's preamble text
-- plus the key lists the engine reads, not a tree: it collects the subset
-- of lines a picture's renderer must read and drops everything else by
-- design, so no census equality can hold. What it must conserve is stated
-- where it pays: `boundaryDecls_covers` and `tikzsetKeys_covers`.
private def boundaryLevel (file : String) (raws : Array Raw) (out : BoundaryScan) :
    List Raw → Nat → Nat → BoundaryScan
  | [], _, _ => out
  | _ :: rest, i, skip + 1 => boundaryLevel file raws out rest (i + 1) skip
  | .ctrl name p :: rest, i, 0 =>
    if name == "usepackage" || name == "RequirePackage" then
      let (opt, j) := takeOpt raws (i + 1)
      let (args, k) := takeGroups raws j 1
      let pkgs := ((rawSrc (args.getD 0 #[])).splitOn ",").map (·.trimAscii.toString)
        |>.filter (fun p => !p.isEmpty && !nativePackages.contains p)
      let out :=
        if pkgs.isEmpty then out
        else
          let o := match opt with | some o => s!"[{o}]" | none => ""
          let line := s!"\\usepackage{o}\{{String.intercalate "," pkgs}}\n"
          { out with pre := out.pre ++ line }
      boundaryLevel file raws out rest (i + 1) (k - (i + 1))
    else if boundaryCtrls.contains name then
      let (args, k) := takeGroups raws (i + 1) 1
      let groups := String.join (args.toList.map fun g => s!"\{{rawSrc g}}")
      let out := { out with pre := out.pre ++ s!"\\{name}" ++ groups ++ "\n" }
      let out :=
        if nativeSetCtrls.contains name then
          { out with sets := out.sets.push (⟨file, p⟩, args.getD 0 #[]) }
        else out
      boundaryLevel file raws out rest (i + 1) (k - (i + 1))
    else boundaryLevel file raws out rest (i + 1) 0
  | r :: rest, i, 0 => boundaryLevel file raws (boundaryRaw file out r) rest (i + 1) 0

/-- Descend into a group or an environment. Split from the list walk so
the recursion is structural on `Raw`: the body is a field of the head, not
a tail of the list — `rewriteList`/`rewriteRaw`'s shape. An `\input`
wrapper's body is read in its own file. -/
private def boundaryRaw (file : String) (out : BoundaryScan) : Raw → BoundaryScan
  | .group body _ => boundaryLevel file body out body.toList 0 0
  | .env n body _ =>
    if pictureEnvs.contains n then out
    else boundaryLevel ((Parse.inputEnvFile? n).getD file) body out body.toList 0 0
  | .math _ body _ => boundaryLevel file body out body.toList 0 0
  | .word _ _ => out
  | .space => out
  | .par _ => out
  | .ctrl _ _ => out
  | .sym _ _ => out
  | .verb _ _ _ => out

end

/-- What one walk of the tree collects for a picture's renderers: the
preamble text the boundary standalone needs, and the key lists the engine
reads itself, each with the position of the line it came from (a
diagnostic about a key belongs to the line that wrote it, not to whichever
picture first met it). -/
public def boundaryScan (file : String) (raws : Array Raw) : BoundaryScan :=
  boundaryLevel file raws {} raws.toList 0 0

/-- The preamble declarations a boundary standalone needs, collected from
the *unrewritten* tree — the compat rewrite drops package loads, so
collection precedes it. Every non-native `\usepackage` rides with its
options (pgfplots, genealogytree, circuitikz — whatever the pictures
need), and each closed-list set line is reconstructed as written.

**Wherever they stand.** A set line is a definition the pictures read, and
where the author wrote it says nothing about which pictures need it: a
figure kept in its own file carries its `\usetikzlibrary` and `\tikzset`
just above its picture, inside the document body, and a collector that
stopped at `\begin{document}` handed pgf a picture whose arrow tips and
shapes were never defined — `Unknown arrow tip kind`, `Unknown shape` —
so the boundary failed and the page shipped an empty box. The walk
therefore descends the whole tree; only a picture environment is left
closed (`pictureEnvs`), its body being its own standalone's already. Pure
and total; `\input` wrappers open as any other environment does. -/
public def boundaryDecls (file : String) (raws : Array Raw) : String :=
  (boundaryScan file raws).pre

/-- The key lists the engine reads itself, in source order, each with the
span of the `\tikzset` that wrote it, in the file that holds it
(`tikzsetKeys_input_exact`). Read from the *unrewritten* tree for the same
reason `boundaryDecls` is, and from the whole tree for the same reason:
where the author wrote a definition says nothing about which pictures need
it. The one consumer is the elaborator, which folds the
`/.style` entries into every picture's bundles (`Picture.readStyleList`)
and names what it could not read at the line above. -/
public def tikzsetKeys (file : String) (raws : Array Raw) : Array (Span × Array Raw) :=
  (boundaryScan file raws).sets

/-- **A set line reaches the boundary wherever it stands.** Wrapping a run
of declarations in the document environment leaves the standalone's
preamble exactly what it was — the invariant whose absence was the defect:
the preamble-only walk returned nothing for this tree, so a `\tikzset`
written beside its picture (a figure kept in its own file) never reached
pgf, the boundary failed on an arrow tip or a shape it had no definition
for, and the page shipped an empty box. -/
public theorem boundaryDecls_covers (file : String) (raws : Array Raw) (p : Pos) :
    boundaryDecls file #[.env "document" raws p] = boundaryDecls file raws := by
  simp [boundaryDecls, boundaryScan, boundaryLevel, boundaryRaw, pictureEnvs,
    Parse.inputEnvFile?, String.startsWith_string_iff]

/-- **And it reaches the engine's own renderer wherever it stands**, which
is the same claim for the native reading: a style defined beside its
picture, inside the document body, is the style that picture draws with.
Stated over the same walk the boundary's copy comes from, so neither
reading can gain a definition the other lost. -/
public theorem tikzsetKeys_covers (file : String) (raws : Array Raw) (p : Pos) :
    tikzsetKeys file #[.env "document" raws p] = tikzsetKeys file raws := by
  simp [tikzsetKeys, boundaryScan, boundaryLevel, boundaryRaw, pictureEnvs,
    Parse.inputEnvFile?, String.startsWith_string_iff]

/-- **A setting an included file wrote is that file's.** The scan reads an
`\input` wrapper's body under the file the wrapper names, as the elaborator
reads it, so a setting's span is the one the elaborator gives its line: a
note about its keys, or a formula a style of it sets, names that file and
never the including file's line of the same number. -/
public theorem tikzsetKeys_input_exact (caller file name : String) (body : Array Raw)
    (pos : Pos) (h : Parse.inputEnvFile? name = some file) :
    tikzsetKeys caller #[.env name body pos] = tikzsetKeys file body := by
  have hp : name ∉ pictureEnvs := by
    intro hm
    simp only [pictureEnvs, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp [Parse.inputEnvFile?, String.startsWith_string_iff] at h
  simp [tikzsetKeys, boundaryScan, boundaryLevel, boundaryRaw, hp, h]

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

/-- `\usepackage[...]{lineno}`'s options (lineno.sty, the package-options
section). `left`, `running`, `displaymath`, and `mathlines` name the
shipped state: continuous running numbers in the left margin, display-math
lines numbered like every line. `modulo` is `\modulolinenumbers`' initial
value five. The pagewise family (pagewise, switch, switch*, columnwise)
selects per-page or margin-switched numbering — continuous numbering is
lineno's own default and the one mode shipped, so each is named. -/
private def linenoLoad (opt : String) (pos : Pos) : M (Array Raw) := do
  let mut out : Array Raw := #[]
  for o in (opt.splitOn ",").map (·.trimAscii.toString) do
    if o.isEmpty || o == "left" || o == "running" || o == "displaymath"
        || o == "mathlines" then
      pure ()
    else if o == "modulo" then
      let native := "\\page{ modulo = 5 }"
      became "\\usepackage[modulo]{lineno}" native pos
      out := out ++ (← synthAt native pos)
    else
      say .W0101 s!"lineno option '{o}' selects a numbering mode the \
engine does not have; continuous numbers in the left margin stand" pos
  discard "\\usepackage{lineno}" "\\page{ linenumbers = on } turns line numbers on"
    "usepackage:lineno" pos
  return out

/-- unicode-math's option-driven legacy alphabets, carried into the typed
font specification. Other options are named here rather than silently
changing normal, bold, sans, or literal semantics. -/
private def unicodeMathOptions (what opt : String) (pos : Pos) : M (Array Raw) := do
  let mut sources : Array String := #[]
  let mut dropped : Array String := #[]
  for entry in Decl.splitEntries opt do
    match Decl.splitEntry entry with
    | some (key, value) =>
      match Math.MathAlphabet.sourceKey? key,
          Math.MathAlphabetSource.ofName? value.trimAscii.toString with
      | some _, some source => sources := sources.push s!"{key} = {source.name}"
      | _, _ => dropped := dropped.push entry
    | none => dropped := dropped.push entry
  unless dropped.isEmpty do
    say .W0101
      s!"unicode-math options without a model were dropped: {String.intercalate ", " dropped.toList}"
      pos (subject := some "usepackage:unicode-math:options")
  if sources.isEmpty then
    discard what "the engine keeps its existing math-source policy"
      "usepackage:unicode-math" pos
    return #[]
  let native := s!"\\fonts\{ {String.intercalate ", " sources.toList} }"
  became what native pos
  synthAt native pos

/-- Carry natbib declarations to the document: the `@natbib` marker, one
word per declaration, replayed at `\begin{document}` — where natbib reads
the bibliography style back from the `.aux` — for the body elaborator to
collect (`Ir.Doc.natbib`). -/
private def natbibDefer (decls : Array String) (pos : Pos) : M Unit :=
  write fun st => { st with deferred := st.deferred.push (.beginDocument, st.file, pos,
    #[.ctrl "@natbib" pos, .group (decls.map (.word · pos)) pos]) }

/-- `\usepackage[...]{natbib}`: the load, its options as declarations in
natbib's order. An option outside the punctuation vocabulary (`sort`,
`compress`, `super`, `longnamesfirst`, …) is named and dropped. -/
private def natbibLoad (name opt : String) (pos : Pos) : M (Array Raw) := do
  let given := (opt.splitOn ",").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
  let decls := Bib.natbibOptions.foldl (init := #[]) fun acc (o, ds) =>
    if given.contains o then acc.appendList ds else acc
  let dropped := given.filter fun o => !Bib.natbibOptions.any (·.1 == o)
  unless dropped.isEmpty do
    say .W0101 s!"'natbib' options without a native equivalent were dropped: \
{String.intercalate ", " dropped}" pos (subject := some "usepackage:natbib")
  became (if given.isEmpty then s!"\\{name}\{natbib}" else s!"\\{name}[{opt}]\{natbib}")
    "natbib's citation punctuation, read at \\begin{document}" pos
  natbibDefer decls pos
  return #[]

/-- `\setcitestyle{…}` and `\bibpunct[notesep]{open}{close}{sep}{mode}{aysep}{yysep}`
(natbib manual §2.5): in the preamble, natbib's declarations with its
`\bibstyle` door closed, as `\NAT@@setcites` closes it there. `\bibpunct`
is the same seven values by position — mode `n` numbers, `s` superscript
numbers (set on the baseline here, named), anything else author-year. An
item natbib does not read — natbib compares whole items, so a space after
a comma makes a word it does not know — is named and dropped, as natbib
drops it silently. `\citestyle{name}` applies natbib's row for the name
(`Bib.natbibRows`; none for a name without one) with the door closed, as
natbib.sty's `\citestyle` does. In the body natbib applies them from where
they stand; the engine reads natbib's punctuation for the whole document,
so a body declaration is named (W0340) and its groups consumed. -/
private def natbibStyleArm (name : String) (pos : Pos) (raws : Array Raw) (start : Nat) :
    M (Option (Array Raw × Nat)) := do
  let punct := name == "bibpunct"
  let (opt, j) := if punct then takeOpt raws start else (none, start)
  let (args, k) := takeGroups raws j (if punct then 6 else 1)
  if args.size != (if punct then 6 else 1) then return none
  -- premise: natbibChecks — a body declaration leaves no ink and no
  -- punctuation, the page of the document without it
  if (← get).inDoc then
    sayOnce ("ctrl:" ++ name) .W0340
      s!"'\\{name}' is read in the preamble; in the body it is ignored" pos
      (help := "declare it in the preamble, before '\\begin{document}'")
    return some (#[], k)
  -- natbib's values are token lists — `notesep={; }` keeps its space — and
  -- `rawSrc` trims every group, so the source is read one group deep as
  -- written.
  let verbatim (body : Array Raw) : String := body.foldl (init := "") fun s r =>
    let t := match r with
      | .group g _ => "{" ++ rawSrcList g.toList ++ "}"
      | r => rawSrcOne r
    s ++ t
  let src (i : Nat) : String := verbatim (args.getD i #[])
  let notesep := if opt.isSome then
      verbatim (raws.extract (skipSpaces raws start + 1) (j - 1)) else ", "
  let decls := if punct then
      #["open=" ++ src 0, "close=" ++ src 1, "citesep=" ++ src 2,
        if (src 3).trimAscii.toString == "n" || (src 3).trimAscii.toString == "s" then
          "numbers" else "authoryear",
        "aysep=" ++ src 4, "yysep=" ++ src 5, "notesep=" ++ notesep]
    else if name == "citestyle" then #["citestyle=" ++ (src 0).trimAscii.toString]
    else Bib.citeItems (src 0)
  let reads (d : String) : Bool := name == "citestyle" || Bib.CitePunct.reads d
  let dropped := decls.filter (!reads ·)
  unless dropped.isEmpty do
    say .W0101 s!"'\\{name}' keywords without a native equivalent were dropped: \
{String.intercalate ", " (dropped.toList.map fun d => s!"'{d}'")}" pos
      (help := "natbib reads each keyword exactly as written, so write no space after a comma")
      (subject := some ("ctrl:" ++ name))
  if punct && (src 3).trimAscii.toString == "s" then
    say .W0101 s!"'\\bibpunct' superscript citations are set on the baseline" pos
      (subject := some "ctrl:bibpunct")
  became s!"\\{name}" "natbib's citation punctuation, read at \\begin{document}" pos
  natbibDefer (#["nobibstyle"] ++ decls.filter reads) pos
  return some (#[], k)

/-- lineno's switch and modulo commands (lineno.sty, the user-commands
section), natively the declared page keys. `\linenumbers` and
`\runninglinenumbers` turn running numbers on — the one mode shipped —
and `\nolinenumbers` off. The starred on-forms only reset the count to 1,
where numbering always runs from 1, so the star is consumed inert; the
optional argument picks a first number, of which 1 is the shipped value
and anything else is named (W0101). `\modulolinenumbers` prints only
multiples of its argument while counting every line; without the argument
the counter's initial five stands, and [1] turns filtering off. Its
starred form's first-line exception (print the first number after
`\linenumbers` whatever the modulo) is not modelled; the star is consumed
so it cannot leak as content. -/
private def linenoCtrl (name : String) (pos : Pos) (raws : Array Raw)
    (start : Nat) : M (Option (Array Raw × Nat)) := do
  let k := skipStar raws start
  let (opt, k) := takeOpt raws k
  if name == "modulolinenumbers" then
    let n := (opt.bind (fun o => o.trimAscii.toString.toNat?)).getD 5
    let native := s!"\\page\{ modulo = {max 1 n} }"
    became "\\modulolinenumbers" native pos
    return some (← synthAt native pos, k)
  let on := name != "nolinenumbers"
  if on then
    if let some n := opt then
      unless n.trimAscii.toString == "1" do
        say .W0101 s!"'\\{name}[{n}]' asks to start numbering at {n}; \
line numbers here always run from 1" pos
  let native := s!"\\page\{ linenumbers = {if on then "on" else "off"} }"
  became s!"\\{name}" native pos
  return some (← synthAt native pos, k)

/-- The kernel's point-size macros at the values size10.clo–size12.clo and
ltplain give them, in milli-points: `\@xpt` is 10 pt, `\@xipt` 10.95 —
what `\@setfontsize` is called with. -/
private def ptMacros : List (String × Nat) :=
  [("@vpt", 5000), ("@vipt", 6000), ("@viipt", 7000), ("@viiipt", 8000),
   ("@ixpt", 9000), ("@xpt", 10000), ("@xipt", 10950), ("@xiipt", 12000),
   ("@xivpt", 14400), ("@xviipt", 17280), ("@xxpt", 20740), ("@xxvpt", 24880)]

/-- One `\@setfontsize` argument in milli-points: a kernel size macro, or
a literal number (`{14}`, `{10.95}`). -/
public def ptMacroArg (r : Array Raw) : Option Nat :=
  match r.toList with
  | [.ctrl n _] => ptMacros.lookup n
  | _ =>
    (Decl.parseDecimal (rawSrc r).trimAscii.toString).bind fun (m, s) =>
      if m ≥ 0 && s > 0 then some (m.toNat * 1000 / s) else none

/-- A milli value as its shortest decimal spelling: 10000 is "10",
10950 "10.95", 913 "0.913". -/
public def milliStr (m : Nat) : String :=
  let i := m / 1000
  let f := m % 1000
  if f == 0 then toString i else
  let digits := ((toString (1000 + f)).drop 1).toString
  let digits := if digits.endsWith "00" then (digits.dropEnd 2).toString
    else if digits.endsWith "0" then (digits.dropEnd 1).toString
    else digits
  s!"{i}.{digits}"

/-! # Decidable TeX conditionals

A TeX conditional the document's own definitions decide is resolved here,
to its taken branch, with a keyed note naming the decision (N0114), before
the idiom rewrite runs. `\ifdefined\name` reads whether the document bound
the name — a name nothing in the document bound is undefined, the honest
answer for another engine's primitives too (`\directlua`, `\pdfoutput`:
this engine is not that engine); a `\newif` flag's test reads its flow
state; `\ifnum`, `\ifodd` and `\ifcase` read integers, literal or held by a
macro the document defined as one; `\ifx` compares two macros the document
defined; `\iftrue` and `\iffalse` are their own answer.

The state is the one in force where the conditional stands. An environment
is a TeX group, so a definition made inside one ends with it; a macro holds
the value its latest definition in force gave it. That is what a picture's
test needs: the whole-document table its walk expands through cannot say
which of a macro's several definitions is in force at the picture's site,
and read that way three renderings of one picture under three states drew
one branch.

Every other head TeX defines (`condHeads`) is tracked too, as an opaque
frame whose `\else`, `\or` and `\fi` pass through, so a decided conditional
around or inside it stays matched and the refusal downstream sees the
undecided one whole. An `\if…` name that is neither — a package's own flag
the document never declared — cannot be matched, so an extent holding one
is left whole. -/

/-- The conditional heads TeX defines: every `\if…` primitive of TeX82's
table (`texPrimitives`) and e-TeX's three. The one list the pass tracks and
the accounting check ranges over. -/
private def condHeads : List String :=
  (texPrimitives.toList.filter (·.startsWith "if")) ++ ["ifdefined", "ifcsname", "iffontchar"]

/-- Definers that bind the control word standing after them, directly or
as `{\name}`. -/
private def definesNext : List String :=
  ["def", "edef", "gdef", "xdef", "let", "newcommand", "renewcommand",
   "providecommand", "DeclareRobustCommand", "DeclareMathOperator",
   "NewDocumentCommand", "RenewDocumentCommand", "ProvideDocumentCommand",
   "DeclareDocumentCommand",
   "define", "defineenv"]

/-- Bind `n` to `v`, recording what it replaced on the save stack. -/
private def setBind (n : String) (v : Option CondVal) : M Unit :=
  write fun st =>
    let prev := st.binds[n]?
    { st with undo := st.undo.push (.bind n prev), binds := st.binds.insert n v }

/-- Set the flag `x`, recording what it replaced on the save stack. -/
private def setFlag (x : String) (b : Bool) : M Unit :=
  write fun st =>
    let prev := st.flags[x]?
    { st with undo := st.undo.push (.flag x prev), flags := st.flags.insert x b }

/-- `n` is bound from here on; a value it already holds is kept. -/
private def recordDefined (n : String) : M Unit := do
  unless (← get).binds.contains n do setBind n none

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

/-- The value of the `\newif` flag this control word tests (`\ifX`), when
the pass has recorded the flag. -/
private def flagTested (flags : Std.HashMap String Bool) (n : String) : Option Bool :=
  if n.startsWith "if" && n.length > 2 then flags[(n.drop 2).toString]? else none

/-- Can the pass match a conditional headed `n`: one TeX defines, or the
`\ifX` of a flag the document declared? -/
private def isCondHead (flags : Std.HashMap String Bool) (n : String) : Bool :=
  condHeads.contains n || (flagTested flags n).isSome

/-- Where the conditional heading `raws[i]` ends, when the pass can match
it: the index of the `\fi` that closes it at this level, provided every
`\if…` name inside the extent is a head the pass tracks (`isCondHead`) —
decided or not, every one of them opens a frame, so `\else`/`\fi` matching
stays in step. An `\if…` name the pass does not know might open a
conditional or might not, which would desynchronise the matching, so it
leaves the whole extent alone. The name after `\newif` is the flag being
declared, not a conditional. `\ifstrequal` selects grouped arguments and
does not open a primitive conditional. -/
private def condExtentEnd (flags : Std.HashMap String Bool) (raws : Array Raw)
    (i : Nat) : Option Nat := Id.run do
  let mut depth := 0
  let mut j := i
  for _ in [i:raws.size] do
    match raws[j]? with
    | some (.ctrl "fi" _) =>
      if depth == 1 then return some j
      depth := depth - 1
      j := j + 1
    | some (.ctrl "newif" _) => j := j + 2
    | some (.ctrl n _) =>
      if isCondHead flags n then
        depth := depth + 1
        j := j + 1
      else if n.startsWith "if" && n != "ifstrequal" then return none
      else j := j + 1
    | some _ => j := j + 1
    | none => return none
  return none

/-- Can the pass match the conditional heading `raws[i]` (`condExtentEnd`)? -/
private def condExtent (flags : Std.HashMap String Bool) (raws : Array Raw) (i : Nat) : Bool :=
  (condExtentEnd flags raws i).isSome

/-- The value a name holds where the pass stands: `none` when nothing
bound it, `some none` when it is bound but unreadable. -/
private def condValueOf (binds : Std.HashMap String (Option CondVal)) (n : String) :
    Option (Option CondVal) :=
  binds[n]?

/-- A TeX integer literal: optional sign, decimal digits. -/
private def condIntLit (w : String) : Option Int :=
  let (neg, ds) := match w.toList with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  if ds.isEmpty || !ds.all Char.isDigit then none
  else (String.ofList ds).toNat?.map fun v => if neg then -(v : Int) else (v : Int)

/-- The integer a macro holds: its body is one literal, or one control word
holding an integer in turn. Structural on `k`: the caller passes the table's
size, and a chain of distinct names cannot be longer than the table holding
them — a longer one revisits a name, which is a cycle and no value. -/
private def condIntOf (vals : Std.HashMap String (Option CondVal)) : Nat → String → Option Int
  | 0, _ => none
  | k + 1, n =>
    match condValueOf vals n with
    | some (some v) =>
      if v.arity != 0 then none else
        match (v.raws.filter fun r => !(r matches .space)).toList with
        | [.word w _] => condIntLit w
        | [.ctrl m _] => condIntOf vals k m
        | _ => none
    | _ => none

/-- Expand only textual, parameterless selector fragments in the state of
this use. Every successful lookup is a key in this fixed, unmodified table.
Each recursive edge spends one name on its dependency path, so a path longer
than the table's size repeats a name. Parameterless expansion has no changing
argument or state to end that cycle. Sibling paths get the same remaining
bound: repeated uses of one dependency are not cycles. This is a finite-graph
bound, not a fixed expansion cap. A command with effects, groups or arguments
is not a fragment; it remains for the explicit unsupported-selector diagnostic. -/
private def overlayFragment (vals : Std.HashMap String (Option CondVal)) :
    Nat → String → Option String
  | 0, _ => none
  | k + 1, n => do
    let v ← (condValueOf vals n).bind id
    if v.arity != 0 || v.optional.isSome then none else do
      let parts ← v.raws.toList.mapM fun r => match r with
        | .word s _ => some s
        | .space => some ""
        | .sym c _ => some (String.singleton c)
        | .ctrl m _ => overlayFragment vals k m
        | _ => none
      return String.join parts

/-- One element a test is read from: a character of a word (with the raw it
stands in and its offset there), a space, or a control word. -/
private inductive CondAtom where
  | ch (c : Char) (ri : Nat) (ci : Nat)
  | sp (ri : Nat)
  | cs (n : String) (ri : Nat)

private def CondAtom.ri : CondAtom → Nat
  | .ch _ r _ => r
  | .sp r => r
  | .cs _ r => r

private def CondAtom.src : CondAtom → String
  | .ch c _ _ => String.ofList [c]
  | .sp _ => " "
  | .cs n _ => "\\" ++ n

/-- The atoms of a test starting at `raws[j]`: at most sixteen raws, the
widest test the decided shapes hold (two signed operands and a relation,
spaced), and never past a group, a paragraph or math, none of which a
number can hold. -/
private def condAtoms (raws : Array Raw) (j : Nat) : Array CondAtom := Id.run do
  let mut out : Array CondAtom := #[]
  for k in [j:min raws.size (j + 16)] do
    match raws[k]? with
    | some (.word w _) =>
      let mut ci := 0
      for c in w.toList do
        out := out.push (.ch c k ci)
        ci := ci + 1
    | some .space => out := out.push (.sp k)
    | some (.ctrl n _) => out := out.push (.cs n k)
    | some (.sym c _) => out := out.push (.ch c k 0)
    | _ => break
  return out

/-- A TeX ⟨number⟩ from atom `p0` on (TeXbook chapter 24, the decimal
case): signs and spaces, then digits or a macro holding an integer, then
one optional space. A macro the picture being walked binds for itself is
the picture's, and a digit straight after a macro would continue the
number past its expansion; both read as no value here. -/
private def condNumAt (st : St) (atoms : Array CondAtom) (p0 : Nat) :
    Option (Int × Nat) := Id.run do
  let mut p := p0
  let mut neg := false
  for _ in [p0:atoms.size] do
    match atoms[p]? with
    | some (.sp _) => p := p + 1
    | some (.ch '+' _ _) => p := p + 1
    | some (.ch '-' _ _) =>
      neg := !neg
      p := p + 1
    | _ => break
  let sign (v : Int) : Int := if neg then -v else v
  match atoms[p]? with
  | some (.ch c _ _) =>
    if !c.isDigit then return none
    let mut v : Int := 0
    for _ in [p:atoms.size] do
      match atoms[p]? with
      | some (.ch d _ _) =>
        if d.isDigit then
          v := v * 10 + ((d.toNat - '0'.toNat : Nat) : Int)
          p := p + 1
        else break
      | _ => break
    if atoms[p]? matches some (.sp _) then p := p + 1
    return some (sign v, p)
  | some (.cs n _) =>
    if st.picBound.contains n then return none
    match condIntOf st.binds st.binds.size n with
    | none => return none
    | some v =>
      p := p + 1
      match atoms[p]? with
      | some (.ch d _ _) => if d.isDigit then return none
      | some (.sp _) => p := p + 1
      | _ => pure ()
      return some (sign v, p)
  | _ => return none

/-- An `\ifnum` relation from atom `p0` on, spaces first. -/
private def condRelAt (atoms : Array CondAtom) (p0 : Nat) : Option (Char × Nat) := Id.run do
  let mut p := p0
  for _ in [p0:atoms.size] do
    if atoms[p]? matches some (.sp _) then p := p + 1 else break
  match atoms[p]? with
  | some (.ch c _ _) =>
    if c == '<' || c == '=' || c == '>' then return some (c, p + 1) else return none
  | _ => return none

/-- TeX's three integer relations. -/
private def condRelHolds (rel : Char) (a b : Int) : Bool :=
  if rel == '<' then a < b else if rel == '>' then a > b else a == b

/-- The test as written, from its atoms. -/
private def condSrc (atoms : Array CondAtom) (p : Nat) : String :=
  ((atoms.extract 0 p).foldl (fun s a => s ++ a.src) "").trimAscii.toString

/-- How many raws after `raws[j - 1]` a test ending at atom `p` consumed, and
the unread end of the word it stopped inside — branch content, which the
branch keeps or drops. -/
private def condFinish (raws : Array Raw) (j : Nat) (atoms : Array CondAtom) (p : Nat) :
    Nat × Option Raw :=
  match atoms[p]? with
  | none =>
    match atoms.back? with
    | some a => (a.ri + 1 - j, none)
    | none => (0, none)
  | some (.ch _ k ci) =>
    if ci == 0 then (k - j, none)
    else match raws[k]? with
      | some (.word w pos) => (k + 1 - j, some (.word (w.drop ci).toString pos))
      | _ => (k - j, none)
  | some (.sp k) => (k - j, none)
  | some (.cs _ k) => (k - j, none)

/-- One open conditional: decided (whether the branch now read is kept), an
`\ifcase` (the case it selects, the case now read, whether its `\else` has
been read), or opaque — a head the pass cannot decide, whose `\else`, `\or`
and `\fi` pass through so the refusal downstream reads it whole. -/
private inductive CondOpen where
  | decided (keep : Bool)
  | cased (sel : Int) (cur : Nat) (inElse : Bool)
  | opaque

/-- Does the frame keep what is read now? An opaque frame keeps both of its
branches: it is left for what comes after this pass. -/
private def CondOpen.keeps : CondOpen → Bool
  | .decided k => k
  | .cased sel cur inElse => if inElse then sel < 0 || sel > (cur : Int) else sel == (cur : Int)
  | .opaque => true

/-- What the pass reads a head as: the frame it opens, how many raws after
the head its test consumed, the unread end of the word the test stopped
inside, and the keyed note naming the decision. -/
private structure CondRead where
  frame : CondOpen
  used : Nat := 0
  tail : Option Raw := none
  note : Option (String × String) := none

/-- Which branch a two-way decision keeps, in words. -/
private def keptWords (keep : Bool) : String :=
  if keep then "the branch before '\\else' is kept" else "only the '\\else' branch is kept"

/-- The inner theme defines the option even when its package implementation
is replaced by a native theme. Source: both inner themes' `beamerframe`
`standout` key, inherited by the corresponding full themes. -/
private def nativeStandoutDefined (st : St) : Bool :=
  st.loads.pkgs.any fun (name, _) =>
    ["beamerthememoloch", "beamerthememetropolis", "beamerthemem",
     "beamerinnerthememoloch", "beamerinnerthememetropolis"].contains name

/-- A theme's own setter, which the engine implements (`molochOptions`), is
defined once the theme loads: beamerthememoloch.sty's `\molochset`. -/
private def nativeSetterDefined (st : St) (n : String) : Bool :=
  n == "molochset" && st.loads.pkgs.any (·.1 == "beamerthememoloch")

/-- Read the head `h` at `raws[i]` against the state in force there. `neg`:
an `\unless` stands before it, which reverses a two-way test (e-TeX) and is
refused before `\ifcase`. -/
private def readHead (st : St) (raws : Array Raw) (i : Nat) (h : String) (neg : Bool) :
    CondRead := Id.run do
  let undecided : CondRead := { frame := .opaque }
  -- A test that opens with a number reads with a space after the head.
  let shown (src : String) : String :=
    if src.isEmpty || src.startsWith "\\" then src else " " ++ src
  let two (v : Bool) (src what key : String) (used : Nat) (tail : Option Raw) : CondRead :=
    let keep := if neg then !v else v
    let msg := if neg then
        s!"'\\unless\\{h}{shown src}' reverses a test that \
{if v then "holds" else "fails"}, so {keptWords keep}"
      else s!"'\\{h}{shown src}' {what}, so {keptWords keep}"
    { frame := .decided keep, used := used, tail := tail,
      note := some (s!"{h}:{src}:{key}:{neg}", msg) }
  if h == "iftrue" || h == "iffalse" then
    let v := h == "iftrue"
    return two v "" (if v then "is true by definition" else "is false by definition")
      (toString v) 0 none
  if h == "ifdefined" then
    let k := skipSpaces raws (i + 1)
    match raws[k]? with
    | some (.ctrl n _) =>
      if st.picBound.contains n then return undecided
      -- premise: standoutPaletteChecks — inherited, absent and later-loaded
      -- hooks take different branches and ship the corresponding colours;
      -- blockFillConditionalChecks holds the setter's guard to the
      -- unguarded setter's artifact.
      let v := st.binds.contains n ||
        (n == "KV@beamerframe@standout" && nativeStandoutDefined st) ||
        nativeSetterDefined st n
      if neg then return two v s!"\\{n}" "" (toString v) (k - i) none
      return { frame := .decided v, used := k - i,
               note := some (s!"ifdefined:{n}:{v}", condMsg n v) }
    | _ => return undecided
  if h == "ifnum" || h == "ifodd" || h == "ifcase" then
    let atoms := condAtoms raws (i + 1)
    match condNumAt st atoms 0 with
    | none => return undecided
    | some (a, p1) =>
      if h == "ifcase" then
        if neg then return undecided
        let src := condSrc atoms p1
        let (used, tail) := condFinish raws (i + 1) atoms p1
        return { frame := .cased a 0 false, used := used, tail := tail,
                 note := some (s!"ifcase:{src}:{a}",
                   s!"'\\ifcase{shown src}' reads {a}, so only the case it selects is kept") }
      if h == "ifodd" then
        let v := a % 2 != 0
        let src := condSrc atoms p1
        let (used, tail) := condFinish raws (i + 1) atoms p1
        return two v src s!"reads {a}, which is {if v then "odd" else "even"}" (toString a)
          used tail
      match condRelAt atoms p1 with
      | none => return undecided
      | some (rel, p2) =>
        match condNumAt st atoms p2 with
        | none => return undecided
        | some (b, p3) =>
          let v := condRelHolds rel a b
          let src := condSrc atoms p3
          let (used, tail) := condFinish raws (i + 1) atoms p3
          return two v src s!"reads {a} {rel} {b}, which {if v then "holds" else "fails"}"
            s!"{a}{rel}{b}" used tail
  if h == "ifx" then
    match raws[i + 1]?, raws[i + 2]? with
    | some (.ctrl a _), some (.ctrl b _) =>
      if st.picBound.contains a || st.picBound.contains b then return undecided
      let src := s!"\\{a}\\{b}"
      if a == b then return two true src "compares a name with itself" "same" 2 none
      match condValueOf st.binds a, condValueOf st.binds b with
      | some (some va), some (some vb) =>
        let v := match va.optional, vb.optional with
          | some (a, da), some (b, db) =>
            a == b && macroTokens #[] da.toList == macroTokens #[] db.toList
          | none, none =>
            macroTokens #[] va.raws.toList == macroTokens #[] vb.raws.toList &&
              va.arity == vb.arity && va.long == vb.long && va.prot == vb.prot
          | _, _ => false
        return two v src
          (if v then "compares two equal definitions" else "compares two different definitions")
          (toString v) 2 none
      | _, _ => return undecided
    | _, _ => return undecided
  if let some v := flagTested st.flags h then
    if neg then return two v "" "" (toString v) 0 none
    return { frame := .decided v, note := some (s!"flag:{h}:{v}", flagMsg h v) }
  return undecided

/-- Primitives that read the next token as itself rather than expanding it:
a macro after one of them is not a use. -/
private def condNoExpand : List String :=
  ["noexpand", "string", "meaning", "show", "expandafter", "futurelet"]

/-- The definers whose operands the pass reads as a definition rather than as
content: `definesNext` and the environment definers. A definition's replacement
text is expanded where the definition is used, never where it is made. -/
private def condDefiners : List String :=
  definesNext ++ ["newenvironment", "renewenvironment", "newtcolorbox", "renewtcolorbox"]

/-- Is `n` the setter of a declared flag (`\Xtrue`, `\Xfalse`)? -/
private def isFlagSetter (flags : Std.HashMap String Bool) (n : String) : Bool :=
  (n.endsWith "true" && flags.contains (n.dropEnd 4).toString) ||
    (n.endsWith "false" && flags.contains (n.dropEnd 5).toString)

/-! # Package- and class-loaded tests

`\@ifpackageloaded{p}{t}{f}` asks whether package `p` is loaded, and the
document's own loads make that decidable here. The kernel's test
(`\@ifl@aded`, latex.ltx; ltclass.dtx) holds exactly when `\ver@p.sty` is
defined, and `\load@onefile@withoptions` defines it as the file starts to be
read: a package counts as loaded from its `\usepackage` or `\RequirePackage`
on, and never before. `\@ifpackagewith{p}{opts}` reads the list
`\@pass@ptions` accumulates for `p` — each `\PassOptionsToPackage` for it and
the options its load passed, never the class's global options — and holds
when every wanted option is on it. The class forms read the `\documentclass`
line the same way.

What the pass reads is the loads this document and its local style files
write. A package that another package loads, by a `\RequirePackage` inside a
file this engine never reads, is invisible and reads as not loaded: that is
the premise a negative answer rests on. A positive answer read where the test
stands rests on nothing, since a load written here is a load LaTeX performs.

A test is answered where it executes in the shared conditional walk. A
macro's text and a deferred hook are held verbatim until their use or replay;
a selected branch executes unbraced in the caller's state. No later pass
can select a different branch after its definitions or flag changes ran. -/

/-- The branches a loaded test carries after its name and option list: both,
the true one only, or the false one only (latex.ltx defines the `T` and `F`
forms over the `TF` one with `\@firstofone\@gobble` and `{}`). -/
private inductive LoadedBranches where
  | tf
  | t
  | f
  deriving BEq, Repr

/-- One spelling of the loaded-test family: whether it reads the class or the
packages, whether an option list follows the name, and its branches. -/
private structure LoadedTest where
  ctrl : String
  cls : Bool
  withOpts : Bool
  branches : LoadedBranches
  deriving BEq, Repr

/-- The family as latex.ltx defines it: the `\@if…` internals, and the
`\If…Loaded…` interface `\let` to them or wrapped around them. -/
private def loadedTests : List LoadedTest :=
  [⟨"@ifpackageloaded", false, false, .tf⟩, ⟨"IfPackageLoadedTF", false, false, .tf⟩,
   ⟨"IfPackageLoadedT", false, false, .t⟩, ⟨"IfPackageLoadedF", false, false, .f⟩,
   ⟨"@ifclassloaded", true, false, .tf⟩, ⟨"IfClassLoadedTF", true, false, .tf⟩,
   ⟨"IfClassLoadedT", true, false, .t⟩, ⟨"IfClassLoadedF", true, false, .f⟩,
   ⟨"@ifpackagewith", false, true, .tf⟩, ⟨"IfPackageLoadedWithOptionsTF", false, true, .tf⟩,
   ⟨"IfPackageLoadedWithOptionsT", false, true, .t⟩,
   ⟨"IfPackageLoadedWithOptionsF", false, true, .f⟩,
   ⟨"@ifclasswith", true, true, .tf⟩, ⟨"IfClassLoadedWithOptionsTF", true, true, .tf⟩,
   ⟨"IfClassLoadedWithOptionsT", true, true, .t⟩,
   ⟨"IfClassLoadedWithOptionsF", true, true, .f⟩]

/-- What one test asks: the class or the packages, the name, and the options
it wants (`none` for a load test). -/
private structure LoadQuery where
  cls : Bool
  name : String
  want : Option (Array String)
  deriving BEq, Repr

/-- An option list as the kernel compares it: comma-separated, spaces zapped
(`\zap@space`), empty items skipped. -/
private def optionItems (s : String) : Array String :=
  ((s.splitOn ",").map fun o => String.ofList (o.toList.filter (!·.isWhitespace)))
    |>.filter (!·.isEmpty) |>.toArray

/-- One execution gate for native packages and local styles. Reserving a
fresh name precedes its body, so recursive requires see the reservation.
A repeat keeps the first execution even on a clash, and names every new
option at the later call. The write also accounts for a compatible skip. -/
private def admitPackage (name : String) (options passed : List String) (pos : Pos) :
    M (Option (List String)) := do
  let (decision, imports) := PackageImports.admit (← get).loads.imports name options passed
  write fun st => { st with loads := { st.loads with imports } }
  match decision with
  | .load => return some (passed ++ options)
  | .skip missing =>
    for option in missing do
      say .W0110 s!"package '{name}' was already loaded; new option '{option}' is not applied" pos
        (help := "put all package options before its first load")
        (subject := some s!"package-option-clash:{name}:{option}")
    return none

/-- The production gate, for every compatible repeated load: no body is
returned, no diagnostic is added, and no semantic state is changed.
`writes` is only the dispatcher's accounting counter. -/
private theorem admitPackage_compatible_exact (name : String)
    (options passed first : List String) (pos : Pos) (st : St)
    (loaded : st.loads.imports.lookup name = some first)
    (compatible : ∀ o ∈ options, o ∈ first ++ passed) :
    admitPackage name options passed pos st = (none, { st with writes := st.writes + 1 }) := by
  simp only [admitPackage, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure]
  rw [PackageImports.admit_compatible_exact _ _ _ _ _ loaded compatible]
  rfl

/-- Tentatively admit a local file. The driver commits the returned
context only when the file exists, or when this is a repeat. A missing
file therefore remains an ordinary unresolved package request. Forwarded
options are precisely those in force at this executed call. -/
public def InputContext.admitLocalPackage (context : InputContext)
    (name options : String) (pos : Pos) : Option (List String) × InputContext :=
  let passed := (context.state.loads.passed.filter (·.1 == name)).toList.flatMap (·.2.toList)
  let (options, state) :=
    admitPackage name (PackageImports.literalOptions options) passed pos context.state
  (options, { state })

/-- One package load: the first load of a name stands, and a later one of the
same name passes nothing new. -/
private def LoadSet.addPkg (s : LoadSet) (p : String) (os : Option (Array String)) : LoadSet :=
  if s.pkgs.any (·.1 == p) then s else { s with pkgs := s.pkgs.push (p, os) }

/-- The class line: the first `\documentclass` is the class. -/
private def LoadSet.setCls (s : LoadSet) (c : String) (os : Array String) : LoadSet :=
  if s.cls.isSome then s else
    let passed := s.clsPassed.toList.flatMap fun (name, options) =>
      if name == c then options.toList else []
    (classPackages c (passed ++ os.toList)).foldl
      (fun loads name => loads.addPkg name (some #[])) { s with cls := some (c, os) }

/-- Option passes, onto the class half or the package half. -/
private def LoadSet.pass (s : LoadSet) (toClass : Bool) (ps : Array (String × Array String)) :
    LoadSet :=
  if toClass then { s with clsPassed := s.clsPassed ++ ps }
  else { s with passed := s.passed ++ ps }

/-- The answer the loads read so far give a test: `some true` when it holds,
`some false` when it fails, `none` when what it reads is not carried — a
local style file's passed options, where only a positive answer is sound. -/
private def LoadSet.answer (s : LoadSet) (q : LoadQuery) : Option Bool :=
  let passes (ps : Array (String × Array String)) : Array String :=
    (ps.filter (·.1 == q.name)).foldl (fun acc e => acc ++ e.2) #[]
  match q.cls, q.want with
  | false, none => some (s.pkgs.any (·.1 == q.name))
  | true, none => some (s.cls.any (·.1 == q.name))
  | false, some want =>
    let (seen, whole) := match s.pkgs.find? (·.1 == q.name) with
      | some (_, some os) => (passes s.passed ++ os, true)
      | some (_, none) => (passes s.passed, false)
      | none => (passes s.passed, true)
    if want.all seen.contains then some true else if whole then some false else none
  | true, some want =>
    let own := match s.cls with
      | some (c, os) => if c == q.name then os else #[]
      | none => #[]
    some (want.all (passes s.clsPassed ++ own).contains)

/-- Exactly `n` brace groups after `i`, each after any spaces: a grouped
test's shape, read before anything is decided. A token that is not a group,
or a paragraph break, leaves the test unread. -/
private def argGroupsAt (raws : Array Raw) (i n : Nat) : Option (Array (Array Raw)) :=
  Id.run do
    let mut out : Array (Array Raw) := #[]
    let mut j := i
    for _ in [0:n] do
      let k := skipSpaces raws j
      match raws[k]? with
      | some (.group body _) =>
        out := out.push body
        j := k + 1
      | _ => return none
    return some out

/-- A name argument the pass can read: letters and punctuation only. A
control word there is expanded by the kernel before the test, and this pass
does not expand. -/
private def plainName (body : Array Raw) : Bool :=
  body.all fun
    | .word .. | .space | .sym .. => true
    | .par .. | .ctrl .. | .group .. | .math .. | .env .. | .verb .. => false

/-- The question a loaded test at `i` asks, read from the groups after it;
`none` when its shape is not the family's. -/
private def loadedAt (raws : Array Raw) (i : Nat) (test : LoadedTest) : Option LoadQuery :=
  let n := 1 + (if test.withOpts then 1 else 0) + (if test.branches == .tf then 2 else 1)
  (argGroupsAt raws i n).bind fun args =>
    let name := args.getD 0 #[]
    if !plainName name || (rawSrc name).isEmpty then none
    else some { cls := test.cls, name := rawSrc name,
                want := if test.withOpts then
                  some (PackageImports.literalOptions (rawSrc (args.getD 1 #[]))).toArray
                  else none }

/-- e-TeX's `\detokenize` doubles parameter characters. -/
private def stringTestChars (s : String) : String :=
  s.toList.foldl (fun out c => (out.push c) ++ if c == '#' then "#" else "") ""

/-- A detokenized control word carries a delimiter space; a control symbol
does not (e-TeX manual, `\detokenize`). -/
private def stringTestControl (n : String) : String :=
  "\\" ++ n ++ if !n.isEmpty && n.toList.all Lex.nameChar then " " else ""

mutual

-- conserves: none — a comparison key over surface tokens, not an IR rewrite.
private def stringTestTokens (out : String) : List Raw → Option String
  | [] => some out
  | r :: rest => (stringTestToken r).bind fun s => stringTestTokens (out ++ s) rest

/-- Literal token spelling for etoolbox's `\ifstrequal`. Source pretty-printing
is unsuitable: it trims significant spaces and canonicalizes math delimiters.
No name lookup or operand execution occurs. Verbatim nodes have lost their
original delimiters, so their spelling is unread rather than guessed. -/
private def stringTestToken : Raw → Option String
  | .word s _ => some (stringTestChars s)
  | .space => some " "
  | .par _ => some (stringTestControl "par")
  | .ctrl n _ => some (stringTestControl n)
  | .sym c _ => some (stringTestChars (String.singleton c))
  | .group body _ => (stringTestTokens "{" body.toList).map (· ++ "}")
  | .math display body p =>
    let (left, right) := if p.command == some "\\(" then ("\\(", "\\)")
      else if display then ("\\[", "\\]") else ("$", "$")
    (stringTestTokens left body.toList).map (· ++ right)
  | .env n body _ =>
    (stringTestTokens (stringTestControl "begin" ++ "{" ++ n ++ "}") body.toList).map
      (· ++ stringTestControl "end" ++ "{" ++ n ++ "}")
  | .verb .. => none

end

/-- Partitioning a token sequence does not change its literal comparison
key, including an unread token's refusal. -/
private theorem stringTestTokens_append_exact (out : String) (xs ys : List Raw) :
    stringTestTokens out (xs ++ ys) =
      (stringTestTokens out xs).bind (fun s => stringTestTokens s ys) := by
  induction xs generalizing out with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, stringTestTokens]
    cases hx : stringTestToken x with
    | none => rfl
    | some s => simpa only [Option.bind_some] using ih (out ++ s)

/-- `etoolbox.sty` compares `\detokenize` of two operands, without expanding
them, then selects one of two branch arguments outside its comparison group.
Read all four groups before allowing any part of the call to execute. -/
private def stringTestAt (raws : Array Raw) (i : Nat) : Option Bool := do
  let args ← argGroupsAt raws i 4
  let left ← stringTestTokens "" (args.getD 0 #[]).toList
  let right ← stringTestTokens "" (args.getD 1 #[]).toList
  pure (left == right)

/-- Which of the groups after a resolved test are kept, unbraced, and which go
with it: the name and the option list go, and the branch the answer picks
stays. -/
private def loadedPlan (test : LoadedTest) (ans : Bool) : List Bool :=
  let lead := if test.withOpts then [false, false] else [false]
  let branches := match test.branches with
    | .tf => [ans, !ans]
    | .t => [ans]
    | .f => [!ans]
  lead ++ branches

/-- The note a resolved test earns: what it read, when, and what that keeps. -/
private def loadedMsg (test : LoadedTest) (q : LoadQuery) (ans : Bool) :
    String :=
  let opts := String.intercalate "," (q.want.getD #[]).toList
  let fact := match q.cls, q.want.isSome, ans with
    | false, false, true => s!"'{q.name}' is loaded"
    | false, false, false => s!"no package '{q.name}' is loaded"
    | false, true, true => s!"'{q.name}' was given '{opts}'"
    | false, true, false => s!"'{q.name}' was not given '{opts}'"
    | true, false, true => s!"the class is '{q.name}'"
    | true, false, false => s!"the class is not '{q.name}'"
    | true, true, true => s!"the class was given '{opts}'"
    | true, true, false => s!"the class was not given '{opts}'"
  let kept := match test.branches, ans with
    | .tf, true => "the first branch is kept"
    | .tf, false => "only the second branch is kept"
    | .t, true | .f, false => "its branch is kept"
    | .t, false | .f, true => "its branch is dropped"
  s!"'\\{test.ctrl}': {fact} here, so {kept}"

/-- A load the flow performs where it stands: a package line, the class line,
an option pass, or a theme slot (beamer's `\usetheme{X}` is
`\usepackage{beamerthemeX}`). A package loaded already keeps its first
options. -/
private def recordLoad (raws : Array Raw) (name : String) (i : Nat) : M Unit := do
  let names (g : Array Raw) : Array String := optionItems (rawSrc g)
  if name == "usepackage" || name == "RequirePackage" ||
      name == "RequirePackageWithOptions" then
    let (opt, j) := takeOpt raws (i + 1)
    let (args, _) := takeGroups raws j 1
    let os := if name == "RequirePackageWithOptions" then none
      else some (PackageImports.literalOptions (opt.getD "")).toArray
    write fun st => { st with loads :=
      (names (args.getD 0 #[])).foldl (fun s p => s.addPkg p os) st.loads }
  else if name == "documentclass" then
    let (opt, j) := takeOpt raws (i + 1)
    let (args, _) := takeGroups raws j 1
    let c := rawSrc (args.getD 0 #[])
    let os := (PackageImports.literalOptions (opt.getD "")).toArray
    unless c.isEmpty do
      write fun st => { st with loads := st.loads.setCls c os }
  else if name == "PassOptionsToPackage" || name == "PassOptionsToClass" then
    let (args, _) := takeGroups raws (i + 1) 2
    let os := (PackageImports.literalOptions (rawSrc (args.getD 0 #[]))).toArray
    let ps := (names (args.getD 1 #[])).map (·, os)
    write fun st => { st with loads := st.loads.pass (name == "PassOptionsToClass") ps }
  else if let some pre := themeAsking.lookup name then
    let (_, j) := takeOpt raws (i + 1)
    let (args, _) := takeGroups raws j 1
    let nm := rawSrc (args.getD 0 #[])
    unless nm.isEmpty do
      write fun st => { st with loads := st.loads.addPkg (pre ++ nm) (some #[]) }

/-- One collected hook: the note naming its replay point, and the body
stored against that point. Separate from the walk so the walk's recursive
calls stand in plain sight — a call behind a local function is a call the
termination checker cannot see. -/
private def deferOne (name : String) (pt : DeferPoint) (body : Array Raw)
    (pos : Pos) : M Unit := do
  became s!"\\{name}\{...}" (match pt with
    | .beginDocument => "its body, replayed at '\\begin{document}'"
    | .endPreamble => "its body, replayed at the end of the preamble") pos
  let file := (← get).file
  write fun st => { st with deferred := st.deferred.push (pt, file, pos, body) }

/-- The group primitives, opener to closer: `\begingroup … \endgroup`
scopes exactly what a brace pair scopes (TeXbook ch. 24, "\begingroup"),
and `\bgroup … \egroup` is the brace pair itself (latex.ltx `\let\bgroup={`). -/
public def groupPrimitives : List (String × String) :=
  [("begingroup", "endgroup"), ("bgroup", "egroup")]

/-- A flat preamble scope closes before the document starts. Unmatched
primitives stay in the stream for the existing diagnostic. -/
private def beamerScopeClosed (raws : Array Raw) (start : Nat) (close : String) : Bool :=
  Id.run do
    let mut closers := [close]
    for i in [start:raws.size] do
      match raws[i]! with
      | .ctrl n _ =>
        if closers.head? == some n then
          closers := closers.tail
          if closers.isEmpty then return true
        else if let some next := groupPrimitives.lookup n then
          closers := next :: closers
      | .env "document" _ _ => return false
      | _ => pure ()
    return false

mutual

-- conserves: none — a predicate over a replacement text, not a walk that
-- rewrites one.
/-- Does a replacement text do something only its use can decide
(`CondVal.live`): select an optional argument, hold a conditional, set a
flag, make a definition or a picture — itself, or through a macro it uses? -/
private def condLiveList (flags : Std.HashMap String Bool)
    (binds : Std.HashMap String (Option CondVal)) : List Raw → Bool
  | [] => false
  | r :: rest => condLiveRaw flags binds r || condLiveList flags binds rest

private def condLiveRaw (flags : Std.HashMap String Bool)
    (binds : Std.HashMap String (Option CondVal)) : Raw → Bool
  | .ctrl n _ =>
    isCondHead flags n || n == "unless" || n == "newif" || n == "ifstrequal" ||
      condDefiners.contains n ||
      (overlayArity? n).isSome ||
      isFlagSetter flags n || loadedTests.any (·.ctrl == n) ||
      (deferredHooks.lookup n).isSome ||
      ["input", "include", "markdownInput", "documentclass", "usepackage", "RequirePackage",
        "RequirePackageWithOptions", "PassOptionsToPackage", "PassOptionsToClass"].contains n ||
      (themeAsking.lookup n).isSome ||
      -- Length declarations and mutations execute at each use. Their
      -- operands reach the later scoped rewrite in execution order, so
      -- repeated assignments read the value the preceding one left.
      ["newlength", "setlength", "addtolength", "advance", "multiply", "divide"].contains n ||
      groupPrimitives.any (fun p => p.1 == n || p.2 == n) ||
      (match condValueOf binds n with
       | some (some v) => v.live
       | _ => false)
  | .group body _ => condLiveList flags binds body.toList
  | .env n body _ =>
    overlayTitled n || pictureEnvs.contains n || n == "tcolorbox" ||
      binds.contains (Tcolorbox.bindingName n) || condLiveList flags binds body.toList
  | .math _ body _ => condLiveList flags binds body.toList
  | .word _ _ => false
  | .space => false
  | .par _ => false
  | .sym _ _ => false
  | .verb _ _ _ => false

end

/-- A definition's operands as the pass reads them: where they stop, and
which of them are replacement texts. An expanding definer's text is read
where it stands, as TeX reads it, so it is not among the texts. -/
private structure DefShape where
  stop : Nat
  bodies : List Nat

/-- The operands of the definer `d` at `raws[i]`, or `none` for a shape the
pass does not read, whose operands then pass as content: `\def`'s name,
parameter text and text; `\let`'s name and source; the `\newcommand`
family's name, `[n]`, `[default]` and text; an environment's name, options
and two texts; xparse's name, argument spec and text; the native definers'
name, signature and texts. -/
private def definerShape (raws : Array Raw) (i : Nat) (d : String)
    (stored : Bool := false) : Option DefShape := Id.run do
  -- The first group at or after `k`, the parameter text or signature before it.
  let groupFrom (k : Nat) : Option Nat := Id.run do
    let mut j := k
    for _ in [k:raws.size] do
      match raws[j]? with
      | some (.group _ _) => return some j
      | some (.par _) => return none
      | some _ => j := j + 1
      | none => return none
    return none
  let named (k : Nat) : Bool :=
    raws[k]? matches some (.ctrl _ _) || raws[k]? matches some (.group _ _)
  let starred (k : Nat) : Nat :=
    let j := skipSpaces raws k
    if raws[j]? matches some (.word "*" _) then skipSpaces raws (j + 1) else j
  if d == "def" || d == "gdef" || d == "edef" || d == "xdef" || d == "define" then
    let j := skipSpaces raws (i + 1)
    -- A stored replacement text can name its future definition through
    -- an argument. Its extent can be read before that argument is bound.
    unless (raws[j]? matches some (.ctrl _ _)) ||
        (stored && (raws[j]? matches some (.sym '#' _))) do return none
    let some b := groupFrom (j + 1) | return none
    if d == "edef" || d == "xdef" then
      return some { stop := if stored then b + 1 else b, bodies := [] }
    return some { stop := b + 1, bodies := [b] }
  if d == "let" then
    let j := skipSpaces raws (i + 1)
    let k0 := skipSpaces raws (j + 1)
    let k := if raws[k0]? matches some (.word "=" _) then skipSpaces raws (k0 + 1) else k0
    unless raws[j]? matches some (.ctrl _ _) do return none
    if k < raws.size then return some { stop := k + 1, bodies := [] }
    return none
  if d == "newcommand" || d == "renewcommand" || d == "providecommand" ||
      d == "newtcolorbox" || d == "renewtcolorbox" ||
      d == "DeclareRobustCommand" || d == "DeclareMathOperator" then
    let j := starred (i + 1)
    unless named j do return none
    let (_, k1) := takeOpt raws (j + 1)
    let (_, k2) := takeOpt raws k1
    let b := skipSpaces raws k2
    unless raws[b]? matches some (.group _ _) do return none
    return some { stop := b + 1, bodies := [b] }
  if d == "newenvironment" || d == "renewenvironment" || d == "defineenv" then
    let j := starred (i + 1)
    unless raws[j]? matches some (.group _ _) do return none
    let some b1 := (if d == "defineenv" then groupFrom (j + 1) else
        let (_, k1) := takeOpt raws (j + 1)
        let (_, k2) := takeOpt raws k1
        let b := skipSpaces raws k2
        if raws[b]? matches some (.group _ _) then some b else none) | return none
    let b2 := skipSpaces raws (b1 + 1)
    unless raws[b2]? matches some (.group _ _) do return none
    return some { stop := b2 + 1, bodies := [b1, b2] }
  if d == "NewDocumentCommand" || d == "RenewDocumentCommand" ||
      d == "ProvideDocumentCommand" || d == "DeclareDocumentCommand" then
    let j := skipSpaces raws (i + 1)
    unless named j do return none
    let s := skipSpaces raws (j + 1)
    unless raws[s]? matches some (.group _ _) do return none
    let b := skipSpaces raws (s + 1)
    unless raws[b]? matches some (.group _ _) do return none
    return some { stop := b + 1, bodies := [b] }
  return none

mutual

-- conserves: none — drops each conditional extent, definition and flag setting a
-- definition's text holds, by design: they are decided at a use.
/-- A replacement text with what only a use can decide removed, at any
depth — every conditional extent and definition the pass can match, every
declared flag's setter and `\newif` — and whether anything was: the text an expansion that
has no conditionals is given in place of branches it cannot choose. The list
drives the recursion; `raws` and `i` give a head its extent, as `condList`
pairs them. -/
private def condStripList (flags : Std.HashMap String Bool) (raws : Array Raw)
    (acc : Array Raw) (hit : Bool) : List Raw → Nat → Nat → Array Raw × Bool
  | [], _, _ => (acc, hit)
  | _ :: rest, i, skip + 1 => condStripList flags raws acc hit rest (i + 1) skip
  | .ctrl n p :: rest, i, 0 =>
    let h := match n, raws[i + 1]? with
      | "unless", some (.ctrl h _) => h
      | _, _ => n
    let hi := if h != n then i + 1 else i
    if isCondHead flags h then
      match condExtentEnd flags raws hi with
      | some e => condStripList flags raws acc true rest (i + 1) (e - i)
      | none => condStripList flags raws (acc.push (.ctrl n p)) hit rest (i + 1) 0
    else if isFlagSetter flags n then
      condStripList flags raws acc true rest (i + 1) 0
    else if n == "newif" then
      condStripList flags raws acc true rest (i + 1) 1
    else if condDefiners.contains n then
      match definerShape raws i n (stored := true) with
      | some sh => condStripList flags raws acc true rest (i + 1) (sh.stop - (i + 1))
      | none => condStripList flags raws (acc.push (.ctrl n p)) hit rest (i + 1) 0
    else condStripList flags raws (acc.push (.ctrl n p)) hit rest (i + 1) 0
  | r :: rest, i, 0 =>
    let (r', h) := condStripRaw flags r
    condStripList flags raws (acc.push r') (hit || h) rest (i + 1) 0

private def condStripRaw (flags : Std.HashMap String Bool) : Raw → Raw × Bool
  | .group body p =>
    let (b, h) := condStripList flags body #[] false body.toList 0 0
    (.group b p, h)
  | .env n body p =>
    let (b, h) := condStripList flags body #[] false body.toList 0 0
    (.env n b p, h)
  | .math d body p =>
    let (b, h) := condStripList flags body #[] false body.toList 0 0
    (.math d b p, h)
  | .word w p => (.word w p, false)
  | .space => (.space, false)
  | .par p => (.par p, false)
  | .ctrl n p => (.ctrl n p, false)
  | .sym c p => (.sym c p, false)
  | .verb e s p => (.verb e s p, false)

end

/-- Record a definition of `n` whose readable value is `v` (`none`: none
the pass can read), globally when `global`. Each binding takes the next
serial; a copied meaning keeps its text's serial. Whether the text is live
is read against the state the binding is made in. -/
private def recordValue (n : String) (v : Option CondVal) (global : Bool)
    (copied : Bool := false) : M Unit := do
  let st ← get
  let s := st.serial + 1
  let v := v.map fun c =>
    { c with
      live := global || c.live || c.arity > 0 || c.optional.isSome || condLiveList st.flags st.binds c.raws.toList
      serial := s
      -- premise: Tests.macroHookScopeChecks — a local let inside a
      -- substituted group executes its copied meaning before scope closes.
      textSerial := if copied then c.textSerial else s }
  write fun st => { st with serial := s }
  setBind n v
  if global then write fun st => { st with globals := st.globals.push (n, v) }

private def withSpaceBinding (st : St) : St :=
  let value : CondVal :=
    { raws := #[.space], long := false, prot := false, live := true,
      serial := st.serial + 1, textSerial := st.serial + 1 }
  { st with
    serial := st.serial + 1
    binds := st.binds.insert "space" (some value)
    undo := st.undo.push (.bind "space" st.binds["space"]?)
    writes := st.writes + 2 }

private theorem recordValue_space_exact (st : St) :
    recordValue "space"
      (some { raws := #[.space], long := false, prot := false, live := true }) false false st =
        ((), withSpaceBinding st) := by
  simp [recordValue, setBind, withSpaceBinding,
    bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    write_eq,
    pure, StateT.pure, Nat.add_assoc]

/-- The prefixes standing before the definer at `raws[i]`, nearest first: a
run of at most three of `\long`, `\protected`, `\outer` and `\global`
(TeXbook chapter 24's ⟨prefix⟩, with e-TeX's `\protected`). -/
private def definerPrefixes (raws : Array Raw) (i : Nat) : List String := Id.run do
  let mut out : List String := []
  let mut k := i
  for _ in [0:6] do
    if k == 0 then break
    match raws[k - 1]? with
    | some .space => k := k - 1
    | some (.ctrl p _) =>
      if out.length < 3 && (p == "long" || p == "protected" || p == "outer" || p == "global") then
        out := p :: out
        k := k - 1
      else break
    | _ => break
  return out

/-- The value the definer `d` at `raws[i]` gives the name it binds: the body,
undelimited arity and prefixes its meaning carries. LaTeX's
`\newcommand` family is `\long` exactly when it takes arguments and is not
starred, so a parameterless one is never `\long` (measured against LaTeX2e
2025-11-01: `\meaning` reads `macro:->x` for `\def` and `\newcommand` alike).
An optional wrapper records a reserved inner name containing a space, which
no document control word can spell. An `\outer` macro cannot stand where
`\ifx` would read it, and a robust command's meaning names the command
itself (`\protect \name␣`), so neither has a value two names could share.
An expanding definer (`\edef`, `\xdef`) reads a body with no control word
as itself and one standing for a single macro whose value holds none as
that value; anything else it would expand to is unread here. -/
private def definedValue (st : St) (raws : Array Raw) (i : Nat) (d : String) :
    Option CondVal := Id.run do
  let pre := definerPrefixes raws i
  if pre.contains "outer" then return none
  let long := pre.contains "long"
  let prot := pre.contains "protected"
  if d == "def" || d == "gdef" then
    let j := skipSpaces raws (i + 1)
    let some sh := definerShape raws i d | return none
    let b := sh.stop - 1
    let some arity := undelimitedArity (raws.extract (j + 1) b) | return none
    match raws[b]? with
    | some (.group body _) => return some { raws := body, arity, long, prot }
    | _ => return none
  if d == "edef" || d == "xdef" then
    let j := skipSpaces raws (i + 1)
    match raws[j]?, raws[j + 1]? with
    | some (.ctrl _ _), some (.group body _) =>
      if body.all fun r => !(r matches .ctrl _ _) then
        return some { raws := body, long, prot }
      match (body.filter fun r => !(r matches .space)).toList with
      | [.ctrl m _] =>
        match condValueOf st.binds m with
        | some (some v) =>
          if v.arity == 0 && v.raws.all fun r => !(r matches .ctrl _ _) then
            return some { raws := v.raws, long, prot }
          return none
        | _ => return none
      | _ => return none
    | _, _ => return none
  if d == "let" then
    let j := skipSpaces raws (i + 1)
    let k0 := skipSpaces raws (j + 1)
    let k := if raws[k0]? matches some (.word "=" _) then skipSpaces raws (k0 + 1) else k0
    match raws[j]?, raws[k]? with
    | some (.ctrl _ _), some (.ctrl m p) =>
      match condValueOf st.binds m with
      | some v => return v.map fun v => { v with live := true }
      | none =>
        if (overlayArity? m).isSome then
          return some { raws := #[.ctrl (overlayNativeName m) p], long := false, prot := false, live := true }
        return none
    | _, _ => return none
  if d == "newcommand" || d == "renewcommand" || d == "providecommand" then
    let j0 := skipSpaces raws (i + 1)
    let star := raws[j0]? matches some (.word "*" _)
    let j := if star then skipSpaces raws (j0 + 1) else j0
    let (count, k) := takeOpt raws (j + 1)
    let arity? := match count with
      | none => some 0
      | some s => s.trimAscii.toString.toNat?
    let some arity := arity? | return none
    if arity > 9 then return none
    let (defaultArg, k) := takeRawOpt raws k
    if defaultArg.isSome && arity == 0 then return none
    let some name := raws[j]?.bind boundName | return none
    let optional := defaultArg.map fun arg => (name ++ " optional", ungroupArg arg)
    match raws[skipSpaces raws k]? with
    | some (.group body _) =>
      return some {
        raws := body, arity, optional
        long := arity > 0 && !star, prot := false }
    | _ => return none
  return none

/-- Does the definer `d` at `raws[i]` define globally: `\gdef`, `\xdef`, or
a `\global` prefix among the definer's prefixes? -/
private def definesGlobally (raws : Array Raw) (i : Nat) (d : String) : Bool :=
  d == "gdef" || d == "xdef" || (definerPrefixes raws i).contains "global"

/-- The documented `\newtcolorbox{name}[arity][default]{keys}` head.
Only its shape is read here; key values and replacement text execute at
the environment's use through the ordinary argument binder. -/
private def tcolorboxValue (raws : Array Raw) (i : Nat) :
    Option (String × CondVal) := do
  let j := skipSpaces raws (i + 1)
  let some (.group #[.word name _] _) := raws[j]? | none
  let (count, k) := takeOpt raws (j + 1)
  let arity ← match count with
    | none => some 0
    | some s => s.trimAscii.toString.toNat?
  if arity > 9 then none else do
    let (defaultArg, k) := takeRawOpt raws k
    if defaultArg.isSome && arity == 0 then none else do
      let some (.group keys _) := raws[skipSpaces raws k]? | none
      let key := Tcolorbox.bindingName name
      some (name, {
        raws := keys, long := true, prot := false, arity, live := true
        optional := defaultArg.map fun arg => (key, ungroupArg arg) })

/-- The first control word of a group: the name a `\pgfmathsetmacro` sets. -/
private def condFirstCtrl (g : Array Raw) : Array String :=
  match g.find? (· matches .ctrl _ _) with
  | some (.ctrl n _) => #[n]
  | _ => #[]

/-- A control word's name. -/
private def condCtrlName : Raw → Option String
  | .ctrl n _ => some n
  | _ => none

/-- The control words between a `\foreach` and its `in`: its variables, and
a `count=` option's counter. -/
private def condForeachVars (rs : List Raw) : Array String :=
  let head := rs.takeWhile fun r => !(r matches .word "in" _) && !(r matches .group _ _)
  (head.filterMap condCtrlName).toArray

mutual

-- conserves: none — the scan answers a set of names, not a tree: the names a
-- picture binds for itself, whose tests the pass leaves to the picture's walk.
private def condBoundLevel (acc : Array String) : List Raw → Array String
  | [] => acc
  | .ctrl "foreach" _ :: rest =>
    let vs := condForeachVars rest
    condBoundLevel (acc ++ vs) rest
  | .ctrl "pgfmathsetmacro" _ :: .group g _ :: rest =>
    let vs := condFirstCtrl g
    condBoundLevel (acc ++ vs) rest
  | .ctrl "pgfmathtruncatemacro" _ :: .group g _ :: rest =>
    let vs := condFirstCtrl g
    condBoundLevel (acc ++ vs) rest
  | r :: rest => condBoundLevel (condBoundRaw acc r) rest

private def condBoundRaw (acc : Array String) : Raw → Array String
  | .group body _ => condBoundLevel acc body.toList
  | .env _ body _ => condBoundLevel acc body.toList
  | .math _ body _ => condBoundLevel acc body.toList
  | .word _ _ => acc
  | .space => acc
  | .par _ => acc
  | .ctrl _ _ => acc
  | .sym _ _ => acc
  | .verb _ _ _ => acc

end

private def condMark : M CondMark := do
  let st ← get
  return {
    undo := st.undo.size, globals := st.globals.size, picBound := st.picBound.size
    primitives := st.primitiveScopes.size }

/-- Set whether the pass reads a spliced file's top level, returning the
value it replaces. -/
private def swapTop (b : Bool) : M Bool := do
  let old := (← get).fileTop
  write fun st => { st with fileTop := b }
  return old

/-- Does `r` stand on source line `l`? A space rides with its neighbours; a
paragraph break ends the line. -/
private def onLine (l : Nat) : Raw → Bool
  | .space => true
  | .par _ => false
  | .word _ p | .ctrl _ p | .sym _ p | .group _ p | .math _ _ p | .env _ _ p
  | .verb _ _ p => p.line == l

/-- Unwind the save stack to `m`, latest change first: the definition state
the mark was taken in, the picture's own names included. -/
private def condUnwind (m : CondMark) : M Unit := do
  let st ← get
  let recs := st.undo.extract m.undo st.undo.size
  write fun st => { st with
    undo := st.undo.shrink m.undo, picBound := st.picBound.shrink m.picBound
    primitiveScopes := st.primitiveScopes.shrink m.primitives }
  for k in [0:recs.size] do
    match recs[recs.size - 1 - k]? with
    | some (.bind n prev) =>
      write fun st => { st with
        binds := match prev with
          | some v => st.binds.insert n v
          | none => st.binds.erase n }
    | some (.flag x prev) =>
      write fun st => { st with
        flags := match prev with
          | some b => st.flags.insert x b
          | none => st.flags.erase x }
    | none => pure ()

/-- A TeX group closes, whether braces, math or an environment. Its state is the
one it opened with — the save stack is unwound to its mark, latest change
first — and only the global definitions made inside it outlive it, in the
order they were made. -/
private def condClose (m : CondMark) : M Unit := do
  let made := (← get).globals.extract m.globals (← get).globals.size
  condUnwind m
  for (n, v) in made do setBind n v

/-- A nonexpandable token ends the document's opening space scan. The flag
is transient execution state, not a scoped assignment. -/
private def condStopSpaces : M Unit := do
  if (← get).ignoreSpaces then write fun st => { st with ignoreSpaces := false }

/-- A recognised box consumes its arguments even when preparation is refused. -/
private inductive BoxPreparation where
  | ready (prepared : Tcolorbox.Prepared)
  | refused

/-- An executed prefix and the next unread source index. A split word's
remainder stays separate: it is caller text, not output of the expansion. -/
private structure CondRun where
  raws : Array Raw
  stop : Nat
  tail : Array Raw := #[]
  box : Option BoxPreparation := none

mutual

/-- Resolve the decidable conditionals at one level. `stack` holds every open
conditional, innermost first; an element is emitted only while every frame
keeps what is read now (`CondOpen.keeps`), and a bare `\else`, `\or` or
`\fi` with nothing open is not ours and passes through. `skip` counts the
raws a decided head's test consumed. The list drives the recursion; `raws`
and `i` give the heads their lookahead, exactly as `rewriteList` pairs
them. `following` is available to a forwarded macro's argument reader,
but is not otherwise executed by this replacement's walk. -/
private def condList [Monad m]
    (ex : String → Pos → Array Raw → Nat → EvalM m (Option CondRun))
    (plan : List Bool) (raws following : Array Raw)
    (out : OverlayPrefix) (stack : List CondOpen) :
    List Raw → Nat → Nat → EvalM m CondRun
  | [], i, skip => pure { raws := out.raws, stop := i + skip }
  | _ :: rest, i, skip + 1 => condList ex plan raws following out stack rest (i + 1) skip
  | .space :: rest, i, 0 => do
    let out := if plan.isEmpty && stack.all CondOpen.keeps && !(← get).ignoreSpaces
      then out.push .space else out
    condList ex plan raws following out stack rest (i + 1) 0
  | .ctrl "newif" pos :: .ctrl n np :: rest, i, 0 => do
    -- `\newif\ifX` declares a decidable flag, initially false (plain TeX:
    -- `\newif` ends with `\csname …false\endcsname`): `\ifX` joins this
    -- pass, `\Xtrue`/`\Xfalse` set it. A `\newif` whose next token is not
    -- an `\if…` name passes through for the ordinary unknown warning.
    if !(stack.all CondOpen.keeps) then
      condList ex [] raws following out stack rest (i + 2) 0
    else if n.startsWith "if" && n.length > 2 then
      condStopSpaces
      let x := (n.drop 2).toString
      setFlag x false
      recordDefined n
      recordDefined (x ++ "true")
      recordDefined (x ++ "false")
      -- premise: settleChecks — a settled text is read, not run: what it
      -- declares or sets is undone after, so no note may say it holds
      unless (← get).settling.isSome do
        sayOnce ("cond:newif:" ++ n) .N0114
          s!"'\\newif\\{n}': '\\{n}' is resolved from here on, initially false"
          ((← get).useSite.getD pos)
      condList ex [] raws following out stack rest (i + 2) 0
    else
      condStopSpaces
      condList ex [] raws following ((out.push (.ctrl "newif" pos)).push (.ctrl n np)) stack rest (i + 2) 0
  | .ctrl "newif" pos :: .space :: .ctrl n np :: rest, i, 0 => do
    if !(stack.all CondOpen.keeps) then
      condList ex [] raws following out stack rest (i + 3) 0
    else if n.startsWith "if" && n.length > 2 then
      condStopSpaces
      let x := (n.drop 2).toString
      setFlag x false
      recordDefined n
      recordDefined (x ++ "true")
      recordDefined (x ++ "false")
      -- premise: settleChecks — a settled text is read, not run: what it
      -- declares or sets is undone after, so no note may say it holds
      unless (← get).settling.isSome do
        sayOnce ("cond:newif:" ++ n) .N0114
          s!"'\\newif\\{n}': '\\{n}' is resolved from here on, initially false"
          ((← get).useSite.getD pos)
      condList ex [] raws following out stack rest (i + 3) 0
    else
      condStopSpaces
      condList ex [] raws following (((out.push (.ctrl "newif" pos)).push .space).push (.ctrl n np))
        stack rest (i + 3) 0
  | .ctrl "else" pos :: rest, i, 0 => do
    match stack with
    | [] =>
      condStopSpaces
      condList ex [] raws following (out.push (.ctrl "else" pos)) [] rest (i + 1) 0
    | .decided k :: more => condList ex [] raws following out (.decided (!k) :: more) rest (i + 1) 0
    | .cased sel cur _ :: more => condList ex [] raws following out (.cased sel cur true :: more) rest (i + 1) 0
    | .opaque :: more =>
      if more.all CondOpen.keeps then condStopSpaces
      let out := if more.all CondOpen.keeps then out.push (.ctrl "else" pos) else out
      condList ex [] raws following out stack rest (i + 1) 0
  | .ctrl "or" pos :: rest, i, 0 => do
    match stack with
    | .cased sel cur false :: more =>
      condList ex [] raws following out (.cased sel (cur + 1) false :: more) rest (i + 1) 0
    | _ =>
      if stack.all CondOpen.keeps then condStopSpaces
      let out := if stack.all CondOpen.keeps then out.push (.ctrl "or" pos) else out
      condList ex [] raws following out stack rest (i + 1) 0
  | .ctrl "fi" pos :: rest, i, 0 => do
    match stack with
    | [] =>
      condStopSpaces
      condList ex [] raws following (out.push (.ctrl "fi" pos)) [] rest (i + 1) 0
    | .opaque :: more =>
      if more.all CondOpen.keeps then condStopSpaces
      let out := if more.all CondOpen.keeps then out.push (.ctrl "fi" pos) else out
      condList ex [] raws following out more rest (i + 1) 0
    | _ :: more => condList ex [] raws following out more rest (i + 1) 0
  | .ctrl "endinput" pos :: rest, i, 0 => do
    -- TeX reads the rest of the line, then no more of the file (TeXbook
    -- ch. 20). Only a file's own top level is cut: elsewhere the name
    -- passes through to be named where it stands. The walk ends here, so
    -- the conditionals the line closes close with it, and what else the
    -- line holds stands as written.
    if !(stack.all CondOpen.keeps) then
      condList ex [] raws following out stack rest (i + 1) 0
    -- premise: endInputChecks — a wrapper's top level is a file's own text,
    -- the one list TeX stops reading at a terminator
    else if (← get).fileTop then
      let line := rest.takeWhile (onLine pos.line)
      if (rest.drop line.length).any fun r => !(r matches .space | .par _) then
        became "\\endinput" s!"the end of '{(← get).file}': its later lines are not read" pos
          (subject := some "ctrl:endinput")
      let kept := line.filter fun r =>
        !(r matches .ctrl "fi" _ | .ctrl "else" _ | .ctrl "or" _)
      return { raws := out.raws ++ kept.toArray, stop := i + 1 + rest.length }
    else
      condStopSpaces
      condList ex [] raws following (out.push (.ctrl "endinput" pos)) stack rest (i + 1) 0
  | .ctrl n pos :: rest, i, 0 => do
    let st ← get
    -- `\unless` before a head reverses the head's test (e-TeX).
    let unlessHead : Option (String × Pos) := if n == "unless" then
        match rest with
        | .ctrl h hp :: _ => if isCondHead st.flags h then some (h, hp) else none
        | _ => none
      else none
    let head := (unlessHead.map (·.1)).getD n
    let hi := if unlessHead.isSome then i + 1 else i
    if isCondHead st.flags head then
      if stack.isEmpty && !condExtent st.flags raws hi then
        -- An extent the pass cannot match: left whole for what follows.
        condStopSpaces
        condList ex [] raws following (out.push (.ctrl n pos)) stack rest (i + 1) 0
      else
        let r := readHead st raws hi head unlessHead.isSome
        let live := stack.all CondOpen.keeps
        if live then
          if let some (key, msg) := r.note then
            match st.settling with
            | some d =>
              sayOnce ("cond:def:" ++ key) .N0114
                (msg ++ s!", in '\\{d}' as the engine reads it at the end of the preamble") pos
            | none => sayOnce ("cond:" ++ key) .N0114 msg (st.useSite.getD pos)
        let stack' := r.frame :: stack
        match r.frame, unlessHead with
        | .opaque, some (h, hp) =>
          if live then condStopSpaces
          let out := if live then (out.push (.ctrl n pos)).push (.ctrl h hp) else out
          condList ex [] raws following out stack' rest (i + 1) 1
        | .opaque, none =>
          if live then condStopSpaces
          let out := if live then out.push (.ctrl n pos) else out
          condList ex [] raws following out stack' rest (i + 1) 0
        | _, _ =>
          if r.tail.isSome && stack'.all CondOpen.keeps then condStopSpaces
          let out := match r.tail with
            | some t => if stack'.all CondOpen.keeps then out.push t else out
            | none => out
          condList ex [] raws following out stack' rest (i + 1)
            (r.used + (if unlessHead.isSome then 1 else 0))
    else if !(stack.all CondOpen.keeps) then
      condList ex [] raws following out stack rest (i + 1) 0
    else if let some close := groupPrimitives.lookup n then
      condStopSpaces
      let mark ← condMark
      write fun st => { st with primitiveScopes := st.primitiveScopes.push (close, mark) }
      condList ex [] raws following (out.push (.ctrl n pos)) stack rest (i + 1) 0
    else if st.primitiveScopes.back?.any (·.1 == n) then
      condStopSpaces
      if let some (_, mark) := st.primitiveScopes.back? then condClose mark
      condList ex [] raws following (out.push (.ctrl n pos)) stack rest (i + 1) 0
    else if let some pt := deferredHooks.lookup n then
      condStopSpaces
      let j := skipSpaces raws (i + 1)
      match raws[j]? with
      | some (.group body _) =>
        -- premise: Tests.macroHookScopeChecks — hooks execute at their seam;
        -- hookChecks holds nested and body declarations to their named fallback.
        if !st.condInDoc && !st.condReplaying then
          deferOne n pt body pos
          condList ex [] raws following out stack rest (i + 1) (j - i)
        else
          sayOnce ("ctrl:" ++ n) .W0340
            s!"'\\{n}' cannot defer from here; its group is read where it stands" pos
            (help := "declare the hook before '\\begin{document}'")
          condList ex [] raws following out stack rest (i + 1) 0
      | _ => condList ex [] raws following (out.push (.ctrl n pos)) stack rest (i + 1) 0
    else if let some ans := if n == "ifstrequal" then stringTestAt raws (i + 1) else none then
      -- premise: Tests.stringConditionalChecks — operands and the unselected
      -- branch stay inert; the selected argument executes in the caller's scope.
      let msg := if ans then
          "'\\ifstrequal': the literal strings agree, so the first branch is kept"
        else "'\\ifstrequal': the literal strings differ, so the second branch is kept"
      sayOnce ("string-test:" ++ msg) .N0114 msg (st.useSite.getD pos)
      condList ex [false, false, ans, !ans] raws following out stack rest (i + 1) 0
    else if let some (test, query) := (loadedTests.find? (·.ctrl == n)).bind fun test =>
        (loadedAt raws (i + 1) test).map (test, ·) then
      -- premise: loadedTestChecks — selected branches execute where the
      -- test stands; loads hidden inside an unread package remain unknown.
      match st.loads.answer query with
      | some ans =>
        let msg := loadedMsg test query ans
        sayOnce ("ifloaded:" ++ msg) .N0114 msg (st.useSite.getD pos)
        condList ex (loadedPlan test ans) raws following out stack rest (i + 1) 0
      | none =>
        condStopSpaces
        condList ex [] raws following (out.push (.ctrl n pos)) stack rest (i + 1) 0
    else if n == "apptocmd" then
      condStopSpaces
      -- Patch text and callbacks are arguments, not conditionals in force.
      -- The finite hook arm decides the whole call after these passes.
      let (_, k, _) := takeHookArgs raws (i + 1)
      condList ex [] raws following ((out.push (.ctrl n pos)) ++ raws.extract (i + 1) k)
        stack rest (i + 1) (k - (i + 1))
    else if n.endsWith "true" && st.flags.contains (n.dropEnd 4).toString then
      condStopSpaces
      let x := (n.dropEnd 4).toString
      setFlag x true
      -- premise: settleChecks — a settled text is read, not run: what it
      -- declares or sets is undone after, so no note may say it holds
      unless st.settling.isSome do
        sayOnce ("cond:set:" ++ n) .N0114 s!"'\\{n}': '\\if{x}' is true from here on"
          (st.useSite.getD pos)
      condList ex [] raws following out stack rest (i + 1) 0
    else if n.endsWith "false" && st.flags.contains (n.dropEnd 5).toString then
      condStopSpaces
      let x := (n.dropEnd 5).toString
      setFlag x false
      -- premise: settleChecks — a settled text is read, not run: what it
      -- declares or sets is undone after, so no note may say it holds
      unless st.settling.isSome do
        sayOnce ("cond:set:" ++ n) .N0114 s!"'\\{n}': '\\if{x}' is false from here on"
          (st.useSite.getD pos)
      condList ex [] raws following out stack rest (i + 1) 0
    else if n == "newtcolorbox" || n == "renewtcolorbox" then
      condStopSpaces
      match definerShape raws i n with
      | none =>
        condList ex [] raws following (out.push (.ctrl n pos)) stack rest (i + 1) 0
      | some sh =>
        match tcolorboxValue raws i with
        | none =>
          sayOnce ("tcolorbox:definition:" ++ n) .W0104
            s!"'\\{n}' has an unread argument declaration; the definition is skipped"
            (st.useSite.getD pos)
            (help := "use a braced environment name, 0–9 arguments, and at most one default")
        | some (name, value) =>
          let key := Tcolorbox.bindingName name
          let known := st.binds.contains key
          -- premise: TcolorboxChecks.tcolorboxScopeChecks — refused definitions leave
          -- built-in environments and existing scoped definitions unchanged.
          if st.provideKeeps.contains key || (n == "newtcolorbox" && known) ||
              (n == "renewtcolorbox" && !known) then
            sayOnce ("tcolorbox:definition:" ++ name) .W0104
              s!"'\\{n}\{{name}}' cannot replace this environment; its definition is skipped"
              (st.useSite.getD pos)
              (help := "use a new environment name, or renew an existing box")
          else
            let value := if stack.any (· matches .opaque) then none else some value
            recordValue key value (definesGlobally raws i n)
            became s!"\\{n}\{{name}}" "a scoped native block definition" (st.useSite.getD pos)
        condList ex [] raws following out stack rest (i + 1) (sh.stop - (i + 1))
    else if n == "tcbuselibrary" then
      condStopSpaces
      let (args, stop) := takeGroups raws (i + 1) 1
      if args.size == 1 then
        discard "\\tcbuselibrary" "box keys are handled at each use" n (st.useSite.getD pos)
        condList ex [] raws following out stack rest (i + 1) (stop - (i + 1))
      else condList ex [] raws following (out.push (.ctrl n pos)) stack rest (i + 1) 0
    else if condDefiners.contains n then
      condStopSpaces
      let bound := if definesNext.contains n then
          (rest.dropWhile isSpaceOrStar).head?.bind boundName
        else none
      let provide := n == "providecommand" || n == "ProvideDocumentCommand"
      if let some m := bound then
        -- premise: Tests.xparseIgnoredOperandsChecks — ignored operands
        -- keep both artifacts unchanged and receive one discard accounting.
        if provide && (st.binds.contains m || st.provideKeeps.contains m) then
          if let some sh := definerShape raws i n then
            let why := if st.binds.contains m then
                s!"'\\{m}' is already defined and the existing definition is kept"
              else s!"'\\{m}' is built in and the built-in stands"
            discard s!"\\{n}\{\\{m}}" why s!"{n}:{m}" (st.useSite.getD pos)
            -- Consume every operand before later passes can collect a hook
            -- from the ignored signature or replacement text.
            return ← condList ex [] raws following out stack rest (i + 1) (sh.stop - (i + 1))
        unless provide && st.binds.contains m do
          -- Inside a frame the pass cannot decide, the branch may not run:
          -- the name is bound (the flat reading), its value unread.
          let value := definedValue st raws i n
          let v := if stack.any (· matches .opaque) then none else value
          let global := definesGlobally raws i n
          -- A let copies the wrapper, not its target. Ordinary renewals
          -- leave the old optional target available to existing aliases.
          if n != "let" then
            if let some (key, _) := value.bind (·.optional) then
              recordValue key (v.map fun c => { c with optional := none }) global
          recordValue m v global (copied := n == "let")
      match definerShape raws i n with
      | none => condList ex [] raws following (out.push (.ctrl n pos)) stack rest (i + 1) 0
      | some sh =>
        -- The texts are expanded where the definition is used, never here:
        -- nothing in them is decided, set or defined now. What the
        -- expansion cannot decide is taken out of the definition the
        -- elaborator expands.
        let st ← get
        -- premise: tcolorboxTitleBindingChecks — title-local definitions
        -- leave no inline syntax, while global effects reach later content.
        if st.materializeTitle &&
            (bound.bind (condValueOf st.binds ·)).any Option.isSome &&
            !(bound.any st.provideKeeps.contains) then
          let kept := (definerPrefixes raws i).reverse.foldl (init := out.raws.toList.reverse)
            fun rs name => match rs.dropWhile (· matches .space) with
              | .ctrl found _ :: rest => if found == name then rest else rs
              | _ => rs
          let out := OverlayPrefix.ofArray kept.reverse.toArray
          -- Expanding definers have already evaluated their readable text;
          -- consume that text too, rather than recovering it as title content.
          let stop := ((definerShape raws i n (stored := true)).getD sh).stop
          became s!"\\{n}\\{bound.getD n}" "a scoped title binding"
            (st.useSite.getD pos) (subject := bound)
          return ← condList ex [] raws following out stack rest (i + 1) (stop - (i + 1))
        let liveVal := match bound.bind (condValueOf st.binds ·) with
          | some (some v) => if v.live then some v else none
          | _ => none
        -- A use of a built-in the pass never expands: the elaborator reads
        -- the text, at the preamble's end, so there it is settled.
        let expands := liveVal.isSome && !(bound.any st.provideKeeps.contains)
        -- premise: Tests.macroDefaultChecks — copied readable meanings
        -- execute at their uses, including after the source is redefined.
        if n == "let" && expands then
          became s!"\\let\\{bound.getD n}" "a copied command definition"
            (st.useSite.getD pos) (subject := some (bound.getD n))
          return ← condList ex [] raws following out stack rest (i + 1) (sh.stop - (i + 1))
        let settles := liveVal.any (·.arity == 0) && !st.condInDoc
        let refused := (n == "def" || n == "gdef") &&
          (undelimitedArity
            (raws.extract (skipSpaces raws (i + 1) + 1) (sh.stop - 1))).isNone
        let flags := st.flags
        let site := st.useSite
        let file := st.file
        let mut ops : Array Raw := #[]
        let mut stripped := false
        let mut texts : Array Pos := #[]
        for k in [i + 1:sh.stop] do
          if let some r := raws[k]? then
            if sh.bodies.contains k then
              let (r', h) := condStripRaw flags r
              ops := ops.push r'
              stripped := stripped || h
              if let .group _ gp := r then texts := texts.push gp
            else ops := ops.push r
        if settles then
          if let (some m, some v) := (bound, liveVal) then
            for gp in texts do
              write fun st => { st with
                pending := st.pending.push { name := m, serial := v.serial, file := file, pos := gp } }
        if stripped && !(expands || settles || refused) then
          -- premise: Tests.macroArgumentChecks — readable undelimited calls
          -- execute after binding; an unread definition keeps no program
          -- in a replacement text that the elaborator cannot execute.
          -- A delimited definition is refused whole by W0357 below,
          -- which also accounts for its replacement text.
          sayOnce ("cond:body:" ++ n ++ ":" ++ (bound.getD "")) .W0104
            (s!"'\\{n}' makes a definition whose text holds a conditional, a flag \
setting or another definition, which TeX executes where it is used; this engine cannot \
execute this definition there, so that part of the text is skipped whole")
            (site.getD pos)
            (help := "use \\def with undelimited arguments or \\newcommand")
        condList ex [] raws following ((out.push (.ctrl n pos)) ++ ops) stack rest (i + 1) (sh.stop - (i + 1))
    else if condNoExpand.contains n then
      condStopSpaces
      -- The next token is read as itself here, never expanded.
      match rest with
      | r :: _ => condList ex [] raws following ((out.push (.ctrl n pos)).push r) stack rest (i + 1) 1
      | [] => condList ex [] raws following (out.push (.ctrl n pos)) stack rest (i + 1) 0
    else
      if !st.condInDoc then recordLoad raws n i
      -- premise: Tests.overlayInputChecks — a selector reads textual macro
      -- fragments at its use, before the shared numbered boundary is sealed.
      if out.scan.opened then
        let r := match overlayFragment st.binds st.binds.size n with
          | some text => .word text pos
          | none => .ctrl n pos
        -- A refused fragment stays inside the selector; ordinary execution
        -- here would run effects and could turn its remainder into a number.
        condList ex [] raws following (out.push r) stack rest (i + 1) 0
      else match ← ex n pos (raws ++ following) (i + 1) with
        | some run =>
          if run.stop > i + 1 + rest.length then
            return { run with raws := out.raws ++ run.raws }
          condList ex [] raws following (out ++ run.raws ++ run.tail)
            stack rest (i + 1) (run.stop - (i + 1))
        | none =>
          condStopSpaces
          condList ex [] raws following (out.push (.ctrl n pos)) stack rest (i + 1) 0
  | r :: rest, i, 0 => do
    match plan with
    | keep :: more =>
      let out ← if keep && stack.all CondOpen.keeps then do
        match ← condOne ex false r with
        | .group body _ => pure (out ++ body)
        | r => pure (out.push r)
        else pure out
      condList ex more raws following out stack rest (i + 1) 0
    | [] =>
      if stack.all CondOpen.keeps then
        condList ex [] raws following (out.push (← condOne ex true r)) stack rest (i + 1) 0
      else
        condList ex [] raws following out stack rest (i + 1) 0

/-- Descend into a group, math or an environment body. The definition state
is restored when its TeX group closes (`condClose`). A selected test operand
has `groupScope = false`: its argument braces open no scope, but an explicit
group in its text still does. A picture's own bindings are known before its
body is read. An `\input` wrapper switches the file its notes name, as
`rewriteRaw` does, and is no group at all. -/
private def condOne [Monad m]
    (ex : String → Pos → Array Raw → Nat → EvalM m (Option CondRun))
    (groupScope : Bool) : Raw → EvalM m Raw
  | .group body p => do
    if groupScope then condStopSpaces
    let m ← condMark
    let top := (← get).fileTop
    if groupScope then write fun st => { st with fileTop := false }
    let body' ← condList ex [] body #[] (OverlayPrefix.ofArray #[]) [] body.toList 0 0
    let _ ← swapTop top
    if groupScope then condClose m
    return .group body'.raws p
  | .math d body p => do
    condStopSpaces
    let m ← condMark
    let top ← swapTop false
    let body' ← condList ex [] body #[] (OverlayPrefix.ofArray #[]) [] body.toList 0 0
    let _ ← swapTop top
    condClose m
    return .math d body'.raws p
  | .env n body p => do
    match Parse.inputEnvFile? n with
    | some f =>
      if !(← get).condInDoc && f.endsWith ".sty" then
        let pkg := (f.dropEnd ".sty".length).toString
        write fun st => { st with loads := st.loads.addPkg pkg none }
      let saved ← get
      write fun st => { st with file := f, useSite := none }
      let top ← swapTop true
      let body' ← condList ex [] body #[] (OverlayPrefix.ofArray #[]) [] body.toList 0 0
      let _ ← swapTop top
      write fun st => { st with file := saved.file, useSite := saved.useSite }
      return .env n body'.raws p
    | none =>
      if n == "document" then
        -- premise: Tests.macroPhaseChecks — only opening spaces disappear;
        -- a retained group or a subsequently discarded command stops the scan.
        write fun st => { st with ignoreSpaces := true }
      else condStopSpaces
      let m ← condMark
      let inPic := (← get).inPicture
      if pictureEnvs.contains n then
        let names := condBoundLevel #[] body.toList
        write fun st => { st with picBound := st.picBound ++ names, inPicture := true }
      let top ← swapTop false
      let box ← ex (Tcolorbox.bindingName n) p body 0
      -- The title argument belongs to this environment's selector window,
      -- just as it does in overlayInputsRaw after execution.
      let head := if overlayTitled n then #[Raw.ctrl "titled overlay" p] else #[]
      let front := head ++ (box.map (·.tail)).getD #[]
      let body' ← condList ex [] body #[] (OverlayPrefix.ofArray front) [] body.toList 0
        ((box.map (·.stop)).getD 0)
      let result ← match box.bind (·.box) with
        | some (.ready prepared) => do
          let lowered := prepared.lower body'.raws p
          became s!"\\begin\{{n}}" "a native block" p
          unless lowered.unsupported.isEmpty do
            say .W0110
              s!"these box keys are not fully applied: {String.intercalate ", " lowered.unsupported.toList}"
              p (help := "use native block styles for portable decoration")
              (subject := some ("tcolorbox:" ++ n))
          pure (Raw.env Parse.scopeEnv lowered.raws p)
        | some .refused => pure (.group (body'.raws.extract head.size body'.raws.size) p)
        | none => pure (.env n (body'.raws.extract head.size body'.raws.size) p)
      let _ ← swapTop top
      condClose m
      write fun st => { st with inPicture := inPic }
      return result
  | r => do
    condStopSpaces
    pure r

end

/-- Bind a readable command's optional first argument and remaining
undelimited arguments. An explicit empty option is a value; an unterminated
option is unread. Omission uses the already-read default without removing
another group. The optional lookahead consumes spaces but expands nothing. -/
private def takeCondArgs (raws : Array Raw) (start arity : Nat)
    (defaultArg : Option (Array Raw)) :
    Option (Array (Array Raw) × Nat × Array Raw) := do
  match defaultArg with
  | none => some (takeRawArgs raws start arity)
  | some fallback =>
    if arity == 0 then none else do
      let (actual, stop) := takeRawOpt raws start
      let first := skipSpaces raws start
      if actual.isNone && (raws[first]? matches some (.sym '[' _)) then none else
        let (args, stop, tail) := takeRawArgs raws
          (if actual.isSome then stop else first) (arity - 1)
        some (#[(actual.map ungroupArg).getD fallback] ++ args, stop, tail)

mutual

-- conserves: none — a predicate over surface tokens, not an IR rewrite.
/-- A substituted replacement that cannot request another expansion or
execute a control. Its group and math boundaries still pass through the
ordinary conditional walk, preserving the opening-space scan. -/
private def condTerminalList : List Raw → Bool
  | [] => true
  | r :: rest => condTerminalRaw r && condTerminalList rest

private def condTerminalRaw : Raw → Bool
  | .group body _ | .math _ body _ => condTerminalList body.toList
  | .ctrl _ _ | .env _ _ _ => false
  | .word _ _ | .space | .par _ | .sym _ _ | .verb _ _ _ => true

end

/-- Select the request of an unbound input command at its executed site.
Settlement reads stored text and never crosses the input door. -/
private def inputRequestAt (st : St) (n : String) (pos : Pos)
    (raws : Array Raw) (start : Nat) : Option (InputRequest × Nat) := do
  if st.settling.isSome then none else do
    let input := ["input", "include", "markdownInput"].contains n
    -- premise: frontendInputRequestChecks — execution inside a live macro
    -- can load a local style; settlement cannot.
    let style := !st.condInDoc &&
      (n == "usepackage" || n == "RequirePackage" || (themeAsking.lookup n).isSome)
    if !(input || style) then none else do
      let (_, k) := if n == "markdownInput" || style then takeOpt raws start else (none, start)
      let j := skipSpaces raws k
      let some (.group _ _) := raws[j]? | none
      some ({
        command := n
        file := st.file
        pos := st.useSite.getD pos
        callPos := pos
        operands := raws.extract start (j + 1) }, j + 1)

/-- The unbound-command arm of the production evaluator. Selection, the
actual reader call, its receipt and acceptance of its state have one owner. -/
private def condReadAt [Monad m] (reader : Option (InputReader m))
    (n : String) (pos : Pos) (raws : Array Raw) (start : Nat) :
    EvalM m (Option CondRun) := do
  let st ← get
  let some reader := reader | return none
  let some (request, stop) := inputRequestAt st n pos raws start | return none
  let (answer, context) ← dispatchInput (m := m) reader request { state := st }
  write fun _ => context.state
  return answer.map fun answer => { raws := answer, stop }

private theorem condReadAt_refused_exact (reader : InputReader Id)
    (st : St) (name : String) (pos : Pos) (raws : Array Raw) (start stop : Nat)
    (request : InputRequest)
    (hs : inputRequestAt st name pos raws start = some (request, stop))
    (hr : reader request { state := st } = (none, { state := st })) :
    condReadAt (some reader) name pos raws start st =
      (none, { st with
        inputAttempts := st.inputAttempts.push ⟨request, false⟩
        writes := st.writes + 1 }) := by
  simp only [condReadAt, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, hs, dispatchInput, hr, finishInput, InputContext.inputAttempts,
    Option.isSome_none, pure, StateT.pure]
  rfl

/-- Expand the macro `n` where the conditional pass meets it in live
content, when its optional argument or text needs the use's state
(`CondVal.live`), during the opening space scan, or inside a picture, which reads a
macro at its own site: the text is walked where the use stands, against the
state in force there, so its conditionals are decided — and its flags set,
its definitions made — at the use, as TeX does, and the decisions are named
at the use. `bound` is the binding order the enclosing text sees. An older
binding lowers it; a newer copy of an older text keeps it and lowers
`textBound` instead. Direct calls to helpers below that binding order stay
readable; a further local copy must itself lower one of the two orders.
Every recursive macro expansion descends the lexicographic pair. A substituted
replacement containing no controls or environments needs no recursion and
can execute even when neither order descends.
`prepareBox` is a separate final stage: preparing selected fields preserves
both macro orders and disables further preparation throughout those fields.
An optional wrapper and its inner text use the later of their serials,
so a retained alias sees the current inner text. A live use that still
needs recursion when the orders rule it out is refused by name; `none`
leaves it to the elaborator. -/
private def condExpandAt [Monad m] (reader : Option (InputReader m))
    (bound textBound : Nat) (prepareBox : Bool) (n : String) (pos : Pos)
    (raws : Array Raw) (start : Nat) : EvalM m (Option CondRun) := do
  let st ← get
  let site := st.useSite
  if let some name := Tcolorbox.boundName? n then
    let call := if name == "tcolorbox" then
        let (options, stop) := takeRawOpt raws start
        some (options.getD #[], stop, #[])
      else do
        let v ← (condValueOf st.binds n).bind id
        let usePos := site.getD pos
        let atUse := fun p : Pos => { p with line := usePos.line, col := usePos.col }
        let defaultArg := v.optional.map fun (_, arg) => arg.map (rebase atUse false)
        let (args, stop, tail) ← takeCondArgs raws start v.arity defaultArg
        if args.size != v.arity then none else
          some (bindRawArgsList args #[] (rebaseList atUse false v.raws.toList), stop, tail)
    let some (options, stop, tail) := call | return none
    -- A template selects fields without changing either macro order.
    -- Its original body keeps the caller's preparation stage in condOne.
    -- premise: tcolorboxPreparationChecks — copied helpers remain executable;
    -- refusing a nested template keeps only its consumed boundary and body.
    if _hstage : prepareBox then
      -- Capture selected colors in the use's binding snapshot before either
      -- font hook runs. Text fragments cannot execute assignments.
      let prepared ← Tcolorbox.prepareM (fun _ (rs : Array Raw) => pure <|
        (rs.toList.mapM fun (r : Raw) => match r with
          | .ctrl name p =>
            (overlayFragment st.binds st.binds.size name).map (Raw.word · p)
          | .word _ _ | .sym _ _ | .space => some r
          | _ => none).map List.toArray) options pos
      write fun s => { s with materializeTitle := true }
      let title ← condOne
        (fun n p rs k => condExpandAt reader bound textBound false n p rs k)
        true (.group prepared.title pos)
      write fun s => { s with materializeTitle := st.materializeTitle }
      let decls ← condList
        (fun n p rs k => condExpandAt reader bound textBound false n p rs k)
        [] prepared.bodyDecls #[] (OverlayPrefix.ofArray #[]) []
        prepared.bodyDecls.toList 0 0
      let title := match title with
        | .group body _ => body
        | _ => prepared.title
      return some {
        raws := #[], stop, tail
        box := some (.ready { prepared with title, bodyDecls := decls.raws }) }
    else
      say .W0104
        "a box title or style requests another box; its template is skipped and its body kept"
        (site.getD pos)
        (help := "place nested boxes in the body")
        (subject := some ("tcolorbox:" ++ name))
      return some { raws := #[], stop, tail, box := some .refused }
  let inPic := st.inPicture
  let own := st.picBound.contains n || st.provideKeeps.contains n ||
    (inPic && picWalkCtrls.contains n)
  match condValueOf st.binds n with
  | some (some v) =>
    -- premise: Tests.macroDefaultChecks — optional selection changes both
    -- artifacts; macroPhaseChecks holds the opening scan across expansion,
    -- and macroUseChecks holds execution between two states.
    if !(v.live || inPic || st.ignoreSpaces || st.materializeTitle) || own then return none
    let value := match v.optional with
      | none => some v
      | some (key, _) => (condValueOf st.binds key).bind id
    let some body := value | do
      sayOnce ("cond:unexpanded:" ++ n) .W0104
        s!"'\\{n}' selects an optional argument, but its replacement text depends \
on a conditional this engine cannot decide; the call is left unexpanded"
        (site.getD pos)
      return none
    let serial := max v.serial body.serial
    let textSerial := max v.textSerial body.textSerial
    -- Replacement text and omitted defaults come from the definition, but
    -- execute in this file. Relocate them before binding written arguments
    -- or reading includes, whose tokens keep their own source coordinates.
    -- Retain semantic ancestry from any already-settled child expansions.
    let usePos := site.getD pos
    let atUse := fun p : Pos => { p with line := usePos.line, col := usePos.col }
    let defaultArg := v.optional.map fun (_, arg) => arg.map (rebase atUse false)
    -- premise: Tests.macroHookScopeChecks — copied texts execute locally
    -- while aliases keep direct calls to helpers renewed before the use.
    let descends := serial < bound || textSerial < textBound
    -- premise: Tests.macroRoleChecks — a terminal substituted call executes
    -- without recursion, including copied meanings and discarded arguments;
    -- an out-of-order effectful call still names its lost execution.
    let terminal := !descends &&
      (takeCondArgs raws start body.arity defaultArg).any
        (fun (args, _, _) => args.size == body.arity &&
          condTerminalList (bindRawArgsList args #[] body.raws.toList).toList)
    if descends || terminal then
      let call := (takeCondArgs raws start body.arity defaultArg).filter
        fun (args, _, _) => args.size == body.arity
      let some (args, stop, tail) := call | do
        -- premise: macroForwardArgumentsChecks — an incomplete stored forwarder
        -- waits for its use; an incomplete actual call still names the loss.
        if st.settling.isSome then return none
        sayOnce ("cond:arguments:" ++ n) .W0104
          s!"'\\{n}' needs {body.arity} arguments before its replacement text can execute; \
the argument boundary is unread here, so its optional selection and state changes are not applied"
          (site.getD pos)
          (help := "close an optional argument with ']' and put each required argument in braces")
        return none
      -- Native content scopes separate uses of a settled body; settlement
      -- must retain the executed child's provenance within that body.
      let origin : Option MacroOrigin := if body.arity > 0 && !inPic
        then some { id := st.macroClock, name := n } else none
      let body := bindRawArgsList args #[] (rebaseList atUse false body.raws.toList)
      let following := tail ++ raws.extract stop raws.size
      let nextBound := if serial < bound then serial else bound
      write fun s => { s with
        useSite := some (site.getD pos), macroClock := st.macroClock + 1 }
      let top ← swapTop false
      let run ← if _h : serial < bound ∨ textSerial < textBound then
          condList (fun n p rs k => condExpandAt reader nextBound textSerial prepareBox n p rs k)
            [] body following (OverlayPrefix.ofArray #[]) [] body.toList 0 0
        else
          condList (fun _ _ _ _ => pure none) [] body following (OverlayPrefix.ofArray #[]) [] body.toList 0 0
      let _ ← swapTop top
      write fun s => { s with useSite := site }
      let out := match origin with
        | some origin => Parse.markMacroList origin #[] run.raws.toList
        | none => run.raws
      let used := run.stop - body.size
      let remaining := if used == 0 then tail else run.tail
      unless remaining.isEmpty do condStopSpaces
      return some { raws := out, stop := stop + (used - tail.size), tail := remaining }
    else if v.live then
      sayOnce ("cond:unexpanded:" ++ n) .W0104
        (s!"'\\{n}' selects an optional argument or holds state changes that TeX executes where it is \
used; here it is reached through a macro defined before it, which this engine expands \
without that selection or those changes")
        (site.getD pos)
        (help := "define '\\{n}' before the macros that use it")
      return none
    else return none
  | some none => return none
  | none =>
    condReadAt reader n pos raws start
termination_by (bound, textBound, if prepareBox then 1 else 0)
decreasing_by
  all_goals
    simp_wf
    first
    | exact Prod.Lex.right _ (Prod.Lex.right _ (by simp [_hstage]))
    | (split
       · apply Prod.Lex.left
         assumption
       · apply Prod.Lex.right
         apply Prod.Lex.left
         omega)

/-- The expander running text uses: every definition made so far is visible. -/
private def condTopExpand [Monad m] (reader : Option (InputReader m))
    (n : String) (pos : Pos) (raws : Array Raw) (start : Nat) :
    EvalM m (Option CondRun) := do
  let bound := (← get).serial + 1
  condExpandAt reader bound bound true n pos raws start

private theorem condTopExpand_unbound_exact (reader : Option (InputReader Id))
    (st : St) (name : String) (pos : Pos) (raws : Array Raw) (start : Nat)
    (hb : Tcolorbox.boundName? name = none)
    (hv : condValueOf st.binds name = none) :
    condTopExpand reader name pos raws start st =
      condReadAt reader name pos raws start st := by
  simp only [condTopExpand, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get]
  change condExpandAt reader (st.serial + 1) (st.serial + 1) true
    name pos raws start st = _
  rw [condExpandAt]
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, hb, hv]

private theorem condStopSpaces_quiet (st : St) (h : st.ignoreSpaces = false) :
    condStopSpaces st = ((), st) := by
  simp [condStopSpaces, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, StateT.pure, h]

private theorem condOne_word_exact
    (ex : String → Pos → Array Raw → Nat → EvalM Id (Option CondRun))
    (scope : Bool) (word : String) (pos : Pos) (st : St)
    (h : st.ignoreSpaces = false) :
    condOne ex scope (.word word pos) st = (.word word pos, st) := by
  simp only [condOne, bind, StateT.bind, pure, StateT.pure]
  change (match condStopSpaces st with
    | ((), s) => (Raw.word word pos, s)) = _
  rw [condStopSpaces_quiet st h]

private theorem condList_word_exact
    (ex : String → Pos → Array Raw → Nat → EvalM Id (Option CondRun))
    (word : String) (pos : Pos) (raws following : Array Raw)
    (out : OverlayPrefix) (i : Nat) (st : St)
    (h : st.ignoreSpaces = false) :
    condList ex [] raws following out [] [.word word pos] i 0 st =
      ({ raws := (out.push (.word word pos)).raws, stop := i + 1 }, st) := by
  rw [condList]
  all_goals try simp
  simp only [bind, StateT.bind, pure, StateT.pure,
    condOne_word_exact ex true word pos st h, condList, Nat.add_zero]

private theorem condClose_current_exact (st : St) :
    condClose {
      undo := st.undo.size, globals := st.globals.size
      picBound := st.picBound.size, primitives := st.primitiveScopes.size } st =
      ((), { st with writes := st.writes + 1 }) := by
  simp [condClose, condUnwind, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, write_eq,
    Array.extract_empty_of_stop_le_start, Array.shrink_eq_take]

private theorem condOne_literal_group_exact
    (ex : String → Pos → Array Raw → Nat → EvalM Id (Option CondRun))
    (word : String) (pos gp : Pos) (st : St)
    (h : st.ignoreSpaces = false) :
    condOne ex true (.group #[.word word pos] gp) st =
      (.group #[.word word pos] gp, { st with writes := st.writes + 3 }) := by
  simp only [condOne, bind, StateT.bind, pure, StateT.pure,
    ↓reduceIte]
  change (do
    condStopSpaces
    let mark ← condMark
    let top := (← get).fileTop
    write fun s => { s with fileTop := false }
    let body ← condList ex [] #[.word word pos] #[] (OverlayPrefix.ofArray #[])
      [] [.word word pos] 0 0
    let _ ← swapTop top
    condClose mark
    pure (Raw.group body.raws gp) : M Raw) st = _
  simp only [bind, StateT.bind, condStopSpaces_quiet st h,
    condMark, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, write_eq]
  rw [condList_word_exact ex word pos _ _ _ _
    { st with fileTop := false, writes := st.writes + 1 } h]
  simp only [swapTop, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, StateT.pure, write_eq]
  rw [condClose_current_exact { st with writes := st.writes + 1 + 1 }]
  simp [OverlayPrefix.push, OverlayPrefix.ofArray, Nat.add_assoc]

private theorem condList_literal_group_exact
    (ex : String → Pos → Array Raw → Nat → EvalM Id (Option CondRun))
    (word : String) (pos gp : Pos) (raws following : Array Raw)
    (out : OverlayPrefix) (i : Nat) (st : St)
    (h : st.ignoreSpaces = false) :
    condList ex [] raws following out [] [.group #[.word word pos] gp] i 0 st =
      ({ raws := (out.push (.group #[.word word pos] gp)).raws, stop := i + 1 },
        { st with writes := st.writes + 3 }) := by
  rw [condList]
  all_goals try simp
  simp only [bind, StateT.bind, pure, StateT.pure,
    condOne_literal_group_exact ex word pos gp st h, condList, Nat.add_zero]

private theorem condList_package_read_step
    (ex : String → Pos → Array Raw → Nat → EvalM Id (Option CondRun))
    (name : String) (pos : Pos) (raws following : Array Raw)
    (out : OverlayPrefix) (first : Raw) (rest : List Raw) (i : Nat) (st after : St)
    (hc : name = "usepackage" ∨ name = "RequirePackage")
    (hp : st.primitiveScopes = #[]) (hd : st.condInDoc = false)
    (hflags : st.flags = {})
    (ho : out.scan.opened = false)
    (he : ex name pos (raws ++ following) (i + 1)
      (recordLoad raws name i st).2 = (none, after))
    (hs : after.ignoreSpaces = false) :
    condList ex [] raws following out [] (.ctrl name pos :: first :: rest) i 0 st =
      condList ex [] raws following (out.push (.ctrl name pos)) [] (first :: rest)
        (i + 1) 0 after := by
  have hn : name ≠ "newif" ∧ name ≠ "else" ∧ name ≠ "or" ∧
      name ≠ "fi" ∧ name ≠ "endinput" ∧ name ≠ "unless" ∧
      name ≠ "ifstrequal" ∧ name ≠ "apptocmd" ∧
      name ≠ "newtcolorbox" ∧ name ≠ "renewtcolorbox" := by
    rcases hc with rfl | rfl <;> decide
  have hcond : isCondHead st.flags name = false := by
    have heads : condHeads.contains name = false := by
      have base : name ∉ texPrimitives.toList := by
        rcases hc with rfl | rfl <;> decide
      have extra : name ∉ ["ifdefined", "ifcsname", "iffontchar"] := by
        rcases hc with rfl | rfl <;> decide
      apply Bool.eq_false_iff.mpr
      intro h
      have hmem := List.contains_iff_mem.mp h
      rcases List.mem_append.mp hmem with h | h
      · exact base (List.mem_filter.mp h).1
      · exact extra h
    simp only [isCondHead, heads, Bool.false_or, flagTested, hflags,
      Std.HashMap.getElem?_empty]
    split <;> rfl
  have hg : groupPrimitives.lookup name = none := by
    rcases hc with rfl | rfl <;> decide
  have hh : deferredHooks.lookup name = none := by
    rcases hc with rfl | rfl <;> decide
  have hl : loadedTests.find? (·.ctrl == name) = none := by
    rcases hc with rfl | rfl <;> decide
  have ht : (name.endsWith "true" &&
      st.flags.contains (name.dropEnd 4).toString) = false := by simp [hflags]
  have hf : (name.endsWith "false" &&
      st.flags.contains (name.dropEnd 5).toString) = false := by simp [hflags]
  have hdef : condDefiners.contains name = false := by
    rcases hc with rfl | rfl <;> decide
  have hno : condNoExpand.contains name = false := by
    rcases hc with rfl | rfl <;> decide
  have hbox : (name == "newtcolorbox" || name == "renewtcolorbox") = false := by
    rcases hc with rfl | rfl <;> decide
  have htcb : name ≠ "tcbuselibrary" := by
    rcases hc with rfl | rfl <;> decide
  rw [condList.eq_16]
  all_goals try solve | simp_all
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure]
  simp only [hn.2.2.2.2.2.1, beq_iff_eq, ↓reduceIte, Option.map_none,
    Option.getD_none, hcond, List.all_nil,
    Bool.not_true, Bool.false_eq_true, hg, hp, Array.back?_empty,
    Option.any_none, hh, hn.2.2.2.2.2.2.1, hl, Option.bind_none,
    hn.2.2.2.2.2.2.2.1, ht, hf,
    hbox, htcb, hdef, hno, hd, Bool.not_false, ho]
  cases hload : recordLoad raws name i st with
  | mk tick loaded =>
    cases tick
    simp only [hload] at he
    simp only [evalLift_id, bind, StateT.bind, hload,
      he, condStopSpaces_quiet after hs]

/-- One live package call with a literal comma-separated name argument.
All names and positions are parameters; execution still uses the normal
conditional dispatcher and the supplied input reader. -/
public def packageCall (command names : String) (pos groupPos namePos : Pos) : Array Raw :=
  #[.ctrl command pos, .group #[.word names namePos] groupPos]

/-- The literal package-call surface exchanged with the elaborator. -/
public theorem packageCall_exact (command names : String)
    (pos groupPos namePos : Pos) :
    packageCall command names pos groupPos namePos =
      #[.ctrl command pos, .group #[.word names namePos] groupPos] := by
  rfl

private theorem packageCall_readers (command names : String)
    (pos groupPos namePos : Pos) :
    skipSpaces (packageCall command names pos groupPos namePos) 1 = 1 ∧
    takeOpt (packageCall command names pos groupPos namePos) 1 = (none, 1) ∧
    takeGroups (packageCall command names pos groupPos namePos) 1 1 =
      (#[#[.word names namePos]], 2) := by
  have hs : skipSpaces (packageCall command names pos groupPos namePos) 1 = 1 := by
    rw [skipSpaces]
    simp [packageCall]
  refine ⟨hs, ?_, ?_⟩
  · simp only [takeOpt, takeRawOpt, hs, Id.run]
    simp [packageCall]
  · simp [takeGroups, hs]
    simp [packageCall]

/-- The actual request's filename projection reads the package operand,
including the same outer whitespace normalization as the producer. -/
public theorem InputRequest.package_name_exact (file command names : String)
    (pos groupPos namePos : Pos) :
    (InputRequest.mk command file pos pos
      #[.group #[.word names namePos] groupPos]).name = names.trimAscii.toString := by
  change rawSrc ((takeGroups (packageCall command names pos groupPos namePos)
    (takeOpt (packageCall command names pos groupPos namePos) 1).2 1).1.getD 0 #[]) = _
  rw [(packageCall_readers command names pos groupPos namePos).2.1,
    (packageCall_readers command names pos groupPos namePos).2.2]
  simp [rawSrc, rawSrcList, rawSrcOne]

private theorem packageCall_request_exact (command names : String)
    (pos groupPos namePos : Pos) (st : St)
    (hc : command = "usepackage" ∨ command = "RequirePackage")
    (hd : st.condInDoc = false) (hs : st.settling = none) :
    inputRequestAt st command pos (packageCall command names pos groupPos namePos) 1 =
      some (⟨command, st.file, st.useSite.getD pos, pos,
        #[.group #[.word names namePos] groupPos]⟩, 2) := by
  have hp : (command == "usepackage" || command == "RequirePackage") = true := by
    rcases hc with rfl | rfl <;> decide
  have ht := (packageCall_readers command names pos groupPos namePos).2.1
  have hj := (packageCall_readers command names pos groupPos namePos).1
  simp [inputRequestAt, hs, hd, hp, ht, hj]
  simp [packageCall]

private def packageLoaded (st : St) (names : String) : St :=
  { st with
    loads := (optionItems names.trimAscii.toString).foldl
      (fun s p => s.addPkg p (some (PackageImports.literalOptions "").toArray)) st.loads
    writes := st.writes + 1 }

private theorem recordLoad_package_exact (command names : String)
    (pos gp np : Pos) (st : St)
    (hc : command = "usepackage" ∨ command = "RequirePackage") :
    recordLoad (packageCall command names pos gp np) command 0 st =
      ((), packageLoaded st names) := by
  have hw : (command == "RequirePackageWithOptions") = false := by
    rcases hc with rfl | rfl <;> decide
  simp only [recordLoad, ↓reduceIte, Nat.zero_add,
    (packageCall_readers command names pos gp np).2.1,
    (packageCall_readers command names pos gp np).2.2, hw, Bool.false_eq_true,
    Option.getD_none]
  simp [hc, rawSrc, rawSrcList, rawSrcOne, optionItems, packageLoaded, write_eq]

private def packageRequest (command names : String) (pos gp np : Pos)
    (st : St) : InputRequest :=
  ⟨command, st.file, st.useSite.getD pos, pos, #[.group #[.word names np] gp]⟩

private def packageFailed (command names : String) (pos gp np : Pos) (st : St) : St :=
  { packageLoaded st names with
    inputAttempts := st.inputAttempts.push ⟨packageRequest command names pos gp np st, false⟩
    writes := st.writes + 5 }

private theorem condList_package_failed_exact (reader : InputReader Id)
    (command names : String) (pos gp np : Pos) (st : St)
    (hc : command = "usepackage" ∨ command = "RequirePackage")
    (hp : st.primitiveScopes = #[]) (hd : st.condInDoc = false)
    (hflags : st.flags = {}) (hi : st.ignoreSpaces = false)
    (hsettling : st.settling = none)
    (hv : condValueOf st.binds command = none)
    (hr : ∀ request context, reader request context = (none, context)) :
    condList (condTopExpand (some reader)) []
      (packageCall command names pos gp np) #[] (OverlayPrefix.ofArray #[])
      [] (packageCall command names pos gp np).toList 0 0 st =
      ({ raws := packageCall command names pos gp np, stop := 2 },
        packageFailed command names pos gp np st) := by
  have hb : Tcolorbox.boundName? command = none := by
    rw [Tcolorbox.boundName?_exact]
    have h : command.toSlice.dropPrefix? "tcolorbox " = none := by
      rw [String.Slice.dropPrefix?_eq_none_iff,
        String.Slice.startsWith_string_eq_false_iff, String.copy_toSlice]
      rcases hc with rfl | rfl <;> decide
    rw [String.dropPrefix?_eq_dropPrefix?_toSlice, h]
    rfl
  let loaded := packageLoaded st names
  let attempted : St := { loaded with
    inputAttempts := loaded.inputAttempts.push
      ⟨packageRequest command names pos gp np loaded, false⟩
    writes := loaded.writes + 1 }
  have hex : condTopExpand (some reader) command pos
      (packageCall command names pos gp np ++ #[]) (0 + 1)
      (recordLoad (packageCall command names pos gp np) command 0 st).2 =
      (none, attempted) := by
    rw [recordLoad_package_exact command names pos gp np st hc]
    simp only [Array.append_empty, Nat.zero_add]
    rw [condTopExpand_unbound_exact (some reader) loaded command pos _ 1 hb hv]
    exact condReadAt_refused_exact reader loaded command pos _ 1 2
      (packageRequest command names pos gp np loaded)
      (packageCall_request_exact command names pos gp np loaded hc hd hsettling)
      (hr _ _)
  change condList _ [] _ #[] _ [] (.ctrl command pos ::
    [.group #[.word names np] gp]) 0 0 st = _
  rw [condList_package_read_step _ command pos _ #[] _ _ [] 0 st attempted
    hc hp hd hflags rfl hex hi]
  rw [condList_literal_group_exact _ names np gp _ #[] _ 1 attempted hi]
  simp [OverlayPrefix.push, OverlayPrefix.ofArray, packageFailed,
    attempted, loaded, packageLoaded, packageRequest, packageCall, Nat.add_assoc]

/-- Execute a parsed file answer in the state of its request, before
continuing the caller. The input wrapper carries its filename and opens
no TeX group; definitions therefore obey the caller's existing scope. -/
public def resumeInput [Monad m] (reader : InputReader m) (context : InputContext)
    (raws : Array Raw) (diags : Array Diag := #[]) : m (Array Raw × InputContext) := do
  let (run, state) ←
    (condList (condTopExpand (some reader)) [] raws #[] (OverlayPrefix.ofArray #[]) [] raws.toList 0 0).run
      { context.state with
        diags := context.state.diags ++ diags
        sourceTriggers := sourceTriggers context.state.file context.state.sourceTriggers raws.toList }
  return (run.raws, { state := state })

/-- Run `act` and put the definition state back as it was: a definition's
text settled for the elaborator is read, not run, so nothing it binds, sets
or defines — globally or not — outlives the reading. -/
private def condSandbox [Monad m] (act : EvalM m CondRun) : EvalM m (Array Raw) := do
  let saved ← get
  let m ← condMark
  let r ← act
  condUnwind m
  write fun st => { st with
    globals := st.globals.shrink m.globals
    loads := saved.loads, deferred := saved.deferred, ignoreSpaces := saved.ignoreSpaces }
  return r.raws

/-- Settle the pending preamble definitions (`CondPending`) against the
state at the preamble's end, which is where the elaborator reads a text no
use the pass sees reaches: each one still in force is walked there, its
decisions named as the definition's, and handed back with where it stands.
The document body begins here. -/
private def condSettle [Monad m] (reader : Option (InputReader m)) :
    EvalM m (Array (String × Pos × Array Raw)) := do
  let pend := (← get).pending
  write fun st => { st with pending := #[], condInDoc := true }
  let mut out : Array (String × Pos × Array Raw) := #[]
  for p in pend do
    match condValueOf (← get).binds p.name with
    | some (some v) =>
      if v.serial == p.serial && v.arity == 0 then
        let file := (← get).file
        write fun st => { st with file := p.file, settling := some p.name }
        let replacement := bindRawArgsList #[] #[] v.raws.toList
        let body ← condSandbox
          (condList (fun n q rs k => condExpandAt reader v.serial v.textSerial true n q rs k)
            [] replacement #[] (OverlayPrefix.ofArray #[]) [] replacement.toList 0 0)
        write fun st => { st with file := file, settling := none }
        out := out.push (p.file, p.pos, body)
    | _ => pure ()
  return out

mutual

-- conserves: none — the walk swaps each settled text in where its
-- definition stands, by design.
/-- Put each settled text (`condSettle`) back into the definition it came out
of, found by its file and position; an `\input` wrapper switches the file,
as `condOne` does. -/
private def condPatchList (texts : Array (String × Pos × Array Raw)) (file : String)
    (acc : Array Raw) : List Raw → Array Raw
  | [] => acc
  | r :: rest => condPatchList texts file (acc.push (condPatchRaw texts file r)) rest

private def condPatchRaw (texts : Array (String × Pos × Array Raw)) (file : String) :
    Raw → Raw
  | .group body p =>
    match texts.find? (fun t => t.1 == file && t.2.1 == p) with
    | some (_, _, b) => .group b p
    | none => .group (condPatchList texts file #[] body.toList) p
  | .env n body p =>
    .env n (condPatchList texts ((Parse.inputEnvFile? n).getD file) #[] body.toList) p
  | .math d body p => .math d (condPatchList texts file #[] body.toList) p
  | .word w p => .word w p
  | .space => .space
  | .par p => .par p
  | .ctrl n p => .ctrl n p
  | .sym c p => .sym c p
  | .verb e s p => .verb e s p

end

/-- Execute one deferred bucket in registration order, in its declaring
files. Its state changes remain in force for the next bucket and the body;
the returned text is translated and placed at that bucket's seam later. -/
private def condReplay [Monad m] (reader : Option (InputReader m))
    (hooks : Array (DeferPoint × String × Pos × Array Raw))
    (point : DeferPoint) : EvalM m (Array (DeferPoint × String × Pos × Array Raw)) := do
  let saved ← get
  write fun st => { st with condReplaying := true, fileTop := false }
  let mut out := #[]
  for (pt, file, pos, body) in hooks do
    if pt == point then
      write fun st => { st with file := file }
      let body ← condList (condTopExpand reader) [] body #[] (OverlayPrefix.ofArray #[]) [] body.toList 0 0
      out := out.push (pt, file, pos, body.raws)
  write fun st => { st with
    file := saved.file, fileTop := saved.fileTop
    condReplaying := saved.condReplaying }
  return out

private theorem condReplay_empty_exact (reader : Option (InputReader Id))
    (point : DeferPoint) (st : St) :
    condReplay reader #[] point st = (#[], { st with writes := st.writes + 2 }) := by
  simp [condReplay,
    bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    write_eq,
    pure, StateT.pure, Nat.add_assoc]

/-- Execute the preamble, its end hooks, the begin-document hooks, then the
body. Stored definitions settle after end-preamble hooks have run. Every
phase reads the same conditional, binding and load state, so a hook reads
and changes that state only at its replay point. -/
private def condDocument [Monad m] (reader : Option (InputReader m))
    (raws : Array Raw) : EvalM m (Array Raw) := do
  let seam := raws.findIdx? (· matches .env "document" _ _)
  let d := seam.getD raws.size
  let pre := raws.extract 0 d
  let post := raws.extract d raws.size
  let pre' ← condList (condTopExpand reader) [] pre #[] (OverlayPrefix.ofArray #[]) [] pre.toList 0 0
  let hooks := (← get).deferred
  let endHooks ← condReplay reader hooks .endPreamble
  let texts ← if seam.isSome then condSettle reader else pure #[]
  let file := (← get).file
  let patch (file : String) (body : Array Raw) :=
    if texts.isEmpty then body else condPatchList texts file #[] body.toList
  let endHooks := endHooks.map fun (pt, f, pos, body) => (pt, f, pos, patch f body)
  let beginHooks ← condReplay reader hooks .beginDocument
  write fun st => { st with deferred := endHooks ++ beginHooks }
  let post' ← condList (condTopExpand reader) [] post #[] (OverlayPrefix.ofArray #[]) [] post.toList 0 0
  return patch file pre'.raws ++ post'.raws

private theorem condDocument_without_seam_exact
    (reader : Option (InputReader Id)) (raws : Array Raw) (st after : St)
    (run : CondRun)
    (hseam : raws.findIdx? (· matches .env "document" _ _) = none)
    (hpre : condList (condTopExpand reader) [] raws #[]
      (OverlayPrefix.ofArray #[]) [] raws.toList 0 0 st = (run, after))
    (hdeferred : after.deferred = #[]) :
    condDocument reader raws st =
      (run.raws, { after with deferred := #[], writes := after.writes + 5 }) := by
  have ht : raws.extract raws.size raws.size = #[] :=
    Array.extract_empty_of_stop_le_start (Nat.le_refl _)
  simp only [condDocument, hseam, Option.getD_none,
    Array.extract_size, ht, bind, StateT.bind, hpre, get, getThe,
    MonadStateOf.get, StateT.get, pure, hdeferred,
    condReplay_empty_exact, Option.isSome_none, Bool.false_eq_true,
    ↓reduceIte, StateT.pure, Array.isEmpty_empty, Array.map_empty,
    Array.empty_append, evalLift_id, write_eq, Array.toList_empty, condList]
  simp only [OverlayPrefix.ofArray, Array.append_empty]

private theorem condDocument_package_failed_exact (reader : InputReader Id)
    (command names : String) (pos gp np : Pos) (st : St)
    (hc : command = "usepackage" ∨ command = "RequirePackage")
    (hp : st.primitiveScopes = #[]) (hd : st.condInDoc = false)
    (hflags : st.flags = {}) (hi : st.ignoreSpaces = false)
    (hsettling : st.settling = none) (hdeferred : st.deferred = #[])
    (hv : condValueOf st.binds command = none)
    (hr : ∀ request context, reader request context = (none, context)) :
    condDocument (some reader) (packageCall command names pos gp np) st =
      (packageCall command names pos gp np,
        { packageFailed command names pos gp np st with writes := st.writes + 10 }) := by
  have hs : (packageCall command names pos gp np).findIdx?
      (· matches .env "document" _ _) = none := by
    simp [packageCall]
  rw [condDocument_without_seam_exact (some reader) _ st _
    { raws := packageCall command names pos gp np, stop := 2 } hs
    (condList_package_failed_exact reader command names pos gp np st
      hc hp hd hflags hi hsettling hv hr) hdeferred]
  simp [packageFailed, packageLoaded, Nat.add_assoc, hdeferred]

/-- A TeX length in the native spelling: `0.75\beat` is `0.75 * beat`,
`\relax` vanishes. Each control word goes through `ref`, told whether an
argument group follows it; `none` from `ref` makes the whole value
unreadable. `\dimexpr … \relax` is its parenthesized expression. -/
public def lengthSrcBy (ref : String → Bool → Option String) (raws : Array Raw) :
    Option String := Id.run do
  let mut s := ""
  let mut prevNumber := false
  let mut depth := 0
  for h : k in [0:raws.size] do
    match raws[k] with
    | .ctrl "relax" _ =>
      if depth > 0 then
        s := s ++ ")"
        depth := depth - 1
    | .ctrl "dimexpr" _ =>
      s := s ++ (if prevNumber then " * (" else "(")
      depth := depth + 1
      prevNumber := false
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
      let some v := ref n (raws[skipSpaces raws (k + 1)]? matches some (.group _ _))
        | return none
      -- A factor against a name multiplies it; a sign before one negates
      -- it, which the native reader spells as a factor too (`-1 * x`).
      let t := s.trimAsciiEnd.toString
      let pre := if prevNumber || t.back.isDigit || t.back == '.' then " * "
        else if t == "-" || t.endsWith "(-" then "1 * " else ""
      s := s ++ pre ++ v
      prevNumber := false
    | .word w _ =>
      s := s ++ w
      prevNumber := w.toList.all fun c => c.isDigit || c == '.'
    | .space => s := s ++ " "
    | other => s := s ++ rawSrcOne other
  -- `\dimexpr` ends with its argument when no `\relax` closes it (e-TeX
  -- manual §3.5: the expression stops at the first token it cannot read).
  return some (s ++ String.ofList (List.replicate depth ')')).trimAscii.toString

/-- A TeX length in the native spelling, every name standing as itself. -/
private def lengthSrc (raws : Array Raw) : String :=
  (lengthSrcBy (fun n _ => some n) raws).getD ""

/-- The parameter a `\setlength` target names: a control word, or TeX's
register reference `\skip\footins` (the skip an insertion holds, TeXbook
ch. 15), read as the name it holds. -/
private def paramName (raws : Array Raw) : Option String :=
  match raws.toList.filter (fun r => match r with | .space => false | _ => true) with
  | [.ctrl n _] => some n
  | [.ctrl "skip" _, .ctrl n _] => some n
  | _ => none

/-- A parameter no engine site reads, named where it is set, once per
parameter: the one door for that loss, whatever spelling set it. -/
private def nameParam (n why : String) (pos : Pos) : M Unit := do
  sayOnce ("ctrl:setlength:" ++ n) .W0104 s!"'\\{n}' is not honoured: it {why}" pos
    -- premise: paramDemoteChecks — a setting in a style file ships the page the
    -- same setting ships from the document, and only its severity moves
    (demote := packageFile (← get).file)

/-- The kernel's three vertical skip amounts, the same in every class
(ltspace.dtx, as plain.tex sets them). -/
public def kernelSkip : String → Option String
  | "smallskipamount" => some "3pt plus 1pt minus 1pt"
  | "medskipamount" => some "6pt plus 2pt minus 2pt"
  | "bigskipamount" => some "12pt plus 4pt minus 4pt"
  | _ => none

/-- Class-independent length defaults the compatibility store can read
before an assignment: the skip amounts and the text-column gap. -/
private def kernelLength (n : String) : Option String :=
  if n == "columnsep" then some s!"{Ir.columnSep.sp.toPtString}pt" else kernelSkip n

/-- A length value as the door reads it where it stands: a kernel parameter
the document set is the value it holds (TeX copies a register's value; the
parameter's own token may not exist, or carry an engine name), a kernel
skip amount is the value the document last set it to, or its fixed value
where it never did (ltspace.dtx sets each once), and any other name is a
token of the document's, read where the declaration reads it. The text
block's measures stand as the engine's own tokens (`\textwidth`,
`\textheight`), read where the class fixes them — so not in a preamble
whose page `measureKnown` denies: a flow class whose page declares no
measure settles its text block after the preamble. `\linewidth` and
`\columnwidth` hold the class's `\textwidth` in a preamble (measured under
lualatex: `0.1\linewidth` is a tenth of it on a one-column page), which is
the engine's where the class fixes its text block at load and never on a
flow page (`flowPage`), whose block is the engine's own; in the body a
line's width is its scope's. Neither has a reading where it is not the
engine's. `none` for what the door
cannot evaluate: a kernel parameter whose value it was never told (the
class sets it), a box's dimension, and a command that computes a length
(`\stretch`, calc's `\widthof`). In a definition's body (`deferred`) the
assignment runs where the command is used, so a kernel parameter is read
there, by its name. -/
private def lenValue (lens : Array (String × String)) (raws : Array Raw)
    (deferred : Bool := false) (preamble : Bool := false) (measureKnown : Bool := true)
    (flowPage : Bool := false) : Option String :=
  -- premise: unreadableLengthChecks — a definition's body names nothing where
  -- it is defined: a kernel parameter there stands by its name
  let kernel (n : String) : Bool := !deferred && (paramSites.lookup n).isSome
  let set (n : String) : Option String := (lens.find? (·.1 == n)).map (·.2)
  let line (n : String) : Bool := n == "linewidth" || n == "columnwidth"
  let held (n : String) : Option String :=
    -- premise: columnGeometryChecks — class defaults are readable register
    -- values too; copying a gap and repeating a macro both read it at use.
    if kernel n then (set n).orElse fun _ => kernelLength n
    else if (kernelSkip n).isSome then
      match set n with
      | some v => if deferred then none else some v
      | none => kernelSkip n
    else none
  -- premise: kernelLengthChecks — under a flow class whose page declares
  -- no measure the elaborator withholds `textwidth` (E0321 on the native
  -- token), and a declared margin offers it
  let unknown (n : String) : Bool :=
    (kernel n && n != "textwidth") || n == "ht" || n == "wd" || n == "dp" ||
      (!deferred && ((line n && (!preamble || flowPage || (set "textwidth").isSome)) ||
        (preamble && !measureKnown && n == "textwidth")))
  let ref (n : String) (arg : Bool) : Option String :=
    if arg then none
    else match held n with
      | some v => some s!"({v})"
      | none => if unknown n then none else some (if line n && !deferred then "textwidth" else n)
  match raws.filter (!· matches .space) with
  | #[.ctrl n _] =>
    -- One name alone copies its value whole, glue included.
    (held n).orElse fun _ => lengthSrcBy ref raws
  | _ => lengthSrcBy ref raws

/-- The names a native length spells, in order: the word runs that start
with a letter or `@` (a package's internal lengths). Units stand against
their digits (`2pt`), so none is one. -/
private def lengthNames (s : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  for c in s.toList ++ [' '] do
    if c.isAlphanum || c == '@' || c == '_' then cur := cur.push c
    else
      if !cur.isEmpty && (cur.front.isAlpha || cur.front == '@') then out := out.push cur
      cur := ""
  return out

/-- Does the declaration reader take `s` as a length, each name in it taken
as declared? Whether a name resolves stays the reader's, where it reads. -/
private def readsAsLength (s : String) : Bool :=
  match Decl.parseValue s ((lengthNames s).map fun n => (n, {})) with
  | some (.glue _) | some (.dim _) => true
  | _ => false

/-- The list parameters a level's style carries: `\leftmargin` its indent,
`\topsep` its opening space, `\itemsep` and `\parsep` its gap between items. -/
private def listCarried : List String := ["leftmargin", "topsep", "itemsep", "parsep"]

/-- What `\list` spends where a list opens (ltlists.dtx: `\@trivlist`'s
`\@topsepadd` from `\topsep` and `\partopsep`, `\parskip\parsep`,
`\leftmargin` and `\rightmargin` into the measure, `\listparindent` into
`\parindent`): set in the list's body, it reaches nothing of the list, and
its group ends it. -/
public def listSpent : List String :=
  ["leftmargin", "rightmargin", "listparindent", "parsep", "topsep", "partopsep"]

/-- What a list's items read as they set (ltlists.dtx: `\@item`'s
`\itemsep` and label box, `\itemindent`, `\labelsep`, `\labelwidth`; and
`\parskip` between paragraphs): set in the list's body, it spaces that one
list. -/
public def listPerItem : List String := ["itemsep", "itemindent", "labelsep", "labelwidth", "parskip"]

/-- Does a body assignment of `n` reach the lists after it in LaTeX? Only
where the document's `\@listi` stands (`listiKept`) and leaves `n` be: a
class's own sets every carried parameter again at every list (size10.clo),
and a deeper level inherits what the outermost left. -/
private def reachesLists (st : St) (n : String) : Bool :=
  listCarried.contains n && st.listiKept &&
    (st.listDefs.find? (·.1 == 1)).any fun (_, _, as) => !as.any (·.name == n)

/-- One length assignment, natively, at the site `paramSites` gives it: a
page property, a token an engine site reads, a list level's indent, or —
where LaTeX's own code sets the value again before anything reads it —
nothing, said so. A parameter no engine site reads is named where it stands,
and a length of the document's own is a token of its name. Inside a
definition nothing is judged: the assignment runs where the command is used,
so it is not the value later arithmetic reads either; everywhere else the
value is recorded, for as long as its group lasts (`rewriteRaw`). -/
private def setLength (n src what : String) (pos : Pos) : M (Array Raw) := do
  let st ← get
  -- premise: registerScopeChecks — an assignment in a definition body or in a
  -- group leaves the value arithmetic after it reads as it was
  unless st.inDef do
    write fun st => { st with lens := (st.lens.filter (·.1 != n)).push (n, src) }
  let preamble ← docPreamble
  let own := s!"\\tokens\{ {n} = {src} }"
  let emit (native : String) : M (Array Raw) := do
    became what native pos
    synthAt native pos
  let nothing (why : String) (tokens : Bool := true) : M (Array Raw) := do
    discard what why s!"setlength:{n}" pos
    if tokens then synthAt own pos else pure #[]
  let named (why : String) : M (Array Raw) := do
    nameParam n why pos
    synthAt own pos
  let list (level : Nat) (kind : String) : String :=
    if level == 1 then kind else s!"{kind}{level}"
  -- premise: listBodyChecks — a list parameter set in a list's body ships
  -- the page the list ships without it, noted where LaTeX discards it too
  if st.inList && !st.inDef && (listSpent.contains n || listPerItem.contains n) then
    if listSpent.contains n then
      return ← nothing "the list spent it where it opened, and it ends with the list"
        (tokens := false)
    let why := match paramSites.lookup n with
      | some (.unmodelled w) => w
      | _ => "spaces this one list; a list here is spaced per level, in the preamble"
    nameParam n why pos
    return #[]
  match (paramSites.lookup n).getD (.token n), st.inDef with
  | .page key, _ =>
    if preamble && key == "textwidth" then write fun st => { st with measureKnown := true }
    if st.inDoc && !st.inDef && key == "textwidth" then
      return ← nothing "'\\begin{document}' set the lines' measure from it, and no later value \
moves a line" (tokens := false)
    emit s!"\\page\{ {key} = {src} }"
  | .token t, _ =>
    unless st.inDef do
      write fun st => { st with localLengths :=
        if st.localLengths.contains t then st.localLengths else st.localLengths.push t }
    -- premise: listLevelChecks — a named body setting under a kept \@listi
    -- ships the page the document ships without it: no list reads it here
    if !st.inDef && !preamble && !st.inList && reachesLists st n then
      named "opens the lists after it, whose level macro leaves it be; a list here opens \
with the space its level sets in the preamble, and only the trivlists after it read it"
    -- A preamble `\topsep` stands until a list runs its `\@list⟨n⟩`, which
    -- sets the length again: only a trivlist outside every list reads it.
    else if !st.inDef && preamble && n == Ir.trivlistSkipName then
      became what s!"\\tokens\{ {t} = {src} }, which a trivlist outside a list reads; \
every list sets '\\topsep' again from its class's parameters" pos
      synthAt s!"\\tokens\{ {t} = {src} }" pos
    else emit s!"\\tokens\{ {t} = {src} }"
  | _, true => emit own
  | .listIndent level, false =>
    if level > 4 then
      nothing "lists here nest four levels, and a deeper one reuses the fourth's"
    else if preamble then
      let styles := s!"\\style\{{list level "itemize"}}\{ indent = {n} }\
\\style\{{list level "enumerate"}}\{ indent = {n} }"
      became what s!"\\style\{{list level "itemize"}}\{ indent = {n} }, and enumerate's" pos
      synthAt (own ++ styles) pos
    else named "indents the lists after it; a list's indent here is declared in the preamble"
  | .sizeReset body, false =>
    if preamble then
      nothing "'\\begin{document}' runs '\\normalsize', which sets it again"
        (tokens := !(body matches .token _))
    else match body with
      | .token t => emit s!"\\tokens\{ {t} = {src} }"
      | .unmodelled why => named why
      | _ => emit own
  | .listReset, false =>
    if preamble then
      write fun st => { st with listResets := st.listResets.push (n, what, st.file, pos) }
      synthAt own pos
    else if reachesLists st n then
      -- premise: listLevelChecks — a named body setting under a kept \@listi
      -- ships the page the document ships without it: no list reads it here
      named "spaces the lists after it, whose level macro leaves it be; a list here is \
spaced per level, in the preamble"
    else
      nothing s!"the next list sets '\\{n}' again from its class's parameters, so no list reads it"
  | .unmodelled why, false =>
    if n == "parindent" && Decl.parseGlue src == some {} then
      nothing "paragraphs here are set flush, as declared"
    else named why

/-- The one warning for a length assignment the door cannot read (`shown`,
the value as written): named once per parameter, and skipped, the length
keeping what it held, as though no assignment took place. -/
private def unreadableLength (n shown : String) (pos : Pos) : M (Array Raw) := do
  sayOnce ("ctrl:setlength:" ++ n ++ ":value") .W0104
    s!"'\\{n}' is set to '{shown}', a value this engine cannot read: skipped, and \
the length keeps its value" pos
    -- premise: unreadableLengthChecks — each LaTeX-valid spelling the door
    -- cannot read builds with this one warning, and ships the page it shipped
    -- without the setting
    (demote := packageFile (← get).file)
  return #[]

/-- A length value as the assignment door reads it where it stands:
`lenValue`, then the declaration reader's own test. `none` for a value the
door cannot read. -/
private def doorValue? (value : Array Raw) : M (Option String) := do
  let st ← get
  return (lenValue st.lens value st.inDef (!st.inDoc && !st.seam) st.measureKnown
    st.flowPage).filter readsAsLength

/-- A length assignment from its value's raws (`\setlength`, TeX's own
`\parskip 6pt`): read at the door and landed by `setLength`, or named and
skipped (`unreadableLength`). -/
private def assignLength (n : String) (value : Array Raw) (what : String) (pos : Pos) :
    M (Array Raw) := do
  if let some src ← doorValue? value then return ← setLength n src what pos
  unreadableLength n (rawSrc value).trimAscii.toString pos

/-- A document macro used in a list's body whose definition is length
settings and nothing else — pandoc's `\tightlist`,
`\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}` — as the settings it
stands for: TeX expands it where it stands, so they are the list's own
(`setLength`'s list arm). The definition is the one the conditional pass
recorded; `none` for any other body, which the elaborator expands. -/
private def listSettings? (st : St) (name : String) : Option (Array (String × Array Raw)) :=
  if !st.inList || st.inDef then none
  else match st.binds[name]? with
    | some (some v) =>
      if v.arity == 0 then go (v.raws.filter (!· matches .space)).toList #[] else none
    | _ => none
where
  go : List Raw → Array (String × Array Raw) → Option (Array (String × Array Raw))
    | [], acc => if acc.isEmpty then none else some acc
    | .ctrl "setlength" _ :: .group t _ :: .group v _ :: rest, acc =>
      (paramName t).bind fun n => go rest (acc.push (n, v))
    | _, _ => none

/-- A length operand the rewrite evaluates: a literal (`2pt`, `-2pt`), or a
length whose value it set, negated or not. -/
private def lenOperand (lens : Array (String × String)) : List Raw → Option String
  | [.word w _] => (Decl.parseLength w).map fun _ => w
  | [.sym '-' _, .word w _] => (Decl.parseLength ("-" ++ w)).map fun _ => "-" ++ w
  | [.ctrl y _] => (lens.find? (·.1 == y)).map fun (_, v) => s!"({v})"
  | [.sym '-' _, .ctrl y _] => (lens.find? (·.1 == y)).map fun (_, v) => s!"-({v})"
  | [.word "-" _, .ctrl y _] => (lens.find? (·.1 == y)).map fun (_, v) => s!"-({v})"
  | _ => none

/-- A unit or glue keyword inside a value (plain.tex's `\p@` and `\z@`,
ltdefns.dtx's `\@plus` and `\@minus`), never a register. -/
private def valueCtrl (n : String) : Bool :=
  n == "p@" || n == "z@" || n == "@plus" || n == "@minus"

private def isSign : Raw → Bool
  | .sym '-' _ | .sym '+' _ | .word "-" _ | .word "+" _ => true
  | _ => false

/-- Where one dimension ends: an optional sign, then a factor with its unit
(`4pt`, `2\p@`, `2 pt`), a factor of a register (`.5\leftmargin`), or a
register alone. -/
private def dimenEnd (raws : Array Raw) (i : Nat) : Nat :=
  let i := skipSpaces raws i
  let i := if (raws[i]?.map isSign).getD false then skipSpaces raws (i + 1) else i
  match raws[i]? with
  | some (.ctrl _ _) => i + 1
  | some (.word w _) =>
    if w.toList.any Char.isAlpha then i + 1
    else
      let j := skipSpaces raws (i + 1)
      match raws[j]? with
      | some (.ctrl _ _) => j + 1
      | some (.word u _) => if u.toList.all Char.isAlpha then j + 1 else i + 1
      | _ => i + 1
  | _ => i

/-- Past an optional glue keyword (`plus`, or its sanitised `\@plus`) and
the dimension after it. -/
private def afterKey (raws : Array Raw) (k : Nat) (key : String) : Nat :=
  let j := skipSpaces raws k
  match raws[j]? with
  | some (.ctrl c _) => if c == "@" ++ key then dimenEnd raws (j + 1) else k
  | some (.word w _) => if w == key then dimenEnd raws (j + 1) else k
  | _ => k

/-- Where a glue value ends: a register it copies (`\itemsep \parsep`), or
a dimension with its optional `plus` and `minus` parts. -/
private def glueEnd (raws : Array Raw) (i : Nat) : Nat :=
  let i := skipSpaces raws i
  let rubber (k : Nat) : Nat := afterKey raws (afterKey raws k "plus") "minus"
  match raws[i]? with
  | some (.ctrl r _) => if valueCtrl r then rubber (i + 1) else i + 1
  | _ =>
    let d := dimenEnd raws i
    if d == i then i else rubber d

/-- The parameter assignments `raws` spells from `i`, in order, and where
they stop: at the end, or at the first construct that assigns no length
parameter `paramSites` knows. -/
private def readAssigns (raws : Array Raw) (i : Nat) : Array TexAssign × Nat := Id.run do
  let mut out : Array TexAssign := #[]
  let mut j := skipSpaces raws i
  for _ in [0:raws.size] do
    match raws[j]? with
    | some (.ctrl "advance" _) =>
      let t := skipSpaces raws (j + 1)
      let some (.ctrl n _) := raws[t]? | break
      let v0 := skipSpaces raws (t + 1)
      let v0 := if raws[v0]? matches some (.word "by" _) then v0 + 1 else v0
      let e := glueEnd raws v0
      if e ≤ v0 then break
      out := out.push { name := n, add := true, value := raws.extract v0 e }
      j := skipSpaces raws e
    | some (.ctrl n _) =>
      if (paramSites.lookup n).isNone then break
      let v0 := skipSpaces raws (j + 1)
      let v0 := if raws[v0]? matches some (.sym '=' _) then v0 + 1 else v0
      let e := glueEnd raws v0
      if e ≤ v0 then break
      out := out.push { name := n, add := false, value := raws.extract v0 e }
      j := skipSpaces raws e
    | _ => break
  return (out, j)

/-- Past the spaces and the optional `=` before a TeX assignment's value. -/
private def skipEq (raws : Array Raw) (i : Nat) : Nat :=
  let j := skipSpaces raws i
  match raws[j]? with
  | some (.sym '=' _) | some (.word "=" _) => skipSpaces raws (j + 1)
  | _ => j

/-- The display skips a redefined `\normalsize` assigns from `start`, each
read through the length door in order, as TeX runs the body: a skip copied
from one the body set earlier is that value, one it cannot read — a copy of
a skip the class set — is named once and skipped (`unreadableLength`).
All four a display reads are taken, the short pair with the long
(`Ir.displaySkipsFor`). -/
private def sizeSkips (body : Array Raw) (start : Nat) (pos : Pos) : M (Array String) := do
  let mut lens := (← get).lens
  let known := (← get).measureKnown
  let flow := (← get).flowPage
  let mut out : Array String := #[]
  for a in (readAssigns body start).1 do
    if !a.add && (paramSites.lookup a.name) matches some (.sizeReset (.token _)) then
      if let some src := (lenValue lens a.value (preamble := true) (measureKnown := known)
          (flowPage := flow)).filter readsAsLength then
        out := out.push s!"{a.name} = {src}"
        lens := (lens.filter (·.1 != a.name)).push (a.name, src)
      else
        let _ ← unreadableLength a.name (rawSrc a.value).trimAscii.toString pos
        pure ()
  return out

/-- The raw standing before index `i`, spaces skipped. -/
private def rawBefore (raws : Array Raw) (i : Nat) : Option Raw := Id.run do
  let mut k := i
  for _ in [0:i] do
    k := k - 1
    match raws[k]? with
    | some .space => pure ()
    | r => return r
  return none

/-- Does the raw standing before a register read it as an operand, so no
assignment opens there (TeXbook ch. 20 and 24)? A command that reads a
dimension or a number next (`\hskip`, `\ifdim`, `\the`), a keyword that
does (`by`, `plus`, `to`), a factor (`2`, `.5`), a sign, or a relation. -/
private def readsOperand : Option Raw → Bool
  | some (.ctrl c _) => ["hskip", "vskip", "kern", "mskip", "mkern", "the", "showthe",
      "advance", "multiply", "divide", "ifdim", "ifnum", "ifodd", "ifcase", "dimexpr",
      "glueexpr", "numexpr", "muexpr", "raise", "lower", "moveleft", "moveright"].contains c
  | some (.word w _) =>
    ["by", "plus", "minus", "to", "spread", "width", "height", "depth", "=", "<", ">"].contains w ||
      (!w.isEmpty && w.toList.all fun ch => ch.isDigit || ch == '.' || ch == '-' || ch == '+')
  | some (.sym c _) => "=<>+-*/(".toList.contains c
  | _ => false

/-- TeX's own assignment to a kernel parameter, when the control word
`name`, read up to `start`, opens one (TeXbook ch. 24:
⟨variable⟩[=]⟨value⟩, as `\parskip 6pt plus 1pt`, `\parskip=0pt` and
`\parindent\z@` spell it): the value's raws and where it ends. The value
starts with `=`, a number or a register; a parameter read as an operand
(`readsOperand`: after `\hskip` or `\ifdim`, after a factor) opens none. -/
private def plainAssign? (name : String) (raws : Array Raw) (start : Nat) :
    Option (Array Raw × Nat) :=
  if (paramSites.lookup name).isNone then none
  else if readsOperand (rawBefore raws (start - 1)) then none
  else
    let j := skipSpaces raws start
    -- The lexer keeps an `=` against the word it opens (`=6pt`).
    let (eq, raws) := match raws[j]? with
      | some (.sym '=' _) | some (.word "=" _) => (true, raws)
      | some (.word w p) =>
        if w.startsWith "=" && w.length > 1 then (true, raws.set! j (.word (w.drop 1).toString p))
        else (false, raws)
      | _ => (false, raws)
    let v0 := skipEq raws start
    let opens := eq || match raws[v0]? with
      | some (.word w _) => w.front.isDigit || w.front == '.' || w.front == '-'
      | some (.sym c _) => c == '-' || c == '+'
      | some (.ctrl c _) => valueCtrl c || (paramSites.lookup c).isSome
      | _ => false
    let e := glueEnd raws v0
    if opens && e > v0 then some (raws.extract v0 e, e) else none

/-- The list depth a class's parameter macro sets up: `\@listi` to
`\@listvi` (size10.clo), the one `\list` calls for its depth (ltlists.dtx). -/
private def listLevelOf : String → Option Nat
  | "@listi" => some 1
  | "@listii" => some 2
  | "@listiii" => some 3
  | "@listiv" => some 4
  | "@listv" => some 5
  | "@listvi" => some 6
  | _ => none

/-- Does a body run `\let\@listi\@listI`, a class `\normalsize`'s reset of
the outermost list level (size10.clo)? -/
private def resetsListi (body : Array Raw) : Bool :=
  let xs := body.toList.filter (!· matches .space)
  (xs.zip xs.tail).any fun p => (p.1 matches .ctrl "let" _) && (p.2 matches .ctrl "@listi" _)

/-- A redefined list-level macro whose body is parameter assignments only:
recorded for the level, as `\list` runs it where a list of that depth opens,
with each parameter no engine site reads named once. `false` for any other
body, which the definer reads as it reads every definition. -/
private def listLevelDef (level : Nat) (what : String) (body : Array Raw) (pos : Pos) :
    M Bool := do
  let (assigns, stop) := readAssigns body 0
  if stop < body.size || assigns.isEmpty then return false
  write fun st => { st with
    listDefs := (st.listDefs.filter (·.1 != level)).push (level, pos, assigns) }
  for n in (assigns.map (·.name)).toList.eraseDups do
    if let some (.unmodelled why) := paramSites.lookup n then nameParam n why pos
    else if assigns.any (fun a => a.add && a.name == n) && listCarried.contains n then
      sayOnce "ctrl:advance" .W0104
        s!"TeX register arithmetic ('\\advance') is not supported; skipped" pos
  became what s!"the level-{level} list parameters, set where a list that deep opens" pos
  return true

/-- A list-level value as one native operand: the running value of the
parameter it copies, a length the document set (a token of its name), or a
literal glue; `none` for anything else. -/
private def listOperand (run : List (String × Option String)) (lens : Array (String × String))
    (value : Array Raw) : Option String :=
  match value.toList.filter (!· matches .space) with
  | [.ctrl r _] =>
    if valueCtrl r then some (lengthSrc value)
    else match run.lookup r with
      | some o => o
      | none => if lens.any (·.1 == r) then some r else none
  | vs =>
    if vs.all (fun x => match x with | .ctrl c _ => valueCtrl c | _ => true)
    then some (lengthSrc value) else none

/-- Each list level a redefined macro sets, as LaTeX's `\list` computes it
where a list of that depth opens (ltlists.dtx): the level's assignments over
the values the enclosing level left — the preamble's, for the outermost. A
level the class's own macro sets up leaves its values the class's, so what a
deeper level inherits from it is not known here and not written; the
outermost is the class's unless the document's `\normalsize` keeps the
preamble's `\@listi` (`listiKept`). The known values become the level's
style, for both list kinds, and each preamble assignment to a parameter a
level sets again is said to reach the lists it reaches, or none. -/
private def flushListLevels : M (Array Raw) := do
  let st ← get
  -- premise: listLevelChecks — a class's \normalsize resets \@listi, so the
  -- document's redefinition ships the page the document ships without it
  let defOf (level : Nat) : Option (Pos × Array TexAssign) :=
    if level == 1 && !st.listiKept then none
    else (st.listDefs.find? (·.1 == level)).map fun (_, p, a) => (p, a)
  -- What the preamble set, where the outermost list opens, is the list's
  -- only when its level macro is the document's and leaves the parameter be.
  let outer := (defOf 1).map (·.2)
  for (n, what, file, pos) in st.listResets do
    write fun st => { st with file := file }
    match outer with
    | some assigns =>
      if assigns.any (·.name == n) then
        discard what s!"the outermost lists' parameters set '\\{n}' again" s!"setlength:{n}" pos
      else became what s!"the outermost lists' '\\{n}', which their parameters leave be" pos
    | none =>
      discard what s!"every list sets '\\{n}' again from its class's parameters, so no list reads it"
        s!"setlength:{n}" pos
  write fun s => { s with file := st.file }
  if st.listDefs.isEmpty then return #[]
  let lens := st.preLens.getD st.lens
  let preamble (n : String) : Option String := if lens.any (·.1 == n) then some n else none
  let mut run : List (String × Option String) := listCarried.map fun n => (n, preamble n)
  let mut out : Array Raw := #[]
  for level in [1:5] do
    match defOf level with
    | none => run := listCarried.map fun n => (n, none)
    | some (pos, assigns) =>
      for a in assigns do
        if listCarried.contains a.name then
          let v := if a.add then none else listOperand run lens a.value
          run := run.map fun (n, o) => if n == a.name then (n, v) else (n, o)
      let op (n : String) : Option String := (run.lookup n).bind id
      let r := (["i", "ii", "iii", "iv"][level - 1]?).getD ""
      let mut native := ""
      let mut keys : Array String := #[]
      if let some v := op "leftmargin" then keys := keys.push s!"indent = {v}"
      if let some v := op "topsep" then keys := keys.push s!"before = {v}"
      if let (some i, some p) := (op "itemsep", op "parsep") then
        native := s!"\\tokens\{ itemsep{r} = {i}, parsep{r} = {p} }"
        keys := keys.push s!"gap = itemsep{r} + parsep{r}"
      unless keys.isEmpty do
        for kind in ["itemize", "enumerate"] do
          let el := if level == 1 then kind else s!"{kind}{level}"
          native := native ++ s!"\\style\{{el}}\{ {String.intercalate ", " keys.toList} }"
        out := out ++ (← synthAt native pos)
  return out

/-- A TeX length from option text: `3\\gapunit` is `3 * gapunit`, `\\x` is `x`. -/
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

/-- The output drivers geometry and crop choose among (geometry manual §5.1,
"Driver options"; crop.dtx's driver options): each says how a DVI or PDF
backend is handed the paper size and the marks, which this engine — its
own PDF writer — decides itself. So a driver option, under any value, asks
for nothing the page shows, and it passes without a loss to name. -/
private def driverOptions : List String :=
  ["dvips", "dvipdfm", "dvipdfmx", "dvisvgm", "pdftex", "luatex", "xetex", "vtex", "driver"]

/-- `\usepackage[opts]{geometry}`, `\geometry{...}`, `\newgeometry{...}`
→ `\page{...}`. `textwidth`/`textheight` pass through to the `\page` keys
of the same names (geometry manual §5.2: they size the body; the engine
centres it — geometry's own oneside `hmarginratio` 1:1). `headsep` and
`footskip` pass through too, carrying their LaTeX baseline semantics to
the page model (`Layout.furnGapOfSep` for the head, `Layout.latexFootY`
for the foot); `headheight` is satisfied
by construction — the head's band reserves its line's whole ink
(`Layout.bodyTop_clears_head`), which is what a declared `headheight`
exists to guarantee. The one-sided margins `top`/`bottom` and
`left`/`right` map when the pair agrees (the engine's page model has one
margin per axis) and are dropped named when it does not. -/
private def geometry (opts : String) (pos : Pos)
    (spelling : String := "\\usepackage{geometry}") : M (Array Raw) := do
  let mut keys : Array String := #[]
  let mut dropped : Array String := #[]
  let mut droppedExpr : Array String := #[]
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
      -- premise: driverOptionChecks — a driver option or `verbose` ships
      -- the page the document ships without it
      else if driverOptions.contains f || f == "verbose" then pure ()
      else dropped := dropped.push f
    | k :: v =>
      let k := k.trimAscii.toString
      let v := (String.intercalate "=" v).trimAscii.toString
      -- geometry's width/height size the text block, paperwidth/paperheight
      -- the page (geometry manual §5.2); \page speaks in page dimensions.
      let k := if k == "paperwidth" then "width" else if k == "paperheight" then "height" else k
      -- A `\dimexpr` is TeX arithmetic `lengthOfTeX` cannot carry (its
      -- operands may be registers, `\ht\strutbox` in the wild): mapping it
      -- would synthesize an unreadable `\page` value and turn a named drop
      -- into an error. It stays a drop, and the warning names the spelling
      -- — for a key the engine otherwise reads, "footskip" alone would
      -- point the author at the wrong half of the assignment.
      -- premise: driverOptionChecks — a driver option or `verbose` ships
      -- the page the document ships without it
      if driverOptions.contains k || k == "verbose" then pure ()
      else if v.startsWith "\\dimexpr" then
        droppedExpr := droppedExpr.push s!"{k} = {v}"
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
  if keys.any fun k => ["margin =", "hmargin =", "textwidth ="].any (k.startsWith ·) then
    write fun st => { st with measureKnown := true }
  became spelling native pos
  unless dropped.isEmpty do
    say .W0101 s!"geometry keys without a native equivalent were dropped: \
{String.intercalate ", " dropped.toList}" pos
  unless droppedExpr.isEmpty do
    say .W0101 s!"geometry values the engine cannot evaluate were dropped: \
{String.intercalate ", " droppedExpr.toList}" pos
      (help := "TeX register arithmetic has no value here; write the \
length as one literal")
  synthAt native pos

/-- `\usepackage[opts]{crop}` and `\crop[opts]` → `\page{ marks = cut }`.
crop's `cam` style is the one the engine draws — derived from the trim
and bleed instead of enlarging the sheet, so a trim+bleed submission
keeps its dimensions — and `off` is the declared way back
(`marks = none`). Every other option is dropped named (W0101):
`cross`/`frame` are mark styles the engine does not draw, the sheet
sizes and `center` enlarge the medium around the page (this engine's
medium is trim plus the declared `\page{ bleed }`), and `info`/`noinfo`,
`axes`, and the physical transforms (`mirror`, `rotate`, `invert`,
`notext`) configure machinery the engine does not model. `noaxes` asks
for the state the engine is already in, and a driver name
(`driverOptions`) for nothing the page shows; both pass silently. Option
list: crop.dtx v1.10 (Melchior Franz). -/
private def crop (opts : String) (pos : Pos)
    (spelling : String := "\\usepackage{crop}") (key : String := "usepackage:crop") :
    M (Array Raw) := do
  let mut mode : Option Bool := none
  let mut dropped : Array String := #[]
  for e in Decl.splitEntries opts do
    let o := ((e.splitOn "=").headD "").trimAscii.toString
    if o == "cam" then mode := some true
    else if o == "off" then mode := some false
    else if o == "noaxes" then pure ()
    -- premise: driverOptionChecks — a driver option ships the page the
    -- document ships without it
    else if driverOptions.contains o then pure ()
    else if !o.isEmpty then dropped := dropped.push o
  unless dropped.isEmpty do
    say .W0101 s!"crop options without a native equivalent were dropped: \
{String.intercalate ", " dropped.toList}" pos
  match mode with
  | some on =>
    let native := s!"\\page\{ marks = {if on then "cut" else "none"} }"
    became spelling native pos
    synthAt native pos
  | none =>
    discard spelling "crop draws no marks until an option asks for them" key pos
    return #[]

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

/-- `\hypersetup{pdfauthor=..., pdftitle=...}` → `\pdfmeta{...}`, and its link
colours (`colorlinks`, `linkcolor`, `urlcolor`, `citecolor`, `allcolors`,
`hidelinks`) → the link kinds' `\style` colours (`LinkSetup.native`). The
other rendering hints (`pdfborder`, a viewer's frame) have no meaning and go
quietly. -/
private def hypersetup (opts : String) (pos : Pos) : M (Array Raw) := do
  let mut keys : Array String := #[]
  let mut links := (← get).links
  let mut linked := false
  for e in Decl.splitEntries opts do
    match e.splitOn "=" with
    | k :: v =>
      let k := k.trimAscii.toString
      let v := (String.intercalate "=" v).trimAscii.toString
      let v := if v.startsWith "{" && v.endsWith "}" then
        (v.drop 1).dropEnd 1 |>.toString else v
      for m in ["title", "author", "subject", "keywords"] do
        if k == "pdf" ++ m then keys := keys.push s!"{m} = \"{v}\""
      if let some l := links.read k v then
        links := l
        linked := true
    | [] => pure ()
  if linked then write fun st => { st with links }
  let native := s!"\\pdfmeta\{ {String.intercalate ", " keys.toList} }" ++
    (if linked then links.native else "")
  became "\\hypersetup" native pos
  synthAt native pos

/-- `\DocumentMetadata{...}` (usrguide, "Document metadata"; ltdocinit):
`lang` is the document's language and lands on the same `\pdfmeta{
language }` door babel's main language uses, and `pdfversion` on
`\pdfmeta{ version }` when it names a version the writer writes (1.7 or
2.0). The other writer keys (`pdfstandard`, `uncompress`, `testphase`, …)
configure a PDF writer the engine is not, so each is dropped by name, never
silently, and never as page content. -/
private def documentMetadata (opts : String) (pos : Pos) : M (Array Raw) := do
  let mut lang : Option String := none
  let mut version : Option String := none
  let mut dropped : Array String := #[]
  for e in Decl.splitEntries opts do
    match Decl.splitEntry e with
    | some ("lang", v) => lang := some v
    | some ("pdfversion", v) =>
      if v == "1.7" || v == "2.0" then version := some v else dropped := dropped.push "pdfversion"
    | some (key, _) => if !key.isEmpty then dropped := dropped.push key
    | none =>
      let key := e.trimAscii.toString
      if !key.isEmpty then dropped := dropped.push key
  unless dropped.isEmpty do
    say .W0101 s!"\\DocumentMetadata keys without a native equivalent were \
dropped: {String.intercalate ", " dropped.toList}" pos
      (help := "the engine writes PDF 2.0, or 1.7 when 'pdfversion=1.7' asks; \
standard and compression keys have no effect here")
  let keys := (lang.map fun tag => s!"language = \"{tag}\"").toArray ++
    (version.map fun v => s!"version = \"{v}\"").toArray
  if keys.isEmpty then return #[]
  let native := s!"\\pdfmeta\{ {String.intercalate ", " keys.toList} }"
  became "\\DocumentMetadata" native pos
  synthAt native pos

/-- `\AddToHook{hook}[label]{code}` (usrguide, "Hooks"): code onto a kernel
hook. The engine has no hook machinery — what a page shows is declared,
not accumulated by hook code — so the construct skips whole: hook name,
label, and body, never leaking the code as text. -/
private def addToHook (pos : Pos) : M Unit :=
  sayOnce "ctrl:AddToHook" .W0104
    "'\\AddToHook' registers code on a kernel hook; the engine has no \
hook machinery; skipped" pos

/-- Does hook code assign a page attribute (`\pdfvariable pageattr` or
`\pdfpageattr`)? That is how a document declares its page boxes at
shipout — values the engine cannot evaluate when an `\edef` computes them,
but a declaration all the same (`Ir.PageSpec.trimMarked`). -/
private def assignsPageAttr (code : Array Raw) : Bool :=
  let toks := code.filter fun r => !(r matches .space)
  toks.any (· matches .ctrl "pdfpageattr" _) ||
    (List.range toks.size).any fun i => match toks[i]?, toks[i + 1]? with
      | some (.ctrl "pdfvariable" _), some (.word "pageattr" _) => true
      | _, _ => false

/-- A shipout picture flattened to TeX's own shape, a token stream with its
group and environment brackets explicit, so reading it is one pass over a
sequence rather than a recursion over what drawing macros expand to. -/
private inductive PicTok where
  | ctrl (n : String)
  | chr (c : Char)
  | bgroup
  | egroup
  | benv (n : String)
  | eenv (n : String)
  | other
  deriving Inhabited, BEq

mutual
/-- The flat stream of a raw list; a control word goes through `onCtrl`,
which is where a drawing macro's body may be spliced. -/
private def picFlatList (onCtrl : String → Array PicTok → Array PicTok) :
    List Raw → Array PicTok → Array PicTok
  | [], acc => acc
  | r :: rest, acc => picFlatList onCtrl rest (picFlatOne onCtrl r acc)
termination_by structural l _ => l

private def picFlatOne (onCtrl : String → Array PicTok → Array PicTok) :
    Raw → Array PicTok → Array PicTok
  | .word w _, acc => w.toList.foldl (fun a c => a.push (.chr c)) acc
  | .sym c _, acc => acc.push (.chr c)
  | .space, acc => acc
  | .par _, acc => acc
  | .ctrl n _, acc => onCtrl n acc
  | .group body _, acc => (picFlatList onCtrl body.toList (acc.push .bgroup)).push .egroup
  | .env n body _, acc =>
    (picFlatList onCtrl body.toList (acc.push (.benv n))).push (.eenv n)
  | _, acc => acc.push .other
termination_by structural r _ => r
end

/-- A picture length as a native expression: `\dimexpr` and `\relax` are
TeX's brackets around the arithmetic, a coefficient against a name is a
product (`0.5\x` is `0.5 * x`), and a name is a declared length or nothing
this reading takes. -/
private def picExpr (lengths : Array String) (ts : Array PicTok) : Option String := Id.run do
  let mut s := ""
  let mut prevNum := false
  for t in ts do
    match t with
    | .ctrl "dimexpr" | .ctrl "relax" => pure ()
    | .ctrl n =>
      unless lengths.contains n do return none
      s := s ++ (if prevNum then " * " else "") ++ n
      prevNum := false
    | .chr c =>
      s := s.push c
      prevNum := c.isDigit || c == '.'
    | _ => return none
  let out := s.trimAscii.toString
  return some (if out.isEmpty then "0pt" else out)

/-- An offset added to an origin, both native expressions. -/
private def picShift (origin e : String) : String :=
  if e.startsWith "-" then s!"({origin}) - ({(e.drop 1).toString})" else s!"({origin}) + ({e})"

/-- **A shipout picture's rules** (the kernel's `shipout/background` and
`shipout/foreground` pictures, whose reference point is the page's top-left
corner, y up): `\put(x,y){...}` moves the reference point for its group,
`\color{c}` inks the rest of its group, `\rule{w}{h}` stands with its
lower-left corner on the point, a `picture` environment opens a group at
the point, and a drawing macro — a parameterless definition whose body
draws — is read one level deep, where shipout expands it. Each rule is
`(x, y, w, h, colour)` in native expressions over the lengths the document
declared (`lengths`). Anything else — text, another command, a picture
offset, a length the document never declared — reads nothing: `none`, and
the hook stays skipped by name. -/
private def shipoutRules (look : String → Option (Array Raw)) (lengths : Array String)
    (code : Array Raw) : Option (Array (String × String × String × String × String)) := Id.run do
  let flat0 := picFlatList (fun n acc => acc.push (.ctrl n))
  let draws (body : Array Raw) : Bool :=
    (flat0 body.toList #[]).any fun t => t == .ctrl "put" || t == .ctrl "rule"
  let toks := picFlatList (fun n acc => match look n with
    | some body => if draws body then flat0 body.toList acc else acc.push (.ctrl n)
    | none => acc.push (.ctrl n)) code.toList #[]
  -- the frame stack: each open group's reference point and ink
  let mut stack : Array (String × String × String) := #[("0pt", "0pt", "black")]
  let mut mode : Nat := 0
  let mut buf : Array PicTok := #[]
  let mut first : Array PicTok := #[]
  let mut name := ""
  let mut rules : Array (String × String × String × String × String) := #[]
  for t in toks do
    let (ox, oy, ink) := stack.back?.getD ("0pt", "0pt", "black")
    if mode == 13 then
      -- after a picture's size: an offset pair is a reference point this
      -- reading does not move
      if t == .chr '(' then return none
      mode := 0
    match mode with
    | 0 =>
      match t with
      | .ctrl "put" => mode := 1
      | .ctrl "color" => mode := 5
      | .ctrl "rule" => mode := 7
      | .ctrl "relax" => pure ()
      | .bgroup => stack := stack.push (ox, oy, ink)
      | .egroup =>
        if stack.size ≤ 1 then return none
        stack := stack.pop
      | .benv "picture" =>
        stack := stack.push (ox, oy, ink)
        mode := 11
      | .eenv "picture" =>
        if stack.size ≤ 1 then return none
        stack := stack.pop
      | _ => return none
    | 1 =>
      unless t == .chr '(' do return none
      buf := #[]
      mode := 2
    | 2 =>
      if t == .chr ',' then
        first := buf
        buf := #[]
        mode := 3
      else if t == .chr ')' || t == .bgroup || t == .egroup then return none
      else buf := buf.push t
    | 3 =>
      if t == .chr ')' then
        let (some px, some py) := (picExpr lengths first, picExpr lengths buf) | return none
        first := #[]
        buf := #[]
        stack := stack.push (picShift ox px, picShift oy py, ink)
        mode := 4
      else if t == .bgroup || t == .egroup then return none
      else buf := buf.push t
    | 4 =>
      unless t == .bgroup do return none
      mode := 0
    | 5 =>
      unless t == .bgroup do return none
      name := ""
      mode := 6
    | 6 =>
      match t with
      | .chr c => name := name.push c
      | .egroup =>
        stack := stack.pop.push (ox, oy, name.trimAscii.toString)
        mode := 0
      | _ => return none
    | 7 =>
      unless t == .bgroup do return none
      buf := #[]
      mode := 8
    | 8 =>
      if t == .egroup then
        first := buf
        buf := #[]
        mode := 9
      else if t == .bgroup then return none
      else buf := buf.push t
    | 9 =>
      unless t == .bgroup do return none
      buf := #[]
      mode := 10
    | 10 =>
      if t == .egroup then
        let (some w, some h) := (picExpr lengths first, picExpr lengths buf) | return none
        rules := rules.push (ox, oy, w, h, ink)
        first := #[]
        buf := #[]
        mode := 0
      else if t == .bgroup then return none
      else buf := buf.push t
    | 11 =>
      unless t == .chr '(' do return none
      mode := 12
    | 12 => if t == .chr ')' then mode := 13
    | _ => return none
  -- the stream ends where it began: every group closed, no command half read
  if (mode == 0 || mode == 13) && stack.size == 1 then return some rules else return none

/-- Internal marker prefix for xcolor's page-ground epoch. -/
public def pageColorMarkPrefix : String := "@pagecolor:"

/-- `\pagecolor[model]{colour}` sets the page background from here on
(xcolor manual §2.6). The source rides intact to the typed resolver; keeping
this distinct from `\palette{bg=...}` lets `\nopagecolor` restore the
document/class ground that existed before page colour was applied. -/
private def pageColor (value : String) (pos : Pos) : M (Array Raw) := do
  became "\\pagecolor" s!"the {value} page-ground epoch" pos
  return #[.ctrl (pageColorMarkPrefix ++ value) pos]

private def modeledColorSource (model : Option String) (value : String) : String :=
  match model with
  | some m => s!"{m.trimAscii.toString}({value})"
  | none => value

/-- Internal marker for xcolor's global page-ground reset. `@` is not a
surface control-word character, so a document cannot forge the transition. -/
public def pageColorResetMark : String := "@pagecolor-reset"

/-- KOMA's `\\sectionlinesformat` is a hook for drawing after a heading. The one
idiom worth reading is a rule in a colour, `\\textcolor{X}{\\leaders\\hrule …}`;
any other non-empty body is a dropped loss and says so — an empty body asks
for no decoration, which is what an unstyled section already draws. The
rule's geometry is read with its colour: `\\hrule` has zero depth, so its
bottom edge is the heading's baseline (`rule-position = baseline`), and
its `height` — TeX's 0.4 pt when none is written (TeXbook p. 221) — is the
thickness. The height reaches `\\style` as written (`\\p@` spelled `pt`), so
an unreadable one is E0321 there, never a silent default; a `depth` or
`width` is not the idiom. -/
private def sectionRule (src : String) (pos : Pos) : M (Array Raw) := do
  let dropped (why : String) : M (Array Raw) := do
    if src.trimAscii.toString.isEmpty then
      -- An empty body asks for no decoration: deliberate, and said so —
      -- the silence guard (W0387) takes wordless consumption for a drop.
      discard "\\sectionlinesformat" "an empty body asks for no decoration"
        "sectionlinesformat" pos
    else
      say .E0113 s!"'\\sectionlinesformat' body is not the rule idiom{why}; it is dropped" pos
        (help := "\\style{section}{ rule = <colour> } declares the section \
rule; \\allow{E0113} accepts the loss")
    return #[]
  match (src.splitOn "\\textcolor {")[1]? with
  | some rest =>
    let color := ((rest.splitOn "}").headD "").trimAscii.toString
    match (rest.splitOn "hrule")[1]? with
    | some afterRule =>
      if color.isEmpty then dropped "" else
      -- The rule's own words end at the next control sequence (`\\hfill`,
      -- `\\kern`); `\\p@` is TeX's own point, spelled for the length grammar.
      let spec := ((afterRule.replace "\\p@" "pt").replace "\\z@" "0pt").splitOn "\\"
        |>.headD "" |>.trimAscii.toString
      let height? : Option String :=
        if spec.isEmpty then some "0.4pt"
        else if spec.startsWith "height" then
          let h := (spec.drop 6).trimAscii.toString
          if (h.splitOn " ").any (fun w => w == "depth" || w == "width") then none
          else some (if h.startsWith "." then "0" ++ h else h)
        else none
      match height? with
      | some h =>
        let native := s!"\\style\{section}\{ rule = {color}, rule-position = baseline, rule-thickness = {h} }"
        became "\\sectionlinesformat" native pos
        synthAt native pos
      | none => dropped s!" (rule dimensions '{spec}' other than a height)"
    | none => dropped ""
  | none => dropped ""

/-- Does environ's `\BODY` stand anywhere in the tree, a group or an
environment down included? -/
private def mentionsBody : List Raw → Bool
  | [] => false
  | .ctrl "BODY" _ :: _ => true
  | .group body _ :: rest => mentionsBody body.toList || mentionsBody rest
  | .env _ body _ :: rest => mentionsBody body.toList || mentionsBody rest
  | .math _ body _ :: rest => mentionsBody body.toList || mentionsBody rest
  | _ :: rest => mentionsBody rest
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    (have hb : sizeOf body = 1 + sizeOf body.toList := by rfl
     omega)

/-- environ's `\BODY` placed once at the top level of a definition's code:
the code before it and the code after it, an environment's begin and end
code with the body standing between them. `none` when `\BODY` is absent,
stands inside a group, or stands twice. -/
public def bodySlot? (code : Array Raw) : Option (Array Raw × Array Raw) :=
  (code.findIdx? (· matches .ctrl "BODY" _)).bind fun i =>
    let before := code.extract 0 i
    let after := code.extract (i + 1) code.size
    if mentionsBody before.toList || mentionsBody after.toList then none
    else some (before, after)

/-- The mark the rewrite sets after the native head of an environ
definition, and that the elaborator's split sets closing the begin half it
builds: the elaborator builds that definition's halves from its code where
the mark stands — the code split at a top-level `\BODY` (`bodySlot?`), or
all of it the end half when it places none — and only there, so a `\BODY`
in a kernel definition is the document's own macro; in a begin half it says
the body's edge spaces are trimmed (environ.sty `\env@save`:
`\trim@spaces`). `:` is no letter (`Lex.nameChar`), so no document spells
the name. -/
public def environBodyMark : String := "@environ:BODY"

/-- The declarations standing in front of a float's kernel core when they
are the whole begin body: each a `\setlength` of one of the two caption
skips, then `\@float{kind}` (latex.ltx defines the float environments as
exactly that core). -/
private def floatCoreDecls (kind : String) : List Raw → Option (List (String × Array Raw))
  | [.ctrl "@float" _, .group n _] =>
    if (rawSrc n).trimAscii.toString == kind then some [] else none
  | .ctrl "setlength" _ :: .group reg _ :: .group v _ :: rest =>
    let skip := (ctrlName reg).filter fun r => r == "abovecaptionskip" || r == "belowcaptionskip"
    skip.bind fun r => (floatCoreDecls kind rest).map ((r, v) :: ·)
  | _ => none

/-- A caption skip's value inside the float-core idiom, read where the code
runs: one name alone copies the skip this code assigned before (TeX's
assignments run in sequence), then the door every `\setlength` reads
through. `\belowcaptionskip` is no token here (the `\setlength` arm's
N0102), so a value naming it that this code never assigned has nothing
to read. -/
private def floatSkipValue? (assigned : Array (String × String)) (v : Array Raw) :
    M (Option String) := do
  if let #[.ctrl n _] := v.filter (!· matches .space) then
    if let some (_, src) := assigned.find? (·.1 == n) then return some src
  if v.any (· matches .ctrl "belowcaptionskip" _) then return none
  doorValue? v

/-- A float redefined around its own kernel core — the venue idiom
`\renewenvironment{table}{\setlength{\abovecaptionskip}{…}…\@float{table}}
{\end@float}`, which swaps the caption skips for tables — is a scoped
declaration over the built-in float, not a new environment: the float
stays the engine's, and each skip becomes the kind's own token
(`tablecaptionsep`, `tablebelowcaptionskip`), which no other kind reads.
Which of them faces the table is the caption's side and the position it
is placed for (`Ir.captionSides`): the caption package's, declared where
the document declares it; without the package, the kernel's own
`\@makecaption` order, declared here as `position=bottom` for the kind.
Any other shape is not the idiom and stays the elaborator's refusal
(W0303). -/
private def floatRedef? (envName : String) (raws : Array Raw) (j : Nat) (pos : Pos) :
    M (Option (Array Raw × Nat)) := do
  let some kind := Ir.FloatKind.ofCaptionType? envName | return none
  unless envName == "table" || envName == "figure" do return none
  let items (xs : Array Raw) : List Raw := xs.toList.filter fun r =>
    match r with | .space | .par _ => false | _ => true
  let b := skipSpaces raws j
  let some (.group beginB _) := raws[b]? | return none
  let e := skipSpaces raws (b + 1)
  let some (.group endB _) := raws[e]? | return none
  match items endB, floatCoreDecls envName (items beginB) with
  | [.ctrl "end@float" _], some decls =>
    -- Each skip is read at the door every `\setlength` reads through, in
    -- the code's order, as TeX runs the assignments: a copy of the other
    -- caption skip reads what this code assigned it before, and a value
    -- the door cannot read is named once and skipped, the skip keeping
    -- its value — never handed to the declaration unread.
    let mut assigned : Array (String × String) := #[]
    for (r, v) in decls do
      match ← floatSkipValue? assigned v with
      | some src => assigned := (assigned.filter (·.1 != r)).push (r, src)
      | none => let _ ← unreadableLength r (rawSrc v).trimAscii.toString pos
    let entries := assigned.toList.map fun (r, src) =>
      let tok := if r == "abovecaptionskip" then "captionsep" else "belowcaptionskip"
      s!"{kind.captionScope}{tok} = {src}"
    -- premise: captionScopeChecks — the kernel's order is declared only
    -- where no caption package places the skips, which the loads read
    -- over the whole preamble say
    let packaged := (← get).loads.pkgs.any fun (p, _) => p == "caption" || p == "subcaption"
    let natives := if entries.isEmpty then [] else
      s!"\\tokens\{ {String.intercalate ", " entries} }" ::
        (if packaged then [] else [s!"\\captionsetup[{envName}]\{position=bottom}"])
    let mut out : Array Raw := #[]
    for native in natives do
      out := out ++ (← synthAt native pos)
    let what := if natives.isEmpty then s!"the built-in \{{envName}}"
      else String.intercalate " " natives
    became s!"\\renewenvironment\{{envName}}" what pos
    return some (out, e + 1)
  | _, _ => return none

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
        -- A negative afterskip declares a run-in heading (ltsect.dtx).
        -- `\paragraph` and `\subparagraph` *are* run-in here — bold at
        -- the body size, an em quad to the text, classes.dtx's own shape
        -- (the elaborator's paragraph arm) — so a redefinition asking for
        -- that under the built-in's own font declares what already
        -- renders. One asking a font the run-in title does not set, or a
        -- run-in at a display level, stays named and skipped.
        let runinBuiltin := cmd == "paragraph" || cmd == "subparagraph"
        let ownFont := args[5].all fun r => match r with
          | .ctrl n _ => ["bf", "bfseries", "normalsize", "raggedright"].contains n
          | .space => true
          | _ => false
        if runinBuiltin && ownFont then
          became s!"\\{cmd} = \\@startsection\{{cmd}}"
            "the built-in run-in heading: bold at the body size, an em \
quad to the text" pos
        else
          sayOnce ("ctrl:runin:" ++ cmd) .W0104
            (if runinBuiltin then
              s!"'\\{cmd}' is already a run-in heading, and the \
redefinition's font is not one the run-in title sets; the redefinition \
is skipped"
            else
              s!"'\\{cmd}' would be a run-in heading (negative \
\\@startsection afterskip), which is not modelled at this level; the \
redefinition is skipped") pos
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

/-- Commands that are one fixed token by another name: each row rewrites
the control word to its literal replacement — no arguments, no note, since
the spelling is native content, not a loss. `compatChecks` pins each
spelling. -/
private def literalReplace : List (String × (Pos → Raw)) :=
  [("thepage", fun p => .ctrl "pagenumber" p),
   ("textbar", fun p => .word "|" p),
   ("textperiodcentered", fun p => .ctrl "middot" p),
   ("textendash", fun p => .ctrl "endash" p),
   ("textemdash", fun p => .ctrl "emdash" p),
   ("textbackslash", fun p => .word "\\" p),
   ("textasciitilde", fun p => .word "~" p),
   -- biblatex's citation spellings are natbib's by other names (biblatex
   -- manual §3.8.2: \parencite is the parenthetical cite, \textcite the
   -- textual, \autocite the context-dependent one that resolves to the
   -- parenthetical in the shipped styles): the rename is the whole
   -- translation, and the natbib door treats notes and stars identically
   -- for both spellings.
   ("autocite", fun p => .ctrl "citep" p),
   ("parencite", fun p => .ctrl "citep" p),
   ("textcite", fun p => .ctrl "citet" p)]

/-- The mark the rewrite sets before `\vspace*`'s space: LaTeX's `\@vspacer`
puts a zero rule there, which keeps the space at a page's top
(`Ir.pageAnchorRole`, the block Elab makes of it). A space is in no control
word, so no document spells the mark, as `frameRestartMark`'s is. -/
public def vspaceAnchorMark : String := "vspace anchor"

/-- Commands whose whole meaning is one fixed native spelling, synthesised
in place with a `became` note: each row is an argument-free rewrite.
`\vfill` is `\vspace{\fill}` (ltspace.dtx): fil glue between blocks. The
skip commands carry LaTeX's own `\bigskipamount` family values. The
setspace named stretches sit at the values its source sets for the 10pt
base size the engine defaults to (setspace.sty: \onehalfspacing =
\setstretch{1.25}, \doublespacing = \setstretch{1.667} under \@ptsize 0).
`compatChecks` pins each spelling. -/
private def simpleNative : List (String × String) :=
  [("vfill", "\\block[before = fill]{}"),
   ("bigskip", "\\block[before = 12pt plus 4pt minus 4pt]{}"),
   ("medskip", "\\block[before = 6pt plus 2pt minus 2pt]{}"),
   ("smallskip", "\\block[before = 3pt plus 1pt minus 1pt]{}"),
   ("singlespacing", "\\page{ leading = 1 }"),
   -- The page's bottom (latex.ltx `\flushbottom`, `\raggedbottom`).
   ("flushbottom", "\\page{ bottom = flush }"),
   ("raggedbottom", "\\page{ bottom = ragged }"),
   ("onehalfspacing", "\\page{ leading = 1.25 }"),
   ("doublespacing", "\\page{ leading = 1.667 }")]

/-- moloch's `block` option (beamercolorthememoloch.sty, `/moloch/color/block`):
`fill` paints the boxes from the page's own colours and `transparent`
clears them — the theme's own declarations, `\moloch@block@fill` and
`\moloch@block@transparent`, spelled as it spells them and resolved like
any `\setbeamercolor`: each keeps the `use` the theme declared at load
(`BeamerColor.themeElement`) where it names none. -/
private def molochBlockColors : String → Option (List (String × String))
  | "fill" => some [("block title", "bg=normal text.bg!80!fg"),
      ("block body", "use=block title,bg=block title.bg!50!normal text.bg"),
      ("block title alerted", "bg=block title.bg"),
      ("block title example", "bg=block title.bg")]
  | "transparent" => some [("block title", "bg="), ("block body", "bg="),
      ("block title alerted", "bg="), ("block title example", "bg=")]
  | _ => none

/-- moloch's options (`\molochset` keys, `\usetheme[...]{moloch}`): the
`block` option declares the theme's block colours, as the
`setbeamercolor` arm hands them to the elaborator; every other key is
theme configuration the engine does not have, named once. -/
private def molochOptions (cmd src : String) (pos : Pos) : M (Array Raw) := do
  let mut out := #[]
  for entry in Decl.splitEntries src do
    match Decl.splitEntry entry with
    | some (key, value) =>
      let value := value.trimAscii.toString
      match key, molochBlockColors value with
      | "block", some decls =>
        became s!"{cmd} block={value}" "moloch's block colours, declared with \\setbeamercolor" pos
        for (element, body) in decls do
          out := out ++ #[.ctrl BeamerColor.marker pos, .group (← synthAt element pos) pos,
            .group (← synthAt body pos) pos]
      | "block", none =>
        sayOnce ("moloch:" ++ key) .W0104
          s!"'{cmd}' option '{key}={value}' is moloch configuration the engine does not have; skipped" pos
          (help := "moloch's block option takes fill or transparent")
      | _, _ =>
        sayOnce ("moloch:" ++ key) .W0104
          s!"'{cmd}' option '{key}={value}' is moloch configuration the engine does not have; skipped" pos
    | none =>
      unless entry.trimAscii.toString.isEmpty do
        sayOnce ("moloch:" ++ entry.trimAscii.toString) .W0104
          s!"'{cmd}' option '{entry.trimAscii.toString}' is moloch configuration the engine does not have; skipped" pos
  return out

/-- The finite block-hook grammar: whitespace and the three standard skip
commands, each read through its existing native translation. Unknown raws
refuse the entire addition; a nested command is never executed here. -/
private def blockHookSkips (out : Array String) : List Raw → Option (Array String)
  | [] => some out
  | .space :: rest => blockHookSkips out rest
  | .ctrl name _ :: rest =>
    if ["smallskip", "medskip", "bigskip"].contains name then
      (simpleNative.lookup name).bind fun native =>
        blockHookSkips (out.push native) rest
    else none
  | _ => none

/-- beamerbasetemplates.sty appends the after-body to the named template;
beamerbaseblocks.sty uses `block begin` between the title and body. Only
top-level preamble additions are global here. All three arguments belong
to this command even on refusal, so their content cannot reach recovery. -/
private def blockHookArm (pos : Pos) (raws : Array Raw) (start : Nat) :
    M (Option (Array Raw × Nat)) := do
  let (args, k) := takeGroups raws start 3
  let element := (rawSrc (args.getD 0 #[])).trimAscii.toString
  match blockHookSkips #[] (args.getD 1 #[]).toList,
      blockHookSkips #[] (args.getD 2 #[]).toList with
  | some before, some after =>
    -- premise: beamerHookChecks — body, grouped and wrong-slot additions cannot set a global gap.
    if args.size == 3 && element == "block begin" && before.isEmpty && (← docPreamble) then
      let native := String.join after.toList
      let spacing ← synthAt native pos
      write fun st => { st with beamerBlockBegin := st.beamerBlockBegin ++ spacing }
      if spacing.isEmpty then
        discard "\\addtobeamertemplate{block begin}" "both additions are empty"
          "addtobeamertemplate:block begin" pos
      else
        became "\\addtobeamertemplate{block begin}"
          s!"{native} at each ordinary block's body start" pos
    else
      sayOnce ("beamer:addtobeamertemplate:" ++ element) .W0104
        s!"'\\addtobeamertemplate\{{element}}' is skipped: only top-level preamble \
additions with an empty before-body and standard skips after 'block begin' are supported" pos
        (help := beamerNative.lookup "addtobeamertemplate")
  | _, _ =>
    say .E0111
      s!"'\\addtobeamertemplate\{{element}}' is dropped with its unsupported template bodies" pos
      (help := beamerNative.lookup "addtobeamertemplate")
      (subject := some ("beamer:addtobeamertemplate:" ++ element))
  return some (#[], k)

/-- The footline restoration reads exactly the standout foreground and
the current canvas background. Other keys or expressions are patch code
the engine cannot interpret, even if one of these fields is also present. -/
private def standoutFootColors (body : Array Raw) : Bool :=
  let fields := Decl.splitEntries (rawSrc body)
  let entries := fields.filterMap Decl.splitEntry
  fields.length == 3 && entries.length == 3 &&
    entries.lookup "fg" == some "standout.fg" &&
    entries.lookup "bg" == some "background canvas.bg" &&
    (match (entries.lookup "use").bind Decl.parseValue with
     | some (.block names) => Decl.splitEntries names == ["standout", "background canvas"]
     | _ => false)

/-- The supported appended body, structurally matched without evaluating
any package code: when the explicit note exists, restore the plain
footline in the frame's colors and clear the unnumbered frame's number. -/
private def standoutFootBody (body : Array Raw) : Bool :=
  match (body.filter (!· matches .space)).toList with
  | [.ctrl "ifbeamertemplateempty" _, .group slot _, .group empty _, .group restore _] =>
    rawSrc slot == "frame footer" && empty.all (· matches .space) &&
      (match (restore.filter (!· matches .space)).toList with
       | [.ctrl "setbeamercolor" _, .group colorSlot _, .group colors _,
          .ctrl "setbeamertemplate" _, .group footSlot _,
          .sym '[' _, .word "plain" _, .sym ']' _,
          .ctrl "ifbeamer@noframenumbering" _,
          .ctrl "setbeamertemplate" _, .group numberSlot _, .group numberBody _,
          .ctrl "fi" _] =>
         rawSrc colorSlot == "footline" && standoutFootColors colors &&
           rawSrc footSlot == "footline" && rawSrc numberSlot == "page number in head/foot" &&
           numberBody.all (· matches .space)
       | _ => false)
  | _ => false

/-- Scan only the finite appended alias grammar. Operands remain original
groups; no patch code, callback or author text is reparsed. -/
private def standoutAliasList (out : Array Raw) : List Raw → Option (Array Raw)
  | [] => some out
  | .ctrl "colorlet" pos :: .group name np :: .group source sp :: rest =>
    standoutAliasList
      (out ++ #[.ctrl BeamerColor.standoutMarker pos, .group name np, .group source sp]) rest
  | _ => none

/-- etoolbox's append succeeds for the known beamer standout option, so
only its empty success callback runs. The failure callback is never read
as executable input. All four arguments are owned even on refusal.
The native setting carries the behavior to both backends; this is not a
general macro patch interpreter. -/
private def standoutFootHookArm (pos : Pos) (raws : Array Raw) (start : Nat) :
    M (Option (Array Raw × Nat)) := do
  let (args, k, tail) := takeHookArgs raws start
  -- premise: beamerHookChecks — altered bodies, callbacks and scopes refuse whole;
  -- the supported shape changes the shipped standout note in both backends.
  if args.size == 4 && (← get).deck && (← docPreamble) &&
      ctrlName (args.getD 0 #[]) == some "KV@beamerframe@standout" &&
      (args.getD 2 #[]).all (· matches .space) then
    if standoutFootBody (args.getD 1 #[]) then
      let native := "\\chrome{standout-note=true}"
      became "\\apptocmd{\\KV@beamerframe@standout}" native pos
      return some ((← synthAt native pos) ++ tail, k)
    -- premise: standoutPaletteChecks — aliases change both artifacts only
    -- on standout frames; unsupported patch bodies are refused whole.
    if let some aliases := standoutAliasList #[]
        ((args.getD 1 #[]).filter (!· matches .space)).toList then
      if !aliases.isEmpty && nativeStandoutDefined (← get) then
        became "\\apptocmd{\\KV@beamerframe@standout}" "frame-local colour aliases" pos
        return some (aliases ++ tail, k)
  say .E0111 "'\\apptocmd' is dropped with its patch and callbacks: only standout \
colour aliases or explicit-footer restoration with an empty success callback are supported in a beamer preamble"
    pos (help := "append '\\colorlet' aliases after loading the standout theme, or use \
'\\chrome{standout-note=true}' to restore explicit notes")
    (subject := some "ctrl:apptocmd")
  return some (tail, k)

/-- cleveref's range form (manual v0.21.4 §2, `\crefrange{key1}{key2}`):
desugared to the pair the resolver renders — the first key carries the
plural name and the range conjunction (`@crefrange`), the second the
label format alone (`labelcref`). The marker is unforgeable (`@` never
lexes into a control word). Outside the dispatcher halves, which sit at
their LCNF compile budgets. -/
private def crefRangeArm (name : String) (pos : Pos) (raws : Array Raw)
    (start : Nat) : M (Option (Array Raw × Nat)) := do
  let (args, k) := takeGroups raws start 2
  if h : args.size = 2 then
    became s!"\\{name}" "the range pair: plural name, both numbers" pos
    return some (#[.ctrl ("@" ++ name) pos, .group args[0] pos,
      .ctrl "labelcref" pos, .group args[1] pos], k)
  else return none

/-- `\alert{body}` without an overlay spec: `alertStyled` around the body —
themed, `\textcolor{alert}` around bold; unthemed, bold. With no body group
the command stays `\textbf`, which names the missing argument. -/
private def alertPlain (pos : Pos) (raws : Array Raw) (start : Nat) :
    M (Option (Array Raw × Nat)) := do
  let themed := (← get).themed
  let (args, k) := takeGroups raws start 1
  match args[0]? with
  | some body =>
    became "\\alert"
      (if themed then "\\textcolor{alert}{\\bfseries ...}" else "{\\bfseries ...}") pos
    return some (alertStyled themed body pos, k)
  | none =>
    if themed then
      became "\\alert" "\\textcolor{alert}" pos
      return some (← synthAt "\\textcolor{alert}" pos, start)
    else
      became "\\alert" "\\textbf" pos
      return some (#[.ctrl "textbf" pos], start)

/-- Unforgeable prefix for a parsed `\fontsize` declaration. The two
source dimensions follow, separated by NUL; source names cannot contain it,
and elaboration removes the spelling before any IR value exists. -/
public def fontSizeMark : String := "@fontsize:"
public def fontSizeSep : String := "\u0000"

/-- Beamer's three marker templates select the corresponding list depth
(beamerbaseauxtemplates.sty). Their bodies remain inline templates. -/
private def beamerMarkerElement : String → Option String
  | "itemize item" => some "itemize"
  | "itemize subitem" => some "itemize2"
  | "itemize subsubitem" => some "itemize3"
  | _ => none

/-- A colour-box footer with a left note and a right frame counter is the
native two-slot footer. Only this structural shape is claimed; unrelated
template code still belongs to the existing whole-body refusal. -/
private def numberedFootline? (body : Array Raw) :
    Option (Array Raw × String × Option String × String) := do
  let [Raw.env "beamercolorbox" box _] := body.toList.filter (· != .space)
    | none
  let (options, j) := takeOpt box 0
  let (args, j) := takeGroups box j 1
  if args.size != 1 || (rawSrc (args.getD 0 #[])).trimAscii.toString != "footline" then none
  let j := skipSpaces box j
  let (font, j) := match box[j]? with
    | some (.ctrl "usebeamerfont" _) =>
      let (args, k) := takeGroups box (j + 1) 1
      (args[0]?.map (fun rs => (rawSrc rs).trimAscii.toString), k)
    | _ => (none, j)
  let content := box.extract j box.size
  let split ← content.findIdx? (fun r => r matches .ctrl "hfill" _)
  let right := String.ofList
    (((rawSrc (content.extract (split + 1) content.size)).replace "\\," "").toList.filter
      (!·.isWhitespace))
  let counter ← if right == "\\insertframenumber" then some "framenumber"
    else if right == "\\insertframenumber/\\inserttotalframenumber" then some "framefraction"
    else none
  some (content.extract 0 split, counter, font, options.getD "")

/-- Resolve a stored footer through the same font-size marker and native
footer declarations as ordinary document content. Box dimensions are not
content: the shared footer band determines those, with a named adaptation. -/
private def flushBeamerFootline : M (Array Raw × Array Raw) := do
  let some (file, pos, body) := (← get).beamerFootline | return (#[], #[])
  let savedFile := (← get).file
  let wrap (rs : Array Raw) : Array Raw :=
    if file == savedFile then rs else #[Raw.env (Parse.inputEnv file) rs pos]
  if body.isEmpty then
    return (wrap (← synthAt "\\runningfoot{\\hfill}" pos),
      wrap #[Raw.ctrl "framefoot" pos, Raw.group #[] pos])
  let some (left, counter, fontName, options) := numberedFootline? body
    | return (#[], #[])
  write fun st => { st with file := file }
  let mut fontPrefix : Array Raw := #[]
  let mut unread : Array String := #[]
  if let some name := fontName then
    if let some fields := (← get).beamerFonts.toList.lookup name then
      let font := beamerTemplateFont name fields
      if let some size := font.size then
        fontPrefix := fontPrefix.push (.ctrl (fontSizeMark ++ size ++ fontSizeSep ++
          font.leading.getD "") pos)
      fontPrefix := fontPrefix ++ (← synthAt font.cmds pos)
      unread := font.unread
      -- premise: beamerTemplateChecks — the selected font reaches the footer note in both outputs
      write fun st => { st with diags := st.diags.filter fun d =>
        !(d.code == DiagCode.W0104.code &&
          d.subject == some ("beamer:setbeamerfont:" ++ name)) }
    else
      unread := unread.push s!"font '{name}'"
  unless options.isEmpty do unread := unread.push "colour-box dimensions"
  if fontName.isSome then unread := unread.push "counter font"
  unless unread.isEmpty do
    sayOnce "beamer:setbeamertemplate:footline" .W0110
      s!"the footer note and frame counter use the native footer band; not applied: \
{String.intercalate ", " unread.toList}" pos
      (help := "use \\framefoot{...} for its note and \\chrome{footer={right=\\framefraction}} for numbering")
  let pre ← synthAt s!"\\chrome\{footer=\{right=\\{counter}}}" pos
  let note := #[Raw.ctrl "framefoot" pos, Raw.group (fontPrefix ++ left) pos]
  write fun st => { st with file := savedFile }
  return (wrap pre, wrap note)

/-- Local option diagnostics travel with the spliced file until conditionals
and `\endinput` have selected its live text. A space is in no control word:
these requests cannot be written by a document. The load request checks for
a live process request at its own file level, never in a nested package. -/
private def styOptionsLoadMark : String := "package options load"
private def styOptionsProcessedMark : String := "package options processed"
private def styOptionsUnhandledMark : String := "package options unhandled"

private def unhandledStyOption (pkg option why : String) (pos : Pos) : M Unit :=
  sayOnce ("package-option:" ++ pkg ++ ":" ++ option) .W0110
    s!"option '{option}' for local package '{pkg}' {why}; ignored" pos
    (help := "remove the option or declare and process its handler in the local style")

/-- Settle only diagnostic requests, through the same accounting door as
other ignored options. No style is opened here and no TeX is evaluated.
`packageOptionChecks` holds the loss, source span, inactive branches,
unprocessed loads and nested file boundaries to the actual CLI splice. -/
private def styOptionsRequest (name : String) (pos : Pos) (raws : Array Raw)
    (start : Nat) : M (Option (Array Raw × Nat)) := do
  if name == styOptionsProcessedMark then
    became "\\ProcessOptions" "the selected local package option bodies" pos
    return some (#[], start)
  if name != styOptionsLoadMark && name != styOptionsUnhandledMark then return none
  let (args, k) := takeGroups raws start 2
  if args.size != 2 then return none
  let pkg := rawSrc (args.getD 0 #[])
  if name == styOptionsUnhandledMark then
    unhandledStyOption pkg (rawSrc (args.getD 1 #[])) "has no handler" pos
  else
    -- premise: packageOptionChecks — only a process in this live file
    -- discharges its options; an inactive or nested process cannot do so.
    if raws.any (fun r => r matches .ctrl "package options processed" _) then
      discard s!"option list for local package '{pkg}'"
        "its options are checked by '\\ProcessOptions'" ("package-options:" ++ pkg) pos
    else
      for r in args.getD 1 #[] do
        if let .word option _ := r then
          unhandledStyOption pkg option "was not processed" pos
  return some (#[], k)

/-- The first share in a two-column `\\columnratio` declaration, in per
mille. Paracol gives every listed ratio to its column and the remainder to
the final column (`paracol.sty`, `\\pcol@setcolwidth@r`). -/
private def paracolRatio? (src : String) : Option Nat := do
  let first ← (src.splitOn ",").find? fun s => !s.trimAscii.toString.isEmpty
  let (m, scale) ← Decl.parseDecimal first.trimAscii.toString
  let p := m * 1000 / scale
  guard (0 < p && p < 1000)
  return p.toNat

private def paracolFactor (p : Nat) : String :=
  let digits := toString (p % 1000)
  "0." ++ "".pushn '0' (3 - digits.length) ++ digits

/-- Named arms of the later dispatcher. The wrapper handles local style
option requests first; keeping that guard outside the match exposes the
actual routing equation without unfolding unrelated command bodies. -/
private def rewriteCtrlLaterNamed (name : String) (pos : Pos) (raws : Array Raw)
    (start : Nat) : M (Option (Array Raw × Nat)) := do
  match name with
  | "addtobeamertemplate" => blockHookArm pos raws start
  | "apptocmd" => standoutFootHookArm pos raws start
  | "linespread" | "setstretch" =>
    -- setspace's parameterised form is \linespread by another name
    -- (setspace.sty: both set \baselinestretch).
    let (args, k) := takeGroups raws start 1
    if args.isEmpty then return none
    let native := s!"\\page\{ leading = {rawSrc (args.getD 0 #[])} }"
    became s!"\\{name}" native pos
    return some (← synthAt native pos, k)
  | "xspace" =>
    -- xspace package: a space unless punctuation follows (xspace
    -- documentation, the exception list — TeX's tokenizer has already
    -- eaten the space the author typed after the control word, here as
    -- there). The walk reads the next parsed element; at the end of a
    -- group or macro body, where the following context is the use
    -- site's and unknowable at rewrite time, the space — the package's
    -- default action — is emitted. It is emitted as control-space, which
    -- survives a macro body's trailing-space trim; a bare interword
    -- space would be dropped there and glue the words after all.
    let punct (c : Char) : Bool :=
      c == '.' || c == ',' || c == '\'' || c == '/' || c == '?' ||
      c == ';' || c == ':' || c == '!' || c == '~' || c == '-' || c == ')'
    let noSpace := match raws[start]? with
      | some (.word w _) => (w.toList.head?.map punct).getD false
      | some (.sym c _) => punct c
      | some .space | some (.par _) => true
      | _ => false
    return some (if noSpace then #[] else #[.ctrl " " pos], start)
  | "addbibresource" =>
    -- biblatex's resource declaration (biblatex manual §3.7.1): the .bib
    -- file, named at load time, that \printbibliography later prints. The
    -- name rides the walk's state to that site; the natbib door
    -- (\bibliography) takes its file where the list prints. The engine
    -- reads one .bib per document, so a second resource is skipped named.
    let (_, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    if h : args.size = 1 then
      let src := (rawSrc args[0]).trimAscii.toString
      let src := if src.endsWith ".bib" then (src.dropEnd 4).toString else src
      if (← get).bibResources.isEmpty then
        write fun st => { st with bibResources := st.bibResources.push src }
        became "\\addbibresource" s!"\\bibliography\{{src}}, at \\printbibliography" pos
      else
        say .W0104 s!"'\\addbibresource' names a second resource '{src}'; the \
engine reads one .bib per document, so it is skipped" pos
          (help := "merge the entries into the first .bib file")
      return some (#[], k)
    else return none
  | "setcitestyle" | "bibpunct" | "citestyle" => natbibStyleArm name pos raws start
  | "bibliographystyle" =>
    -- LaTeX reads the style anywhere before the `.aux` is written, and
    -- natbib reads it back at `\begin{document}`. The preamble elaborator
    -- does not take it, so a preamble declaration replays there, where the
    -- body arm carries it to the `\bibliography` marker.
    -- premise: compatIndexChecks — the index's body \bibliographystyle rows
    -- set their style through the body arm, with no unknown-command warning
    if (← get).inDoc || (← get).seam then return none
    let (args, k) := takeGroups raws start 1
    match args[0]? with
    | some g =>
      became "\\bibliographystyle" "read at \\begin{document}, as natbib reads the .aux" pos
      write fun st => { st with deferred := st.deferred.push (.beginDocument, st.file, pos,
        #[.ctrl "bibliographystyle" pos, .group g pos]) }
      return some (#[], k)
    | none => return none
  | "printbibliography" =>
    -- The list prints here (biblatex manual §3.7.2), from the resources
    -- declared above; its options (heading=, title=) restyle a heading
    -- the locale already words, dropped named when given.
    let (o, k) := takeOpt raws start
    if let some o := o then
      unless o.trimAscii.toString.isEmpty do
        say .W0101 s!"\\printbibliography options without a native equivalent \
were dropped: {o}" pos
    match (← get).bibResources[0]? with
    | some src =>
      let stylePart := match (← get).bibStyle with
        | some s => s!"\\bibliographystyle\{{s}}"
        | none => ""
      let native := s!"{stylePart}\\bibliography\{{src}}"
      became "\\printbibliography" native pos
      return some (← synthAt native pos, k)
    | none =>
      discard "\\printbibliography" "no \\addbibresource declared a file"
        "printbibliography" pos
      return some (#[], k)
  | "crefrange" | "Crefrange" =>
    -- cleveref's range form: desugared by `crefRangeArm` (its docstring
    -- carries the shape and the source).
    crefRangeArm name pos raws start
  | "fontsize" =>
    -- NFSS records the two dimensions and `\selectfont` commits them. The
    -- latter is already an earned no-op here; this marker carries both
    -- values to the one typed style parser without reparsing document text.
    let (args, k) := takeGroups raws start 2
    if args.size < 2 then
      say .E0304 "'\\fontsize' needs {size} and {leading} groups" pos
      return some (#[], k)
    let size := rawSrc (args.getD 0 #[])
    let leading := rawSrc (args.getD 1 #[])
    became "\\fontsize" "an affine font size and baseline skip" pos
    return some (#[.ctrl (fontSizeMark ++ size ++ fontSizeSep ++ leading) pos], k)
  | "fontseries" =>
    -- NFSS's series declaration (fntguide §2.2): the weight half rides the
    -- unforgeable `@series:` marker into elaboration (`declStyleOf`, the
    -- `@lang:` door), where it styles the rest of the scope as `\bfseries`
    -- does. The width half names an axis the engine does not have; it is
    -- warned by name rather than silently dropped with the weight.
    let (args, k) := takeGroups raws start 1
    if args.isEmpty then return none
    let code := (rawSrc (args.getD 0 #[])).trimAscii.toString
    match Ir.Weight.parseSeries code with
    | some (w, width) =>
      -- premise: compatMarkerChecks — a top-level discard leaves the Doc the one without it
      if ← preambleProper then
        discard s!"\\fontseries\{{code}}" "'\\begin{document}' selects the normal series"
          s!"fontseries:{code}" pos
        return some (#[], k)
      if !width.isEmpty then
        sayOnce ("ctrl:fontseries:" ++ width) .W0104
          s!"'\\fontseries\{{code}}' also asks for the '{width}' width; \
the engine has no width axis, so only the weight is honoured" pos
      became s!"\\fontseries\{{code}}" s!"the {w.series} series" pos
      return some (#[.ctrl ("@series:" ++ w.series) pos], k)
    | none =>
      sayOnce "ctrl:fontseries" .W0104
        s!"'\\fontseries\{{code}}' names no NFSS series; \
the weight in force stands" pos
      return some (#[], k)
  | "linenumbers" | "runninglinenumbers" | "nolinenumbers"
  | "modulolinenumbers" =>
    linenoCtrl name pos raws start
  | "selectlanguage" =>
    -- babel's mid-document switch: from here on, in flow order (babel
    -- manual §1.5). The marker is unforgeable (`@` never lexes into a
    -- control word); elaboration turns it into the language attribute,
    -- which hyphenation and both artifacts read.
    let (args, k) := takeGroups raws start 1
    if args.isEmpty then return none
    let lname := rawSrc (args.getD 0 #[])
    -- premise: compatMarkerChecks — a top-level discard leaves the Doc the one without it
    if ← preambleProper then
      discard s!"\\selectlanguage\{{lname}}" "'\\begin{document}' selects the main language"
        s!"selectlanguage:{lname}" pos
      return some (#[], k)
    let tag := Locale.babelTagOf lname
    if (Locale.forTag tag).isNone then
      say .W0368 s!"no locale for language '{lname}'; English captions \
and patterns stand in" pos
        (help := "the engine ships locale records for: en, fr, de")
    -- `\enquote` reads its quotes through `mainLang`, and only a switch in
    -- the body moves it. Under csquotes' default lualatex keeps the main
    -- language's quotes after every switch it was measured at: in a
    -- `\begin{document}` hook, in a `\title` argument and in the body. The
    -- body's move here is that open divergence.
    if (← get).inDoc then
      write fun st => { st with mainLang := tag }
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
    -- `\color[model]{spec}` colours to the end of the group (xcolor manual
    -- §2.6.4). The marker carries the source specification intact; the
    -- typed colour parser and resolver in the elaborator own conversion.
    let (model, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    if args.isEmpty then return none
    let value := rawSrc (args.getD 0 #[])
    let source := modeledColorSource model value
    match model with
    | some m => became s!"\\color[{m}]\{{value}}" s!"the {source} ink declaration" pos
    | none => became s!"\\color\{{value}}" s!"\\{value}" pos
    return some (#[.ctrl ("@ink:" ++ source) pos], k)
  | "vspace" =>
    -- The star is `\@vspacer`'s zero rule before the space: its mark goes
    -- first, so the space stays at a page's top (`vspaceAnchorMark`).
    let starred := skipStar raws start != start
    let start := skipStar raws start
    let (_, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    let native := s!"\\block[before = {lengthSrc (args.getD 0 #[])}]\{}"
    if starred then
      became "\\vspace*" s!"a page-top anchor, then {native}" pos
      return some (#[.ctrl vspaceAnchorMark pos] ++ (← synthAt native pos), k)
    became "\\vspace" native pos
    return some (← synthAt native pos, k)
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
  | "setkomafont" =>
    let (args, k) := takeGroups raws start 2
    if h : args.size = 2 then
      let element := rawSrc args[0]
      if element == "disposition" then
        -- KOMA's `disposition` is the base font of every sectioning level
        -- at once (KOMA-Script manual ch. 4, element `disposition`: used
        -- by all the disposition levels, each level's own element applied
        -- after it). One declaration fans out to each heading element the
        -- engine draws; a later \setkomafont{section} then wins per key,
        -- the engine's own replace-on-redeclare — KOMA composes the two
        -- font lists instead, a divergence this arm accepts.
        let native := "\\style{section}{ font = {...} }, per heading level"
        became "\\setkomafont{disposition}" native pos
        let mut out : Array Raw := #[]
        for lvl in ["section", "subsection", "subsubsection"] do
          let font : Raw := .group #[.word "font" pos, .space, .sym '=' pos, .space,
            .group args[1] pos] pos
          out := out ++ (← synthAt s!"\\style\{{lvl}}" pos).push font
        return some (out, k)
      else if Ir.styleableElements.contains element then
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
    if !Ir.styleableElements.contains element then
      say .W0111 s!"'\\RedeclareSectionCommand\{{element}}' names no styleable element; \
ignored" pos
        (help := "\\style{element}{ before = ..., after = ... } spaces the elements \
the engine draws")
      return some (#[], k)
    if keys.isEmpty then
      -- Recognized element, no mappable key: the declared entries are the
      -- loss, named (W0101's shape); an empty option is the guard's W0387.
      let dropped := (opt.getD "").trimAscii.toString
      unless dropped.isEmpty do
        say .W0101 s!"'\\RedeclareSectionCommand\{{element}}' entries without a \
native equivalent were dropped: {dropped}" pos
      return some (#[], k)
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
    if !Ir.styleableElements.contains element then
      say .W0111 s!"'\\setlist[{element}]' names no styleable element; ignored" pos
        (help := "\\style{element}{ indent = ..., gap = ... } styles the lists \
the engine draws")
      return some (#[], k)
    if keys.isEmpty then
      -- Recognized list, no mappable key: the declared entries are the
      -- loss, named (W0101's shape); an empty argument is the guard's W0387.
      let dropped := (rawSrc (args.getD 0 #[])).trimAscii.toString
      unless dropped.isEmpty do
        say .W0101 s!"'\\setlist[{element}]' entries without a native equivalent \
were dropped: {dropped}" pos
      return some (#[], k)
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
  | "unimathsetup" =>
    let (args, k) := takeGroups raws start 1
    if args.isEmpty then return none
    let opts := rawSrc (args.getD 0 #[])
    return some (← unicodeMathOptions s!"\\unimathsetup\{{opts}}" opts pos, k)
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
    let arity := undelimitedArity params
    match cmd? with
    | some cmd =>
      -- A class's list-level macro read as the parameters it assigns.
      if found && !expanding && arity == some 0 && (← docPreamble) then
        if let (some level, some (.group body _)) := (listLevelOf cmd, raws[k]?) then
          if ← listLevelDef level s!"\\{name}\{\\{cmd}}" body pos then
            return some (#[], k + 1)
      if found && !expanding && arity.isSome then
        let n := arity.getD 0
        let spec := String.ofList (List.replicate n 'm')
        write fun st => { st with
          bound := if st.bound.contains cmd then st.bound else st.bound.push cmd }
        let native := s!"\\define \\{cmd}({signature spec})"
        became s!"\\{name}\{\\{cmd}}" (native ++ " {...}") pos
        write fun st => { st with bodyNext := 1 }
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
    if name == "renewenvironment" && count.isNone && dflt.isNone then
      -- premise: captionScopeChecks — the float-core idiom reads as its native
      -- kind token, the page equal to that spelling's and free of W0303
      if let some (out, k) ← floatRedef? envName.trimAscii.toString raws j pos then
        return some (out, k)
    let n := (count.bind String.toNat?).getD 0
    let spec := if dflt.isSome then "o" ++ String.ofList (List.replicate (n - 1) 'm')
      else String.ofList (List.replicate n 'm')
    let native := s!"\\defineenv\{{envName}}({signature spec})"
    became s!"\\{name}\{{envName}}" (native ++ " {begin} {end}") pos
    write fun st => { st with bodyNext := 2 }
    write fun st => { st with discardEnvs := st.discardEnvs.filter (·.1 != envName.trimAscii.toString) }
    return some (← synthAt native pos, j)
  | "NewEnviron" | "RenewEnviron" =>
    -- environ.sty's definer (`\env@new`): the begin code collects the
    -- environment's body into `\BODY`, its edge spaces trimmed, and runs
    -- the code; the end code runs the final code, `\ignorespacesafterend`
    -- unless one is given (`\environfinalcode`). With `\BODY` once at the
    -- code's top level that is the kernel's `\newenvironment` with the body
    -- standing there; a code that never places `\BODY` runs where the
    -- environment stands and the collected body goes nowhere, the body
    -- discarded at each use (the `.env` arm of `rewriteRaw`, which keeps
    -- only the arguments). Either takes the native definer's spelling, the
    -- code group announced as a macro body and the head marked, and the
    -- elaborator builds the halves from the code (`bodySlot?`), a
    -- following `[final code]` joining the end. A `\BODY` inside a group
    -- (a box around the whole body) or placed twice has no begin and end
    -- to split into: refused where it stands, the construct consumed whole.
    let (args, j) := takeGroups raws (skipStar raws start) 1
    let envName := rawSrc (args.getD 0 #[])
    let (count, j) := takeOpt raws j
    let (dflt, j) := takeOpt raws j
    let b := skipSpaces raws j
    let n := (count.bind String.toNat?).getD 0
    let spec := if dflt.isSome then "o" ++ String.ofList (List.replicate (n - 1) 'm')
      else String.ofList (List.replicate n 'm')
    let native := s!"\\defineenv\{{envName}}({signature spec})"
    match raws[b]? with
    | some (.group code _) =>
      let slot := (bodySlot? code).isSome
      if slot || !mentionsBody code.toList then
        became s!"\\{name}\{{envName}}" (native ++ (if slot
          then " {code before \\BODY} {code after it}" else " {} {code}, its body discarded")) pos
        write fun st => { st with bodyNext := 1 }
        write fun st => { st with discardEnvs := if slot
          then st.discardEnvs.filter (·.1 != envName.trimAscii.toString)
          else st.discardEnvs.push (envName.trimAscii.toString, spec) }
        -- The elaborator builds the halves where this mark stands beside
        -- the head, and nowhere else; the body has no definer to read it
        -- (E0312), so it is set only before `\begin{document}`.
        let mark := if (← get).inDoc then #[] else #[Raw.ctrl environBodyMark pos]
        return some ((← synthAt native pos) ++ mark, j)
      else
        let (_, k) := takeOpt raws (b + 1)
        sayOnce ("ctrl:" ++ name) .W0104
          s!"'\\{name}\{{envName}}' places \\BODY inside a group or more than once; an \
environment's body stands between its begin and its end code here, so the definition \
is skipped" pos
          (help := "write the code around \\BODY at the definition's top level")
        return some (#[], k)
    | _ => return none
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
      write fun st => { st with themed := true }
    return none
  | "alert" =>
    let j := skipSpaces raws start
    match raws[j]? with
    | some spec@(.word w _) =>
      if (overlayWord? spec).isNone then return ← alertPlain pos raws start
      became s!"\\alert{w}" "a conditional alert style" pos
      -- Leave the original body for rewriteRaw: it is not expanded into
      -- two alternative groups and no nested compatibility work is skipped.
      return some (#[.ctrl (alertMark (← get).themed) pos, spec], j + 1)
    | _ => alertPlain pos raws start
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
    else if let some native := beamerMarkerElement element then
      let (bodyArgs, k) := takeGroups raws j 1
      if bodyArgs.size != 1 then return none
      let marker := rawSrc (bodyArgs.getD 0 #[])
      let source := s!"\\style\{{native}}\{marker=\{{marker}}}"
      became s!"\\setbeamertemplate\{{element}}" source pos
      return some (← synthAt source pos, k)
    -- premise: beamerTemplateChecks — preamble and deferred declarations
    -- carry footer content through the native frame furniture.
    else if element == "footline" &&
        (← get).wholeDoc && !(← get).inDoc && !(← get).inDef then
      let (variant, k) := takeOpt raws j
      let (bodyArgs, k) := takeGroups raws k 1
      if bodyArgs.size != 1 then return none
      let body := bodyArgs.getD 0 #[]
      if (numberedFootline? body).isSome then
        let file := (← get).file
        write fun st => { st with beamerFootline := some (file, pos, body),
                                  beamerCaptures := st.beamerCaptures + 1 }
        became "\\setbeamertemplate{footline}" "a footer note and frame counter" pos
      else if variant.isNone && (rawSrc body).trimAscii.toString.isEmpty then
        let file := (← get).file
        write fun st => { st with beamerFootline := some (file, pos, #[]),
                                  beamerCaptures := st.beamerCaptures + 1 }
        became "\\setbeamertemplate{footline}" "an empty footer band" pos
      else
        say .E0111
          "'\\setbeamertemplate{footline}' is dropped with its template body, which carries content" pos
          (help := beamerNative.lookup "setbeamertemplate")
      return some (#[], k)
    else if element == "title page" then
      let (_, j) := takeOpt raws j
      -- A template of the overlay shape — one picture on the page, a fill
      -- over it, nodes pinned to its points — is a spelling of the engine's
      -- own title page, and is read as one: the ground and one slot per
      -- node (`TitleTemplate.read`, `.native`). What the reader meets and
      -- does not model is one named loss, never a fallback.
      let (bodyArgs, k) := takeGroups raws j 1
      let fonts := (← get).beamerFonts.toList.map fun (n, fields) =>
        (n, beamerTemplateFont n fields)
      match TitleTemplate.read fonts (bodyArgs.getD 0 #[]) with
      | some rd@{ mixed := some datum, .. } =>
        -- A datum beside literal text has no slot to stand in, and a
        -- datum is never dropped: the template is not read, the built-in
        -- title page sets every datum, and that is the one named loss.
        let (sfx, msg, help) := TitleTemplate.mixedLoss datum rd.ground.isSome
        sayOnce ("beamer:setbeamertemplate:title page:" ++ sfx) .W0363 msg pos (help := help)
        -- The full-page fill is independent of the unread node arrangement:
        -- keep its ground while the built-in title layout stands.
        match rd.ground with
        | some ground =>
          let native := s!"\\palette\{ titlepagebg = {ground} }"
          return some (← synthAt native pos, k)
        | none => return some (#[], k)
      | some rd =>
        let native := TitleTemplate.native rd
        -- The theme's own fonts the template selects are honoured here:
        -- each skip their declarations drew is withdrawn, by its subject.
        -- premise: themeTitleShipChecks — a selected theme font's declared size reaches the page
        let skips := rd.fonts.map ("beamer:setbeamerfont:" ++ ·)
        write fun st => { st with diags := st.diags.filter fun d =>
          !(d.code == DiagCode.W0104.code && d.subject.any skips.contains) }
        became "\\setbeamertemplate{title page}" native pos
        unless rd.unread.isEmpty do
          sayOnce "beamer:setbeamertemplate:title page" .W0110
            s!"not read from the title-page template: \
{String.intercalate ", " rd.unread.toList}; the rest of it stands" pos
        -- What a node the engine cannot pin sets still ships, unpinned:
        -- the loss is the pin, named once per node by the data it sets.
        for data in rd.unplaced do
          let (sfx, msg, help) := TitleTemplate.unplacedLoss data
          sayOnce ("beamer:setbeamertemplate:title page:" ++ sfx) .W0363 msg pos (help := help)
        for (construct, datum) in rd.skipped do
          let (sfx, msg) := TitleTemplate.skippedLoss construct datum
          sayOnce ("beamer:setbeamertemplate:title page:" ++ sfx) .W0104 msg pos
        return some (← synthAt native pos, k)
      | none =>
      -- `\setbeamertemplate{title page}` IS beamer's spelling of
      -- `\renewcommand{\maketitle}`: `\titlepage` expands this template
      -- (beamerbasetitle.sty). So it routes to the native definer and lands
      -- under rule (b) — the gate the engine already runs on every
      -- redefinition of a rendered built-in. A body that elaborates
      -- non-empty wins and renders; one that loses is refused (W0361), the
      -- built-in title page stands, and the body is read once more for the
      -- declarative styling it carries (`applyRefusedTitleStyle`). Nothing
      -- is dropped, so E0111's `dropped` class is not the honest one here.
      -- The synthesised head is the *native* spelling: synthesised output
      -- is not walked again, so a synthesised `\renewcommand` would reach
      -- elaboration as an unknown command and take the body with it.
      became "\\setbeamertemplate{title page}" "\\define \\maketitle() {...}" pos
      write fun st => { st with bodyNext := 1 }
      return some (← synthAt "\\define \\maketitle()" pos, j)
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
  | "setbeamercolor" =>
    -- Keep relationships until elaboration: a later parent declaration
    -- changes its children, so flattening each declaration here is wrong.
    -- Elab accounts for unsupported sites after seeing their consumers.
    let j := skipStar raws start
    let (args, k) := takeGroups raws j 2
    if h : args.size = 2 then
      let element := (rawSrc args[0]).trimAscii.toString
      became s!"\\setbeamercolor\{{element}}" "named colour declaration in \\palette" pos
      let marker := if j == skipSpaces raws start then BeamerColor.marker
        else BeamerColor.starMarker
      return some (#[.ctrl marker pos, .group args[0] pos, .group args[1] pos], k)
    else return none
  | "ensuremath" =>
    -- Preserve the math-mode group for the math parser, including its
    -- containment accounting; text-mode rewrites do not own its commands.
    let (args, j) := takeGroups raws start 1
    if args.size != 1 then return none
    return some (#[.ctrl name pos] ++ raws.extract start j, j)
  | "raisebox" =>
    let (args, j) := takeGroups raws start 1
    if args.size != 1 then return none
    let (_, j) := takeOpts raws j 2
    sayOnce "ctrl:raisebox" .W0104
      "'\\raisebox' lift, height and depth are not applied; its content keeps the line's baseline" pos
      (help := "remove the box dimensions to use the surrounding line's natural spacing")
    return some (#[], j)
  | "mbox" | "makebox" =>
    -- An hbox's geometry is not modelled — neither command breaks lines, so
    -- neither reduces to a box of declared measure — and dropping it
    -- silently would move ink, so the drop is named once; the content stays
    -- in the stream.
    let (opts, widths) := match boxShape.lookup name with
      | some (o, w) => (o, w)
      | none => (0, 0)
    let (declared, j) := takeOpts raws start opts
    let (_, k) := takeGroups raws j widths
    if declared || widths > 0 then
      sayOnce ("ctrl:" ++ name) .W0104
        s!"'\\{name}' width and alignment are dropped; its content is kept" pos
        (help := "\\hfill spaces content apart; \\allow{W0104} accepts the drop")
    became s!"\\{name}" "its content, kept in the line" pos
    return some (#[], k)
  | "setbeamerfont" =>
    -- Store the fields once for mapped elements and template selection.
    -- `beamerbasefont.sty` merges nonstarred calls and clears starred
    -- ones, then selects the fields in `beamerFontKeys` order.
    let j := skipStar raws start
    let starred := j != start
    let (args, k) := takeGroups raws j 2
    if h : args.size = 2 then
      let element := (rawSrc args[0]).trimAscii.toString
      let source := rawSrc args[1]
      let stored := (← get).beamerFonts.toList.lookup element |>.getD []
      let previous := if starred then [] else stored
      let fields := beamerFontUpdate previous source
      unless element == "normal text" do
        write fun st => { st with
          beamerFonts := (st.beamerFonts.filter (·.1 != element)).push (element, fields)
          beamerCaptures := st.beamerCaptures + 1 }
      match beamerFontElements.lookup element with
      | none =>
        if element == "normal text" then
          -- Not a missing element: the document's own font is `\fonts`,
          -- and offering `\style` for something `\style` cannot reach
          -- would be a help text that does not help.
          sayOnce ("beamer:setbeamerfont:" ++ element) .W0104
            s!"'\\setbeamerfont\{{element}}' sets the document's font, which is \
not an element style; skipped" pos
            (help := "\\fonts selects the document's families; \
\\style{element}{ font = {...} } styles one element")
        else
          sayOnce ("beamer:setbeamerfont:" ++ element) .W0104
            s!"'\\setbeamerfont\{{element}}' names a beamer font element the engine \
has no styleable element for; skipped" pos
            (help := beamerNative.lookup "setbeamerfont")
        return some (#[], k)
      | some (target, styleKey) =>
        let updates := beamerFontUpdate [] source
        for (key, value) in updates do
          if key == "parent" then
            sayOnce ("beamer:setbeamerfont:" ++ element ++ ":" ++ key) .W0104
              s!"'\\setbeamerfont\{{element}}' inherits with '{key}'; the engine has \
no font inheritance, so only declared commands are taken" pos
              (help := beamerNative.lookup "setbeamerfont")
          else if key == "size*" && (braceGroups value).size != 2 then
            sayOnce ("beamer:setbeamerfont:" ++ element ++ ":" ++ key) .W0104
              s!"'\\setbeamerfont\{{element}}' needs two braced dimensions for 'size*'; \
its value is skipped" pos
              (help := "write size*={font size}{baseline distance}")
          else if !beamerFontKeys.contains (beamerFontAxis key) then
            -- An unknown field is data, never template text.
            sayOnce ("beamer:setbeamerfont:" ++ element ++ ":" ++ key) .W0104
              s!"'\\setbeamerfont\{{element}}' key '{key}' is not a beamer font key; \
its value is skipped" pos
              (help := beamerNative.lookup "setbeamerfont")
        -- premise: beamerTemplateChecks — an empty declared field clears
        -- that field; unknown fields alone leave the native style intact.
        if starred || updates.any (fun e => beamerFontKeys.contains (beamerFontAxis e.1)) then
          -- premise: beamerTemplateChecks — a preamble group's font fields
          -- are usable inside it, but no native style escapes its scope.
          if !(← get).inDoc && ((← get).inGroup || !(← get).beamerScopes.isEmpty) then
            became s!"\\setbeamerfont\{{element}}" "local font fields" pos
            return some (#[], k)
          let cmds := beamerFontCommands fields
          let native := s!"\\style\{{target}}\{ {styleKey} = \{{cmds}} }"
          became s!"\\setbeamerfont\{{element}}" native pos
          return some (← synthAt native pos, k)
        else return some (#[], k)
    else return none
  | "tikz" =>
    -- TikZ's inline picture (pgfmanual §12.2.2): `\tikz[opts]{commands}`, or
    -- `\tikz[opts]` and one command up to its `;`. It is the picture a
    -- `{tikzpicture}` with that body is, so it becomes that one node, read
    -- by the picture arm — drawn natively or at the boundary — and never
    -- text that prints its own path code.
    let (_, j) := takeOpts raws start 1
    let opts := raws.extract start j
    let k0 := skipSpaces raws j
    let body? : Option (Array Raw × Array Raw × Nat) := match raws[k0]? with
      | some (.group body _) => some (body, #[], k0 + 1)
      | _ => tikzCommand raws k0
    match body? with
    | some (body, rest, k) =>
      became "\\tikz" "\\begin{tikzpicture}...\\end{tikzpicture}" pos
      return some (#[.env "tikzpicture" (opts ++ body) pos] ++ rest, k)
    | none => return none
  | "columnratio" =>
    let (args, j) := takeGroups raws start 1
    let (right, k) := takeOpt raws j
    if args.isEmpty then return none
    let src := rawSrc (args.getD 0 #[])
    if let some ratio := paracolRatio? src then
      write fun st => { st with paracolRatio := ratio }
    else
      sayOnce "paracol:ratio" .W0104
        s!"cannot read two-column ratio '{src}'; the previous ratio stands" pos
        (help := "write one fraction between zero and one, like \\columnratio{0.35}")
    if right.isSome then
      sayOnce "paracol:right-ratio" .W0104
        "'\\columnratio{...}[...]' declares a paired-page ratio; the same-page ratio is used" pos
    became "\\columnratio" "the widths of the next two-column flow" pos
    return some (#[], k)
  | "switchcolumn" =>
    -- premise: columnGeometryChecks — the enclosing flow consumes the
    -- switch as a column boundary and both artifacts retain its content.
    if (← get).inParacol then return none
    let (_, j) := takeOpt raws start
    let js := skipSpaces raws j
    let starred := raws[js]? matches some (.word "*" _)
    let (_, k) := if starred then takeOpt raws (skipSpaces raws (js + 1)) else (none, j)
    sayOnce "paracol:switch-outside" .W0104
      "'\\switchcolumn' stands outside a supported two-column paracol flow; ignored" pos
    return some (#[], k)
  | "parbox" =>
    -- `\parbox{w}{t}` and `{minipage}{w}` are the same box: latex.ltx builds
    -- both through `\@iiiparbox`, and the manual's own difference is what a
    -- body may contain, not what the box measures. So the width is honoured
    -- rather than dropped — the environment carries it to `Ir.BoxWidth`
    -- through the one width reader — and the `[pos][height][inner-pos]`
    -- options travel with it, read where the environment reads its own.
    let (_, j) := takeOpts raws start 3
    let (args, k) := takeGroups raws j 2
    became "\\parbox" "\\begin{minipage}{<width>}...\\end{minipage}" pos
    -- The environment node directly, not synthesised source: the width group
    -- and the body are already parsed raws, and a `\begin` spelled as text
    -- would have to be re-parsed against its own `\end` to become an
    -- environment at all.
    let widthGroup : Array Raw := #[.group (args[0]?.getD #[]) pos]
    return some (#[.env "minipage" (raws.extract start j ++ widthGroup ++ (args[1]?.getD #[])) pos], k)
  | "footercontent" =>
    -- The gemini poster lineage's footer declaration
    -- (beamerthemegemini.sty, footline template: one centred line of the
    -- author's content across the page bottom): the engine's running
    -- foot is the same furniture slot, so the body group stays in the
    -- stream and `\runningfoot` takes it — the
    -- `\setbeamertemplate{frame footer}` shape.
    became "\\footercontent" "\\runningfoot{...}" pos
    return some (← synthAt "\\runningfoot" pos, start)
  | "usetheme" =>
    let (opt, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    let tname := (rawSrc (args.getD 0 #[])).trimAscii.toString
    let tname := themeAlias tname
    let native := s!"\\theme\{{tname}}"
    became "\\usetheme" native pos
    -- Only a theme the engine ships turns the themed mappings on: an
    -- unknown name leaves the document unthemed (W0314 says so), and
    -- \alert keeps its unthemed bold stand-in.
    if (Theme.find? tname).isSome then
      write fun st => { st with themed := true }
    let options ← if tname == "moloch" then molochOptions "\\usetheme" (opt.getD "") pos
      else pure #[]
    return some ((← synthAt native pos) ++ options, k)
  | "molochset" =>
    let (args, k) := takeGroups raws start 1
    if h : args.size = 1 then
      return some (← molochOptions s!"\\{name}" (rawSrc args[0]) pos, k)
    else return none
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
  | "multicolumn" =>
    -- `\multicolumn{n}{spec}{text}`. Where the tabular arm reads it — the
    -- top level of a tabular body — or where the use site decides — the
    -- head of a definition body, which a use at a cell's head expands —
    -- the construct stays whole, for the elaborator to set as a span; the
    -- groups after it are walked like any, so a `#1` in the text is the
    -- definition's parameter.
    -- premise: multicolumnSpanChecks — the tabular arm sets what this keeps,
    -- at a cell's head or by name where it does not open one
    if (← get).tableTop || ((← get).defTop && skipSpaces raws 0 + 1 == start) then
      return none
    -- Anywhere else — mid-cell, inside a group, outside a tabular body —
    -- no span is set (LaTeX refuses the first two, "Misplaced \omit"). The
    -- count and the spec are consumed and named, one line for every shape
    -- since every shape loses the same: its text stays where it stands,
    -- walked like any group, without a span or an alignment.
    let (gs, k) := takeGroups raws start 2
    let j := skipSpaces raws k
    match gs, raws[j]? with
    | #[_, _], some (.group _ _) =>
      sayOnce "ctrl:multicolumn:misplaced" .W0337 multicolumnMisplaced pos
        (help := multicolumnMisplacedHelp)
      return some (#[], j)
    | _, _ => return none
  | "usefonttheme" =>
    -- beamer's `professionalfonts` theme turns beamer's font substitution
    -- off and keeps the document's declared fonts — the only behaviour this
    -- engine has, so the ask is agreement, not missing configuration.
    -- Every other font theme would change fonts, and warns with the native
    -- spelling.
    let (_, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    if (rawSrc (args.getD 0 #[])).trimAscii.toString == "professionalfonts" then
      discard "\\usefonttheme{professionalfonts}"
        "the engine always uses the declared fonts" "usefonttheme" pos
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
      discard "\\setbeameroption{hide notes}"
        "notes never enter the delivered pages" "setbeameroption" pos
    else
      sayOnce "beamer:setbeameroption" .W0104
        "'\\setbeameroption' is beamer configuration the engine does not have; skipped" pos
        (help := "a theme is a token bundle here: \\theme selects one, and \\palette \
and \\tokens declare the design directly")
    return some (#[], k)
  | "setbeamercovered" =>
    -- beamer's default covering is invisible and `transparent` makes it
    -- show dimmed; this engine's covering is dim-not-hide always (PLAN
    -- M5). `transparent=<n>` shows covered text at n% opaqueness (beamer
    -- manual, \setbeamercovered: 0 transparent .. 100 opaque), and
    -- `transparent` alone is n = 15, the key's default
    -- (beamerbaseoverlay.sty: `\define@key{beamer@mixin}{transparent}[15]`):
    -- exactly the engine's covered fraction, so the two spellings are one
    -- idea — `\palette{ covered = n% }`, each covered colour kept at n% of
    -- itself over the page, in Oklab, inside the ink bound of beamer's
    -- sRGB mixin (`inkBoundChecks` holds a covered run to it). Everything
    -- else (invisible, dynamic, still/again covered) asks for hiding or
    -- per-slide opacity the engine deliberately does not do.
    let (args, k) := takeGroups raws start 1
    let src := (rawSrc (args.getD 0 #[])).trimAscii.toString
    let pct? : Option Nat :=
      if src == "transparent" then some 15
      else if src.startsWith "transparent=" then
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
  | "KOMAoptions" =>
    -- KOMA's runtime option setter (KOMA-Script manual, \KOMAoptions;
    -- switches take true/on/yes and false/off/no). headsepline and
    -- footsepline off ask for no separation rule, the only state the
    -- engine draws — agreement; every other entry is a dropped option,
    -- named (W0101's shape). An empty argument is the guard's W0387.
    let (args, k) := takeGroups raws start 1
    let entries := (Decl.splitEntries (rawSrc (args.getD 0 #[]))).map
      (·.trimAscii.toString) |>.filter (!·.isEmpty)
    let satisfied (e : String) : Bool :=
      match (e.splitOn "=").map (·.trimAscii.toString) with
      | [key, v] => (key == "headsepline" || key == "footsepline")
          && (v == "false" || v == "off" || v == "no")
      | _ => false
    let dropped := entries.filter (!satisfied ·)
    if dropped.isEmpty then
      unless entries.isEmpty do
        discard "\\KOMAoptions" "no head or foot separation rule is drawn" "KOMAoptions" pos
    else
      say .W0101 s!"'\\KOMAoptions' entries without a native equivalent were \
dropped: {String.intercalate ", " dropped}" pos
    return some (#[], k)
  | "column" =>
    -- beamer's command form splits a `{columns}` body where it stands
    -- (beamer user guide §12.7); at that body's top level `splitColumns`
    -- has already made it the environment form, so a `\column` reaching
    -- this arm is somewhere else — outside `{columns}`, or nested in a
    -- group inside it — where beamer itself starts no column.
    let (_, k) := takeGroups raws start 1
    sayOnce "ctrl:column" .W0104
      "'\\column' is not at the top level of a {columns} body; it starts \
no column there and is skipped" pos
      (help := "\\column{width} splits the body of \\begin{columns} ... \\end{columns}")
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
      configSkipReport name pos msg help
      return some (#[], k)
    | none =>
    -- A size command at the preamble's top level sets nothing LaTeX keeps:
    -- `\begin{document}` runs `\normalsize` (measured under lualatex: the
    -- preamble's `\baselineskip` and display skips are gone in the body).
    if (Ir.sizeScale.lookup name).isSome && (← docPreamble) then
      discard s!"\\{name}" "'\\begin{document}' runs '\\normalsize', which sets the size again"
        ("size:" ++ name) pos
      return some (#[], start)
    match meaningFree.lookup name with
    | some (n, note) =>
      let (_, k) := takeGroups raws start n
      meaningFreeReport name pos note
      return some (#[], k)
    | none => return none

/-- The later half of `rewriteCtrl`'s dispatch, with local style option
requests preceding its named arms, exactly as in the source execution order. -/
private def rewriteCtrlLater (name : String) (pos : Pos) (raws : Array Raw)
    (start : Nat) : M (Option (Array Raw × Nat)) := do
  if let some result ← styOptionsRequest name pos raws start then return some result
  rewriteCtrlLaterNamed name pos raws start

/-- The dispatcher's silence guard: an arm answered `some` with no
replacement tokens — the construct is consumed — so the consumption must
have been paid for against the entry snapshot `s0`: a diagnostic
(`diags` grew) or a state write (`writes` grew). Neither grown is the
class W0387 names — the engine knows this command and did nothing with
what it read (distinct from W0301, unknown, and from W0104, a known
refusal with its reason). Warned once per name (sayOnce's policy); a
repeat is accounted as a write. Both branches land on the snapshot's
values: under the guard's own condition the arm grew neither counter,
and every arm only appends, so the snapshot is the live value — spelled
this way, `rewriteCtrl_accounts` closes by unfolding the guard alone,
with every arm opaque. State-explicit (no do-notation) for the same
reason: the theorem reads it with no monad lemmas. -/
private def account (name : String) (pos : Pos) (s0 : St) : M Unit := fun st =>
  if st.diags.size > s0.diags.size ∨ st.writes > s0.writes then ((), st)
  else if st.warned.contains ("silent:" ++ name) then
    -- Named at its first occurrence: the repeat is accounted against the
    -- snapshot — sayOnce's once-per-construct policy, the guard's way.
    ((), { st with writes := s0.writes + 1 })
  else
    ((), { st with
      warned := st.warned.push ("silent:" ++ name)
      diags := s0.diags.push (atSource st pos (Diag.of .W0387
        s!"'\\{name}' was read and had no effect" (some ⟨st.file, pos⟩)
        (help := "\\allow{W0387} accepts the skip")
        (subject := some ("ctrl:" ++ name)))) })

/-- The mark the rewrite sets before a deck's `\appendix` when appendixnumberbeamer is
loaded: the frame count starts over there (`appendixnumberbeamer.sty`: its `\appendix`
keeps the main part's last number as the total and sets `framenumber` to 0). A space is
in no control word, so no document spells the mark. -/
public def frameRestartMark : String := "appendix restart"

/-- The mark a cancel package load leaves in the preamble, its option list in
the group after it: the elaborator's preamble reads it into the context every
formula's marks read (`Ctx.cancel`). A space is in no control word, so no
document spells the mark. -/
public def cancelOptionsMark : String := "cancel options"

/-- Interpret one package in the loading call's declared order. The caller
owns the option and group readers; this producer owns each package's exact
native replacement or refusal record. Keeping the scalar transition named
lets the request contract read its diagnostic without expanding the whole
control dispatcher. -/
private def rewritePackageBody (name p : String) (opt : Option String) (pos : Pos) :
    M (Array Raw) := do
  let mut out : Array Raw := #[]
  if p == "geometry" then
    out := out ++ (← geometry (opt.getD "") pos)
  else if p == "crop" then
    out := out ++ (← crop (opt.getD "") pos)
  else if p == "beamerposter" then
    out := out ++ (← beamerposter (opt.getD "") pos)
  else if p == "parskip" then
    -- The package sets `\parskip` to half a line plus 2pt and drops the
    -- indent; the half line is what changes the page.
    let native := "\\page{ parskip = 0.6em plus 2pt }"
    became "\\usepackage{parskip}" native pos
    out := out ++ (← synthAt native pos)
  else if p == "amsthm" then
    -- amsthm's documented default style is plain (amsthm manual §4:
    -- `plain` is in force until a `\theoremstyle`), which is also what
    -- tells the elaborator amsthm's heads and its `proof` are in force.
    let native := "\\theoremstyle{plain}"
    became "\\usepackage{amsthm}" native pos
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
        write fun st => { st with mainLang := tag }
        out := out ++ (← synthAt native pos)
      else
        say .W0368 s!"no locale for language '{main}'; English \
captions and patterns stand in" pos
          (help := "the engine ships locale records for: en, fr, de")
    | none =>
      discard s!"\\{name}\{{p}}" "the engine does this itself" s!"{name}:{p}" pos
  else if p == "natbib" then
    out := out ++ (← natbibLoad name (opt.getD "") pos)
  else if p == "biblatex" then
    -- biblatex's style options (biblatex manual §3.1.1: style defaults
    -- to numeric, sorting to nty — name-title-year) select onto the
    -- same four-axis record door natbib's \bibliographystyle opens:
    -- numeric over a name-sorted list is `plain`, numeric over
    -- citation order (sorting=none) is `unsrt`, authoryear is
    -- `plainnat`. A style outside the record set (alphabetic labels)
    -- is W0353's meaning, judged here where the author wrote the
    -- name, with unsrtnat standing in.
    let opts := ((opt.getD "").splitOn ",").map (·.trimAscii.toString)
    let pick (key dflt : String) : String := opts.foldl (init := dflt) fun acc kv =>
      match (kv.splitOn "=").map (·.trimAscii.toString) with
      | [k, v] => if k == key then v else acc
      | _ => acc
    let style := pick "citestyle" (pick "style" "numeric")
    let mapped :=
      if style.startsWith "numeric" then
        some (if pick "sorting" "nty" == "none" then "unsrt" else "plain")
      else if style.startsWith "authoryear" then some "plainnat"
      else none
    match mapped with
    | some s =>
      became s!"\\usepackage[style={style}]\{biblatex}"
        s!"\\bibliographystyle\{{s}}, at \\printbibliography" pos
      write fun st => { st with bibStyle := some s }
      -- The citations are biblatex's (`Bib.CitePunct.biblatex`). The numeric
      -- styles take the plain row through the open door; authoryear's
      -- round brackets and semicolons are natbib's own load values, the
      -- style's square-bracket row shut out, and its name and year stand
      -- apart by a space alone (`\nameyeardelim`).
      natbibDefer (if s == "plainnat" then #["nobibstyle", "aysep=", "biblatex"]
        else #["biblatex"]) pos
    | none =>
      say .W0353 s!"bibliography style '{style}' is not one the engine \
knows; the reference list is set as 'unsrtnat'" pos
        (help := "styles known: unsrtnat, unsrt, plainnat, plain, abbrvnat, abbrv")
      write fun st => { st with bibStyle := some "unsrtnat" }
  else if let some spec := fontPackages.lookup p then
    -- carlito's `sfdefault` promotes its sans face to the body slot
    -- (carlito README); every other option (psnfss's `scaled=`) asks
    -- for a face adjustment the engine does not model and is dropped
    -- by name.
    let opts := ((opt.getD "").splitOn ",").map (·.trimAscii.toString)
      |>.filter (!·.isEmpty)
    let sfdefault := p == "carlito" && opts.contains "sfdefault"
    let spec := if sfdefault then spec ++ ", body = \"Carlito\"" else spec
    let dropped := opts.filter (· != "sfdefault")
    unless dropped.isEmpty do
      say .W0101 s!"'{p}' options without a native equivalent were \
dropped: {String.intercalate ", " dropped}" pos
    let native := s!"\\fonts\{ {spec} }"
    became s!"\\usepackage\{{p}}" native pos
    out := out ++ (← synthAt native pos)
  else if p == "lineno" && opt.isSome then
    out := out ++ (← linenoLoad (opt.getD "") pos)
  else if p == "cancel" then
    -- The package's options are the marks' own settings, read where a
    -- formula draws one: carried as data to the elaborator's preamble
    -- (`cancelOptionsMark`), each named option read as the package's
    -- `\ProcessOptions` reads it, an undeclared one named and dropped.
    let opts := ((opt.getD "").splitOn ",").map (·.trimAscii.toString)
      |>.filter (!·.isEmpty)
    let (_, unknown) := Math.CancelSpec.ofOptions opts
    unless unknown.isEmpty do
      say .W0101 s!"'cancel' options without a native equivalent were \
dropped: {String.intercalate ", " unknown}" pos
    became s!"\\usepackage\{cancel}"
      "the cancel marks, drawn from the math font's own rule constants" pos
    out := (out.push (.ctrl cancelOptionsMark pos)).push
      (.group (if opts.isEmpty then #[] else #[.word (String.intercalate "," opts) pos]) pos)
  else if p == "animate" then
    -- animate manual §6 allows package-wide animation defaults. This
    -- scoped lowering reads only each command's own options.
    -- premise: animatedGraphicsChecks — local posters select distinct
    -- shipped images, and package defaults keep their named warning.
    let opts := (opt.getD "").trimAscii.toString
    if opts.isEmpty then
      discard s!"\\{name}\{{p}}"
        "whole multipage animations are read at each '\\animategraphics' command"
        s!"{name}:{p}" pos
    else
      sayOnce "animate:package-options" .W0110
        s!"'animate' package options '{opts}' are not applied" pos
        (help := "put poster and size options on each '\\animategraphics'; playback settings remain unsupported")
  else if p == "markdown" then
    -- premise: markdownInputChecks — the driver reads native
    -- fragments, and unsupported package options keep their warning.
    let opts := (opt.getD "").trimAscii.toString
    if opts.isEmpty then
      discard s!"\\{name}\{{p}}"
        "native Markdown fragments are read at each '\\markdownInput' command"
        s!"{name}:{p}" pos
    else
      sayOnce "markdown:package-options" .W0110
        s!"'markdown' package options '{opts}' are not applied; \
no package options are supported by the strict native Markdown dialect" pos
        (help := "remove the package options")
  else if p == "unicode-math" && opt.isSome then
    out := out ++ (← unicodeMathOptions
      s!"\\{name}[{opt.getD ""}]\{unicode-math}" (opt.getD "") pos)
  else if p == "hyperref" && opt.isSome then
    -- hyperref's package options are `\hypersetup`'s keys; the link
    -- colours become the link kinds' `\style` colours, the rest are the
    -- viewer's, discarded as before.
    let mut links := (← get).links
    let mut linked := false
    for o in (opt.getD "").splitOn "," do
      match o.splitOn "=" with
      | k :: v =>
        if let some l := links.read k.trimAscii.toString
            (String.intercalate "=" v).trimAscii.toString then
          links := l
          linked := true
      | [] => pure ()
    if linked then write fun st => { st with links }
    if linked && links.colorlinks then
      let native := links.native
      became s!"\\usepackage[{opt.getD ""}]\{hyperref}" native pos
      out := out ++ (← synthAt native pos)
    else
      discard s!"\\{name}\{{p}}" "the engine does this itself" s!"{name}:{p}" pos
  else if p == "ulem" then
    let opts := ((opt.getD "").splitOn ",").map (·.trimAscii.toString)
      |>.filter (!·.isEmpty)
    if opts == ["normalem"] then
      discard s!"\\{name}[normalem]\{{p}}"
        "strikeout is native and normal emphasis remains in force"
        s!"{name}:{p}:normalem" pos
    else
      say .W0103 "package 'ulem' without only the 'normalem' option changes \\emph; skipped"
        pos (help := "use \\usepackage[normalem]{ulem} for native \\sout")
        (refused := some p)
  -- premise: tableFaceOrderChecks — the face declared before the load and
  -- after it ship byte-identical pages and only the warning below moves, so
  -- nothing else measures the declared face
  else if p == "booktabs" && (← get).facesDeclared.contains
      (if (← get).deck then "sans" else "body") then
    -- booktabs fixes its rule weights and paddings in the font current where
    -- it loads (`Ir.PreambleFace`): after the preamble family's face is
    -- declared, that face, which the engine does not measure. The load is
    -- the site of the loss, so its one accounting is this warning.
    let (face, cmd) := if (← get).deck then ("sans", "\\setsansfont")
      else ("main", "\\setmainfont")
    say .W0398 s!"'\\{name}\{booktabs}' follows the {face} face's declaration; \
its rule paddings are measured in Latin Modern" pos
      (help := some s!"load booktabs before '{cmd}', where LaTeX measures them in Latin Modern too")
      (subject := some "package:booktabs")
  else if nativePackages.contains p then
    discard s!"\\{name}\{{p}}" "the engine does this itself" s!"{name}:{p}" pos
  else if boundaryPkgs.contains p && (← get).boundaryOpen then
    -- A picture package's load is the boundary's: `boundaryDecls`
    -- carried it, with its options, into every wrapped standalone,
    -- where the real TeX reads it — W0103 would misname a load the
    -- engine consumes. A declared refusal (`tool = none`) restores
    -- the named loss.
    became s!"\\{name}\{{p}}"
      "the boundary standalone's preamble; each picture outside the \
rendered subset is drawn whole at the boundary" pos
  else if let some (slot, _, nm) := themeSlotOfPackage? p then
    -- beamer's own identity, read backwards: `beamerthemeX` **is**
    -- `\usetheme{X}` (beamerbasethemes.sty defines the family through
    -- the package loader), and a theme inheriting another writes that
    -- file name. W0103 answered it as a CTAN support question, so a
    -- bundle the engine ships was refused under the one spelling an
    -- inheriting theme uses. The candidate scan has already offered
    -- `p.sty`; reaching here means no file answered, so what is left
    -- is the slot's own meaning.
    if slot == "usetheme" then
      let nm := themeAlias nm
      let native := s!"\\theme\{{nm}}"
      became s!"\\{name}\{{p}}" native pos
      if (Theme.find? nm).isSome then
        write fun st => { st with themed := true }
      out := out ++ (← synthAt native pos)
    else
      -- The four sub-theme slots have no bundle of their own here: a
      -- token bundle is whole. Their file name gets the slot's named
      -- configuration warning, which is what the slot spelling gets —
      -- never a claim about package support.
      sayOnce ("beamer:" ++ slot) .W0104
        s!"'\\{slot}' is beamer configuration the engine does not have; skipped" pos
        (help := (beamerNative.lookup slot).getD
          "a theme is a token bundle here: \\theme selects one, and \\palette \
and \\tokens declare the design directly")
  else
    say .W0103 s!"package '{p}' is not supported; skipped" pos
      (refused := some p)
  return out

/-- Admit a native package before installing its defaults. Local files use
the same gate before their input fragment executes. Missing packages still
reach their existing refusal, without reserving a name that never loaded.
Option passes are read in rewrite order, not from the execution phase's
final list, so a later pass cannot change an earlier installation. -/
private def rewritePackage (name p : String) (opt : Option String) (pos : Pos) :
    M (Array Raw) := do
  if nativePackages.contains p then
    let passed := (← get).loads.rewritePassed.toList.flatMap fun (q, os) =>
      if q == p then os.toList else []
    let some options ← admitPackage p (PackageImports.literalOptions (opt.getD "")) passed pos
      | return #[]
    let opt := if passed.isEmpty then opt else some (String.intercalate "," options)
    rewritePackageBody name p opt pos
  else
    rewritePackageBody name p opt pos

/-- The real native producer returns no declarations on a compatible
repeat and preserves every semantic field, even after intervening commands
changed a default the first load installed. -/
private theorem rewritePackage_compatible_exact (name p : String) (opt : Option String)
    (pos : Pos) (st : St) (first : List String)
    (native : nativePackages.contains p = true)
    (loaded : st.loads.imports.lookup p = some first)
    (compatible : ∀ o ∈ PackageImports.literalOptions (opt.getD ""),
      o ∈ first ++ st.loads.rewritePassed.toList.flatMap
        (fun (q, os) => if q == p then os.toList else [])) :
    rewritePackage name p opt pos st = (#[], { st with writes := st.writes + 1 }) := by
  simp only [rewritePackage, native, ↓reduceIte, bind, StateT.bind,
    get, getThe, MonadStateOf.get, StateT.get, pure]
  rw [admitPackage_compatible_exact _ _ _ _ _ _ loaded compatible]
  rfl

/-- The external-package refusal's whole record, before the source index
adds its trigger. Native package options are judged by their own producer;
sharing W0103 does not make them failed file requests. -/
public def packageRefusal (file : String) (pos : Pos) (p : String) : Diag :=
  Diag.of .W0103 s!"package '{p}' is not supported; skipped"
    (some ⟨file, pos⟩) (refused := some p)

private theorem atSource_package_exact (st : St) (pos : Pos) (p : String) :
    atSource st pos (packageRefusal st.file pos p) =
      st.sourceTriggers.attribute (packageRefusal st.file pos p) := by
  simp [atSource, SourceTriggers.atSource, SourceTriggers.attribute,
    packageRefusal, Diag.of_record_exact]

private theorem rewritePackage_external_exact (name p : String)
    (opt : Option String) (pos : Pos) (st : St)
    (hn : nativePackages.contains p = false)
    (hb : (boundaryPkgs.contains p && st.boundaryOpen) = false)
    (ht : themeSlotOfPackage? p = none) :
    rewritePackage name p opt pos st =
      (#[], { st with diags := st.diags.push (atSource st pos (packageRefusal st.file pos p)) }) := by
  have hn' := hn
  simp only [nativePackages, List.contains_cons, List.contains_nil,
    Bool.or_eq_false_iff] at hn'
  have hf : fontPackages.lookup p = none := by
    simp_all [List.lookup_eq_none_iff, fontPackages]
  have hnmem : p ∉ nativePackages := by simpa using hn
  have hbmem : ¬(p ∈ boundaryPkgs ∧ st.boundaryOpen = true) := by simpa using hb
  simp [rewritePackage, rewritePackageBody, hf, hnmem, ht, hn']
  dsimp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure]
  simp only [hbmem, ↓reduceIte]
  rfl

/-- The package-loading arm's production loop. Each spelling in one
comma-separated operand is judged in order against the same current
compatibility state. -/
private def rewritePackages (name : String) (pkgs : List String)
    (opt : Option String) (pos : Pos) : M (Array Raw) := do
  let mut out : Array Raw := #[]
  for p in pkgs do
    out := out ++ (← rewritePackage name p opt pos)
  return out

private theorem rewritePackages_external_exact (name : String)
    (pkgs : List String) (opt : Option String) (pos : Pos) (st : St)
    (hn : ∀ p ∈ pkgs, nativePackages.contains p = false)
    (hb : ∀ p ∈ pkgs, (boundaryPkgs.contains p && st.boundaryOpen) = false)
    (ht : ∀ p ∈ pkgs, themeSlotOfPackage? p = none) :
    rewritePackages name pkgs opt pos st =
      (#[], { st with diags := st.diags ++
        (pkgs.map fun p => atSource st pos (packageRefusal st.file pos p)).toArray }) := by
  have loop :
      ∀ (xs : List String) (out : Array Raw) (s : St),
        (∀ p ∈ xs, nativePackages.contains p = false) →
        (∀ p ∈ xs, (boundaryPkgs.contains p && s.boundaryOpen) = false) →
        (∀ p ∈ xs, themeSlotOfPackage? p = none) →
        ((forIn xs out fun p acc => do
          let repl ← rewritePackage name p opt pos
          pure (.yield (acc ++ repl))) : M (Array Raw)) s =
          (out, { s with diags := s.diags ++
            (xs.map fun p => atSource s pos (packageRefusal s.file pos p)).toArray }) := by
    intro xs
    induction xs with
    | nil =>
      intro out s _ _ _
      simp only [List.forIn_nil, pure, StateT.pure, List.map_nil,
        List.toArray, Array.append_empty]
    | cons p ps ih =>
      intro out s hn hb ht
      rw [List.forIn_cons]
      simp only [bind, StateT.bind, pure, StateT.pure,
        rewritePackage_external_exact name p opt pos s
          (hn p List.mem_cons_self) (hb p List.mem_cons_self) (ht p List.mem_cons_self),
        Array.append_empty]
      let next : St :=
        { s with diags := s.diags.push (atSource s pos (packageRefusal s.file pos p)) }
      have tail := ih out next (fun q hq => hn q (List.mem_cons_of_mem _ hq))
        (fun q hq => hb q (List.mem_cons_of_mem _ hq))
        (fun q hq => ht q (List.mem_cons_of_mem _ hq))
      calc
        _ = (out, { next with diags := next.diags ++
            (ps.map fun q => atSource next pos (packageRefusal next.file pos q)).toArray }) :=
          tail
        _ = _ := by
          change (out, { s with diags := (
            s.diags.push (atSource s pos (packageRefusal s.file pos p)) ++
              (ps.map fun q => atSource s pos (packageRefusal s.file pos q)).toArray) }) = _
          rw [List.push_append_toArray, List.map_cons]
  have h := loop pkgs #[] st hn hb ht
  unfold rewritePackages
  simp only [bind, StateT.bind, pure, StateT.pure]
  simp only [bind, pure] at h
  rw [h]

/-- Named arms after the dispatcher's state-dependent guards. Registry
contracts quantify over this actual match: an ordinary body control emits
no replacement, consumes its declared argument prefix, and leaves the
continuation at the first unconsumed token. No dispatch order changes. -/
private def rewriteCtrlNamed (name : String) (pos : Pos) (raws : Array Raw)
    (start : Nat) : M (Option (Array Raw × Nat)) := do
  match name with
  | "usepackage" | "RequirePackage" =>
    -- One dispatch for both spellings: `\RequirePackage` is `\usepackage`
    -- for package writers (ltclass.dtx), and a local `.sty` spliced into
    -- the preamble spells its loads that way.
    -- Replacement text is stored, not a load. Actual uses have already
    -- expanded through the execution reader (`condLiveRaw`).
    if (← get).inDef then return none
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
    let out ← rewritePackages name pkgs opt pos
    return some (out, k)
  | "PassOptionsToPackage" | "PassOptionsToClass" =>
    if (← get).inDef then return none
    let (args, k) := takeGroups raws start 2
    if args.size != 2 then return none
    let options := (PackageImports.literalOptions (rawSrc (args.getD 0 #[]))).toArray
    let packages := optionItems (rawSrc (args.getD 1 #[]))
    write fun st => { st with loads := if name == "PassOptionsToClass" then
      { st.loads with
        rewriteClassPassed := st.loads.rewriteClassPassed ++ packages.map (·, options) }
      else { st.loads with rewritePassed := st.loads.rewritePassed ++ packages.map (·, options) } }
    discard s!"\\{name}\{...}\{...}" "load options are recorded" name pos
    return some (#[], k)
  | "documentclass" =>
    let (opt, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    let cls := rawSrc (args.getD 0 #[])
    if presentationClasses.contains cls then
      write fun st => { st with deck := true }
    let native := if articleClasses.contains cls then "article"
      else if resumeClasses.contains cls then "resume"
      else if cls == "beamer" then "slides" else cls
    let flow := ((Ir.DocClass.ofString? native).map (·.record.model == .flow)).getD true
    write fun st => { st with
      measureKnown := !flow, flowPage := flow,
      titlepageReset := !((opt.getD "").splitOn ",").any (·.trimAscii.toString == "twoside") }
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
      let passed := (← get).loads.rewriteClassPassed.toList.flatMap fun (name, options) =>
        if name == cls then options.toList else []
      let packages := classPackages cls (passed ++ PackageImports.literalOptions (opt.getD ""))
      let declaration ← synthAt s!"\\documentclass{o}\{slides}" pos
      let dependencies ← rewritePackages "RequirePackage" packages none pos
      return some (declaration ++ dependencies, k)
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
          (Decl.splitEntry kv).bind fun (key, v) =>
            if key == k then
              some (if v.startsWith "{" && v.endsWith "}" then
                ((v.drop 1).toString.dropEnd 1).toString.trimAscii.toString
              else v)
            else none
    let dirPart := match feature "Path" with
      | some d => s!"dir = \"{d}\", "
      | none => ""
    let mut parts := #[s!"{slot} = \"{family}\""]
    for (opt, variant) in [("UprightFont", "upright"), ("BoldFont", "bold"),
        ("ItalicFont", "italic"), ("BoldItalicFont", "bolditalic")] do
      if let some f := feature opt then
        -- fontspec's `*` stands for the family name (fontspec manual,
        -- "Choosing additional fonts": "may be replaced by *"):
        -- `UprightFont = *-Semibold` under `{Ordwick}` names "Ordwick-Semibold".
        let f := if f.startsWith "*" then family ++ (f.drop 1).toString else f
        parts := parts.push s!"{slot}.{variant} = \"{f}\""
    -- fontspec's `FontFace = {series}{shape}{font}`: one declared face per
    -- NFSS series/shape pair (fontspec sources: the `fontspec-preparse`
    -- FontFace key feeds `\__fontspec_add_nfssfont:nnnn` series, shape,
    -- font, features). Each entry becomes the native
    -- `slot.<series>[.italic]` declaration, so `\fontseries{l}` selects
    -- exactly the face the document named. What the engine has no axis or
    -- shape for is named, never silently dropped.
    for opts in [optBefore, optAfter].filterMap id do
      for kv in Decl.splitEntries opts do
        if let some ("FontFace", v) := Decl.splitEntry kv then
          if let some part := ← fontFacePart family slot v pos then
            parts := parts.push part
    if name == "babelfont" then
      if let some l := langOpt then
        say .W0369 s!"'\\babelfont[{l}]' binds a font per language; one \
face serves every language, so the binding is dropped" pos
          (help := "\\fonts{ body = \"...\" } names the face every language uses")
        return some (#[], k)
    let native := s!"\\fonts\{ {dirPart}{String.intercalate ", " parts.toList} }"
    became s!"\\{name}" native pos
    write fun st => { st with facesDeclared := st.facesDeclared.push slot }
    return some (← synthAt native pos, k)
  | "definecolor" =>
    let (args, k) := takeGroups raws start 3
    if h : args.size = 3 then
      let n := rawSrc args[0]
      let model := rawSrc args[1]
      let modeled := modeledColorSource (some model) (rawSrc args[2])
      let native := s!"\\palette\{ {n} = {modeled} }"
      let carried := s!"\\palette\{ {n} = {Decl.xcolorDefinitionPrefix}{modeled} }"
      became s!"\\definecolor\{{n}}" native pos
      return some (← synthAt carried pos, k)
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
  | "pagecolor" =>
    let (model, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    if h : args.size = 1 then
      let value := modeledColorSource model (rawSrc args[0])
      return some (← pageColor value pos, k)
    else return none
  | "nopagecolor" =>
    became "\\nopagecolor" "the document's default page ground" pos
    return some (#[.ctrl pageColorResetMark pos], start)
  | "geometry" | "newgeometry" =>
    -- The command forms: the same keys the package options carry
    -- (geometry manual §5: `\newgeometry` is `\geometry` restricted to
    -- the layout keys). One door for every spelling, so a key is honoured
    -- or named (W0101) identically wherever it was written.
    let (args, k) := takeGroups raws start 1
    if args.isEmpty then return none
    return some (← geometry (rawSrc (args.getD 0 #[])) pos s!"\\{name}", k)
  | "crop" =>
    -- The command form: the same options the package load carries, one
    -- door for both spellings. A bare `\crop` is `[cam,noaxes]`, the
    -- command's own default argument (crop.sty v1.10, `\newcommand*\crop`).
    let (opt, k) := takeOpt raws start
    return some (← crop (opt.getD "cam,noaxes") pos "\\crop" "crop", k)
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
  | "DocumentMetadata" =>
    let (args, k) := takeGroups raws start 1
    if h : args.size = 1 then
      return some (← documentMetadata (rawSrc args[0]) pos, k)
    else return none
  | "AddToHook" =>
    let (hookArgs, j) := takeGroups raws start 1
    let (_, j) := takeOpt raws j
    let (codeArgs, k) := takeGroups raws j 1
    let hook := rawSrc (hookArgs.getD 0 #[])
    if hook == "shipout/background" || hook == "shipout/foreground" then
      let st ← get
      let look (n : String) : Option (Array Raw) := match st.binds[n]? with
        | some (some v) => if v.arity == 0 then some v.raws else none
        | _ => none
      -- the lengths this level declared before the hook: what a rule's
      -- coordinates may name
      let lengths := (Array.range start).filterMap fun i => match raws[i]? with
        | some (Raw.ctrl "newlength" _) => (takeGroups raws (i + 1) 1).1[0]?.bind ctrlName
        | _ => none
      match shipoutRules look lengths (codeArgs.getD 0 #[]) with
      | some rules =>
        let entries := rules.map fun (x, y, w, h, c) => s!"rule = \"{x}; {y}; {w}; {h}; {c}\""
        let native := s!"\\page\{ {String.intercalate ", " entries.toList} }"
        became s!"\\AddToHook\{{hook}}" native pos
        return some (← synthAt native pos, k)
      | none => pure ()
    -- A page attribute assigned at shipout declares the page's boxes in
    -- values the engine cannot evaluate: the hook stays skipped, and named
    -- (W0104), and the trim the page's drawn cut marks cut stands for the
    -- boxes (`Ir.PageSpec.trimMarked`, `Layout.drawnTrim`).
    if hook == "shipout/before" && assignsPageAttr (codeArgs.getD 0 #[]) then
      addToHook pos
      return some (← synthAt "\\page{ trim = marks }" pos, k)
    addToHook pos
    return some (#[], k)
  | "setcounter" | "addtocounter" | "stepcounter" | "refstepcounter" =>
    -- LaTeX's counter commands are legal in the preamble, and what they
    -- set holds where the body starts (ltcounts.dtx): at a document's
    -- preamble top level the command moves there, to the one arm that
    -- reads counters in flow order. Anywhere else it stands.
    -- premise: counterChecks — a preamble counter numbers the body as the
    -- same command at the body's start does
    if !(← docPreamble) then return none
    let n := if name == "setcounter" || name == "addtocounter" then 2 else 1
    let (args, k) := takeGroups raws start n
    if args.size < n then return none
    let st ← get
    let cmd := raws.extract (start - 1) k
    let cmd := if st.file == st.docFile then cmd
      else #[Raw.env (Parse.inputEnv st.file) cmd pos]
    write fun st => { st with preCounters := st.preCounters ++ cmd }
    return some (#[], k)
  | "newlength" =>
    -- `\newlength{\x}` allocates a length register at 0pt (usrguide,
    -- "Defining lengths"); the native store is a token, so a later
    -- `\setlength{\x}` and references to `\x` in other lengths resolve.
    let (args, k) := takeGroups raws start 1
    let some n := ctrlName (args.getD 0 #[]) | return none
    return some (← setLength n "0pt" s!"\\newlength\{\\{n}}" pos, k)
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
      match paramName args[0] with
      | some n =>
        let target := (rawSrc args[0]).trimAscii.toString
        return some (← assignLength n args[1] s!"\\setlength\{{target}}" pos, k)
      | none => return none
    else return none
  | "addtolength" =>
    -- LaTeX's spelling of `\advance` (usrguide, "Changing lengths"): the
    -- sum of the value the length holds and the operand, where both are
    -- known; otherwise the command stands, named by the elaborator.
    let (args, k) := takeGroups raws start 2
    if h : args.size = 2 then
      let some n := ctrlName args[0] | return none
      let st ← get
      -- premise: registerArithChecks — a length this rewrite set holds the
      -- value it recorded
      match (st.lens.find? (·.1 == n)).map (·.2),
          lenOperand st.lens (args[1].toList.filter (!· matches .space)) with
      | some p, some v =>
        -- premise: composedLengthChecks — a sum the grammar reads is the
        -- value the declaration holds; one it cannot is named, never handed on
        let expr := s!"({p}) + {v}"
        if Decl.readsAsLengthExpr expr then
          return some (← setLength n expr s!"\\addtolength\{\\{n}}" pos, k)
        sayOnce "ctrl:addtolength" .W0104
          s!"'\\addtolength' on a value the length grammar cannot compose ('{expr}'): \
skipped, and the length keeps its value" pos
          (demote := styInternal (← get).file name)
        return some (#[], k)
      | _, _ =>
        -- The value the length holds is its class's, or the addend is one
        -- the door cannot read: the sum is unknown here. In a definition's
        -- body the command stands, for the use to read.
        if (← get).inDef then return none
        return some (← unreadableLength n
          s!"\\{n} + {(rawSrc args[1]).trimAscii.toString}" pos, k)
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
        | some (.word "-" _) =>
          match raws[j2 + 1]? with
          | some (.ctrl _ _) => j2 + 2
          | _ => j2 + 1
        | some (.word _ _) => j2 + 1
        | some (.ctrl _ _) =>
          match raws[j2 + 1]? with
          | some (.ctrl _ _) => j2 + 2
          | _ => j2 + 1
        | some (.sym '-' _) =>
          match raws[j2 + 1]? with
          | some (.ctrl _ _) | some (.word _ _) => j2 + 2
          | _ => j2 + 1
        | _ => j2
      -- A length this rewrite set is evaluated from the value it holds,
      -- as TeX evaluates the register; anything else is named and skipped.
      let tgt := match raws[j0]? with
        | some (.ctrl t _) => t
        | _ => ""
      let st ← get
      let opnd := (raws.extract j2 k).toList.filter (!· matches .space)
      let value := if name == "advance" then lenOperand st.lens opnd
        else match opnd with
          | [.word w _] => w.toNat?.map toString
          | _ => none
      -- premise: registerArithChecks — a length this rewrite set holds the
      -- value it recorded; composedLengthChecks — and the sum is one the
      -- grammar reads, or the statement is named and skipped
      let expr? := match (st.lens.find? (·.1 == tgt)).map (·.2), value with
        | some p, some v => some (if name == "advance" then s!"({p}) + {v}"
            else if name == "multiply" then s!"{v} * ({p})" else s!"({p}) / {v}")
        | _, _ => none
      match expr? with
      | some expr =>
        if Decl.readsAsLengthExpr expr then
          return some (← setLength tgt expr s!"\\{name}\\{tgt}" pos, k)
        sayOnce ("ctrl:" ++ name) .W0104
          s!"'\\{name}' on a value the length grammar cannot compose ('{expr}'): \
skipped, and the length keeps its value" pos
          (demote := styInternal (← get).file name)
        return some (#[], k)
      | none =>
        sayOnce ("ctrl:" ++ name) .W0104
          s!"TeX register arithmetic ('\\{name}') is not supported; skipped" pos
          (demote := styInternal (← get).file name)
        return some (#[], k)
    | _ => return none
  | "NewDocumentCommand" | "ProvideDocumentCommand"
  | "newcommand" | "providecommand" | "renewcommand"
  | "DeclareDocumentCommand" | "RenewDocumentCommand" | "DeclareRobustCommand" =>
    -- One arm for the whole definer family. LaTeX's documented triple
    -- (usrguide, "Defining commands": new must not exist, renew must
    -- exist, provide keeps an existing definition) collapses here to the
    -- one policy that changes what a correct document *means*: a
    -- provision of a name this document already bound keeps the first
    -- definition, so its signature and body are consumed whole. The two error
    -- halves are LaTeX's to check — kernel and package names are
    -- invisible to this pass, so checking them would misfire on every
    -- `\renewcommand` of a kernel command. The native store stays
    -- last-wins, the layering mechanism.
    let xparse := name.endsWith "DocumentCommand"
    let start := skipStar raws start
    let (nameArgs, j) := takeGroups raws start 1
    let some cmd := ctrlName (nameArgs.getD 0 #[]) | return none
    let provide := name == "providecommand" || name == "ProvideDocumentCommand"
    let st ← get
    -- premise: Tests.xparseProvideChecks — provision keeps existing user and builtin
    -- meanings. Decide before interpreting an unused signature or body:
    -- even a recognized heading/size idiom must remain inert.
    if provide && (st.bound.contains cmd || st.provideKeeps.contains cmd) then
      let j := if xparse then (takeGroups raws j 1).2 else
        let (_, j) := takeOpt raws j
        (takeOpt raws j).2
      let (_, k) := takeGroups raws j 1
      let why := if st.bound.contains cmd then
          s!"'\\{cmd}' is already defined and the existing definition is kept"
        else s!"'\\{cmd}' is built in and the built-in stands"
      discard s!"\\{name}\{\\{cmd}}" why s!"{name}:{cmd}" pos
      return some (#[], k)
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
      -- A class's list-level macro read as the parameters it assigns.
      if let some level := listLevelOf cmd then
        if !xparse && (← docPreamble) then
          if ← listLevelDef level s!"\\{name}\{\\{cmd}}" sbody pos then
            return some (#[], js + 1)
    -- The size idiom: a venue class's `\renewcommand\normalsize` whose
    -- body opens with `\@setfontsize\normalsize<size><leading>` (fntguide
    -- §"\@setfontsize"; size10.clo is where `\@xpt`/`\@xipt` get their
    -- values) declares the document's body size and leading. Both are the
    -- page's to carry: the leading lands as the factor over the engine's
    -- 6/5 base (`Ir.leadingMilli`), so a spliced .sty's 10/10.95 sets
    -- baselines at 10.95pt and the rhythm unit follows. The body's
    -- trailing display-skip internals are TeX the engine does not run;
    -- the translation note names what was taken. The display skips it
    -- assigns are the document's (`\begin{document}` runs `\normalsize`),
    -- so they are its tokens, the short pair with the long
    -- (`Ir.displaySkipsFor`).
    if !xparse && cmd == "normalsize" then
      if let some (.group sbody _) := raws[js]? then
        let b := skipSpaces sbody 0
        if let some (.ctrl "@setfontsize" _) := sbody[b]? then
          let (fsArgs, afterFs) := takeGroups sbody (b + 1) 3
          if h : fsArgs.size ≥ 3 then
            if let (some sz, some ld) := (ptMacroArg fsArgs[1], ptMacroArg fsArgs[2]) then
              if sz > 0 && ld > 0 then
                let factor := (ld * 1000000 + sz * 600) / (sz * 1200)
                let skips ← sizeSkips sbody afterFs pos
                let native := s!"\\page\{ fontsize = {milliStr sz}pt, \
leading = {milliStr factor} }" ++
                  (if skips.isEmpty then "" else s!"\\tokens\{ {String.intercalate ", " skips.toList} }")
                write fun st => { st with listiKept := !resetsListi sbody }
                became "\\renewcommand{\\normalsize}" native pos
                return some (← synthAt native pos, js + 1)
    write fun st => { st with
      bound := if st.bound.contains cmd then st.bound else st.bound.push cmd }
    let native := s!"\\define \\{cmd}({spec})"
    became s!"\\{name}\{\\{cmd}}" (native ++ " {...}") pos
    write fun st => { st with bodyNext := 1 }
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
    write fun st =>
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
    write fun st =>
      let st := if st.head.isEmpty && st.foot.isEmpty then { st with runPos := pos } else st
      let put (parts : Array (Nat × String)) : Array (Nat × String) :=
        slots.foldl (init := parts) fun parts slot =>
          let parts := parts.filter (·.1 != slot)
          if src.trimAscii.toString.isEmpty then parts else parts.push (slot, src)
      { st with
        head := if toHead then put st.head else st.head
        foot := if toFoot then put st.foot else st.foot }
    return some (#[], k)
  | "clearpairofpagestyles" =>
    -- scrlayer-scrpage's field reset (KOMA-Script manual ch. 5): every
    -- gathered head and foot field is cleared; fields declared after it
    -- apply from scratch — the same store `\pagestyle{empty}` clears.
    write fun st => { st with head := #[], foot := #[] }
    became "\\clearpairofpagestyles" "no running fields; fields declared after apply" pos
    return some (#[], start)
  | "pagestyle" =>
    let (args, k) := takeGroups raws start 1
    let v := (rawSrc (args.getD 0 #[])).trimAscii.toString
    match v with
    | "fancy" | "scrheadings" =>
      -- The styles that mean "the declared running fields apply" — which
      -- they already do here: gathered fields land as `\runninghead` /
      -- `\runningfoot` by themselves. Agreement, not a missing model (the
      -- old warning said "not modelled" about exactly what is modelled).
      discard s!"\\pagestyle\{{v}}" "declared running fields apply by themselves"
        s!"pagestyle:{v}" pos
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
      write fun st => { st with head := #[], foot := #[] }
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
      write fun st => { st with runFrom := 2 }
      became "\\thispagestyle{empty}" "\\runninghead[from = 2]{...}" pos
    return some (#[], k)
  | _ => rewriteCtrlLater name pos raws start

/-- Rewrite the control sequence `name` given what follows it. Returns the
replacement and how many following elements it consumed, or `none` to leave
the command alone. An empty replacement passes the silence guard
(`account`): the arms need not hand-account their no-ops, and a silent
drop is unrepresentable (`rewriteCtrl_accounts`). State-explicit so its
theorem unfolds it directly. -/
private def rewriteCtrl (name : String) (pos : Pos) (raws : Array Raw) (start : Nat) :
    M (Option (Array Raw × Nat)) := fun s0 =>
  match rewriteCtrlAt name pos raws start s0 with
  | (none, s1) => (none, s1)
  | (some (repl, k), s1) =>
    (some (repl, k - start), if repl.isEmpty then (account name pos s0 s1).2 else s1)
where
  rewriteCtrlAt (name : String) (pos : Pos) (raws : Array Raw) (start : Nat) :
      M (Option (Array Raw × Nat)) := do
  -- premise: beamerTemplateChecks — flat preamble group pairs restore
  -- font and footer capture just as the brace-group walk does.
  if (← get).wholeDoc && (← get).deck && !(← get).inDoc && !(← get).inDef then
    if let some close := groupPrimitives.lookup name then
      if beamerScopeClosed raws start close then
        write fun st => { st with beamerScopes :=
          (close, st.beamerFonts, st.beamerFootline) :: st.beamerScopes }
        became s!"\\{name}" "a local font and footer scope" pos
        return some (#[], start)
    if let (close, fonts, footline) :: rest := (← get).beamerScopes then
      if name == close then
        write fun st => { st with beamerFonts := fonts, beamerFootline := footline,
                                  beamerScopes := rest }
        became s!"\\{name}" "the enclosing font and footer scope" pos
        return some (#[], start)
  if let some tok := literalReplace.lookup name then
    return some (#[tok pos], start)
  -- premise: biblatexChecks — `\cite` under biblatex's authoryear sets bare
  -- (`Doe 2024`, `see Doe 2024, p. 5`), the line lualatex+biber sets, where
  -- natbib's own `\cite` is textual
  if name == "cite" && (← get).bibStyle == some "plainnat" then
    return some (#[.ctrl "citealp" pos], start)
  -- premise: numberingChecks — two decks differing by the package alone: the
  -- appendix numbers from 1 with it and numbers on without it
  if name == "appendix" && (← get).loads.pkgs.any (·.1 == "appendixnumberbeamer") then
    return some (#[.ctrl frameRestartMark pos, .ctrl name pos], start)
  -- premise: kernelLengthChecks — a skip amount the document set ships, at
  -- its command, the page a skip of that value ships
  if let some (_, v) := (← get).lens.find? (·.1 == name ++ "amount") then
    if (kernelSkip (name ++ "amount")).isSome then
      let native := s!"\\block[before = {v}]\{}"
      became s!"\\{name}" native pos
      return some (← synthAt native pos, start)
  if let some native := simpleNative.lookup name then
    became s!"\\{name}" native pos
    return some (← synthAt native pos, start)
  if (deferredHooks.lookup name).isSome then
    -- The replay point, reached: every hook the preamble declared was
    -- collected before this pass began, so a hook standing here is at its
    -- own moment already — in the body, or inside a body a hook is
    -- replaying. Deferring again is what would not terminate; the group
    -- stays in the stream and is read where it stands.
    sayOnce ("ctrl:" ++ name) .W0340
      s!"'\\{name}' cannot defer from here; its group is read where it stands" pos
      (help := "declare the hook before '\\begin{document}'")
    return some (#[], start)
  if let some (value, e) := plainAssign? name raws start then
    return some (← assignLength name value s!"\\{name}" pos, e)
  if let some settings := listSettings? (← get) name then
    let mut out : Array Raw := #[]
    for (n, v) in settings do
      out := out ++ (← assignLength n v s!"\\setlength\{\\{n}}" pos)
    return some (out, start)
  rewriteCtrlNamed name pos raws start

/-- Silence is fidelity, the surface layer: a control word the dispatcher
consumed with an empty replacement is paid for — the diagnostics grew or a
state write happened — for *every* name, position, and state. Proved by
unfolding the dispatcher's tail and the guard (`account`) alone; the arms
(`rewriteCtrlAt` and everything under it) stay opaque, so no future arm
can break the statement. `_accounts` is the registered shape (AGENTS.md,
the suffix registry): an empty result is paid for by a diagnostic or a
write. -/
private theorem rewriteCtrl_accounts (name : String) (pos : Pos) (raws : Array Raw)
    (start : Nat) (s s' : St) (k : Nat)
    (h : (rewriteCtrl name pos raws start).run s = (some (#[], k), s')) :
    s'.diags.size > s.diags.size ∨ s'.writes > s.writes := by
  have h' : rewriteCtrl name pos raws start s = (some (#[], k), s') := h
  unfold rewriteCtrl at h'
  split at h'
  · injection h' with h1 h2
    cases h1
  · injection h' with h1 h2
    injection h1 with h1
    injection h1 with hrepl hk
    subst hrepl
    split at h2
    · simp only [account] at h2
      split at h2
      · rename_i hc
        subst h2
        exact hc
      · split at h2
        · subst h2
          right
          simp
        · subst h2
          left
          simp [Array.size_push]
    · rename_i hne
      exact absurd rfl hne

/-- Split a two-column paracol body by its top-level switching commands.
Bare switches toggle, `[n]` selects n, and repeated visits append to the
same independent flow. The synchronized star form has no `.columns`
semantics; it is consumed and refused at its own site. -/
private def splitParacol (body : Array Raw) (start : Nat) :
    M (Array Raw × Array Raw) := do
  let mut left : Array Raw := #[]
  let mut right : Array Raw := #[]
  let mut current : Nat := 0
  let mut i := start
  for _ in [start:body.size + 1] do
    match body[i]? with
    | none => break
    | some (.ctrl "switchcolumn" spos) =>
      let (selected, k0) := takeOpt body (i + 1)
      let ks := skipSpaces body k0
      let starred := body[ks]? matches some (.word "*" _)
      let afterStar := if starred then skipSpaces body (ks + 1) else k0
      let (spanning, k) := if starred then takeOpt body afterStar else (none, k0)
      if starred then
        sayOnce "paracol:synchronized-switch" .W0104
          ("'\\switchcolumn*' synchronization is not modelled" ++
            if spanning.isSome then "; its spanning content stays in the selected column"
            else "; the independent column flow stands") spos
      let fallback := if current == 0 then 1 else 0
      let next ← match selected.bind (·.trimAscii.toString.toNat?) with
        | some n =>
          if n < 2 then pure n
          else do
            sayOnce "paracol:switch-column" .W0104
              s!"'\\switchcolumn[{n}]' names no column in a two-column flow; the next column is used" spos
            pure fallback
        | none => do
          if selected.isSome then
            sayOnce "paracol:switch-column" .W0104
              "'\\switchcolumn[...]' needs column 0 or 1; the next column is used" spos
          pure fallback
      current := next
      if let some text := spanning then
        let kept ← synthAt text spos
        if current == 0 then left := left ++ kept else right := right ++ kept
      i := k
    | some r =>
      if current == 0 then left := left.push r else right := right.push r
      i := i + 1
  return (left, right)

/-- Turn one paracol environment into the existing columns model, or keep
its content in source order under one truthful refusal when it asks for a
column family beyond the two-flow subset. -/
private def paracolEnv (ratio : Nat) (body : Array Raw) (pos : Pos)
    (restores : Array Raw := #[]) : M Raw := do
  let (leftCount, j) := takeOpt body 0
  let (args, k) := takeGroups body j 1
  let count := (rawSrc (args.getD 0 #[])).trimAscii.toString.toNat?
  if leftCount.isSome then
    sayOnce "paracol:left-count" .W0104
      "'paracol' [left-column-count] asks for paired-page columns; both columns are set on one page" pos
  if count != some 2 then
    sayOnce "env:paracol:count" .W0104
      "only the two-column 'paracol' form is modelled; its content stays in source order" pos
      (help := "write \\begin{paracol}{2} for two independent columns")
    return .group (body.extract k body.size ++ restores) pos
  let (left, right) ← splitParacol body k
  -- paracol.sty's `\pcol@setcolwidth@r` reserves the gap before applying
  -- ratios. Both the enclosing measure and its gap are read by the one
  -- length resolver where the columns open, including native declarations.
  let width (p : Nat) : Raw :=
    .group #[.word s!"{paracolFactor p} * (linewidth - columnsep)" pos] pos
  became "\\begin{paracol}{2}...\\switchcolumn..."
    "\\begin{columns} with two independent column flows" pos
  return .env "columns"
    (#[.env "column" (#[width ratio] ++ left) pos,
      .env "column" (#[width (1000 - ratio)] ++ right) pos] ++ restores) pos

/-- beamer's command form of a column: at the top level of a `{columns}`
body, `\column{width}` starts a column where it stands, running to the
next `\column` or the body's end (beamer user guide §12.7, `\column`) —
the environment form `\begin{column}{width} … \end{column}` with its
close implicit. One pass makes the boundaries explicit, so the
elaborator's one columns walk (`columnsGo`) reads both spellings and the
width group lands where the environment form carries it: first in the
column's body. Content before the first `\column` stays where it stands,
as content between environment-form columns does (kept as ordinary
blocks, never dropped) — the two spellings are one construct, so the
stray-content rule is one too. -/
private def splitColumns (body : Array Raw) : Array Raw := Id.run do
  let flush (out : Array Raw) : Option (Array Raw × Pos) → Array Raw
    | some (col, cpos) => out.push (.env "column" col cpos)
    | none => out
  let mut out : Array Raw := #[]
  let mut col : Option (Array Raw × Pos) := none
  let mut i : Nat := 0
  for _ in [0:body.size + 1] do
    match body[i]? with
    | some (.ctrl "column" cpos) =>
      let (args, k) := takeGroups body (i + 1) 1
      out := flush out col
      col := some (args.map (Raw.group · cpos), cpos)
      i := k
    | some (r@(.env "column" _ _)) =>
      -- The environment form closes an open command-form column too
      -- (beamerbaseframecomponents.sty: both openers run `\beamer@colclose`).
      out := (flush out col).push r
      col := none
      i := i + 1
    | some r =>
      match col with
      | some (c, cpos) => col := some (c.push r, cpos)
      | none => out := out.push r
      i := i + 1
    | none => break
  return flush out col

mutual

/-- The pass that makes every `{columns}` body's implicit column boundaries
explicit, whole tree, before the rewrite walk: the walk is structural on
`Raw`, so a body it descends into cannot be reshaped where it stands, and
`\column` must have become `{column}` by the time the walk's ctrl arm
could see it. Its own pass, like the conditional and hook passes before
it. -/
private def splitColumnsRaw : Raw → Raw
  | .group body p => .group (splitColumnsList body.toList).toArray p
  | .env n body p =>
    let body := (splitColumnsList body.toList).toArray
    .env n (if n == "columns" then splitColumns body else body) p
  | .math d body p => .math d body p
  | .word s p => .word s p
  | .space => .space
  | .par p => .par p
  | .ctrl n p => .ctrl n p
  | .sym c p => .sym c p
  | .verb env s p => .verb env s p

private def splitColumnsList : List Raw → List Raw
  | [] => []
  | r :: rest => splitColumnsRaw r :: splitColumnsList rest

end

/-- One level's group primitives paired into the brace group each pair is:
an opener collects what follows it until the closer of its own kind, and an
opener or closer with no partner at this level stands as written, for the
elaborator to name. -/
private def pairGroupLevel (xs : Array Raw) : Array Raw := Id.run do
  let mut frames : Array (String × Pos × Array Raw) := #[]
  let mut out : Array Raw := #[]
  for r in xs do
    let closer := match r, frames.back? with
      | .ctrl n _, some (c, _, _) => n == c
      | _, _ => false
    let opener := match r with
      | .ctrl n p => (groupPrimitives.lookup n).map (·, p)
      | _ => none
    let (frames', emit) : Array (String × Pos × Array Raw) × Option Raw :=
      if closer then
        match frames.back? with
        | some (_, p, items) => (frames.pop, some (.group items p))
        | none => (frames, some r)
      else match opener with
        | some (c, p) => (frames.push (c, p, #[]), none)
        | none => (frames, some r)
    frames := frames'
    if let some x := emit then
      match frames.back? with
      | some (c, p, items) => frames := frames.pop.push (c, p, items.push x)
      | none => out := out.push x
  -- An opener left unclosed at the level's end stands as written.
  for _ in [0:frames.size] do
    match frames.back? with
    | some (c, p, items) =>
      frames := frames.pop
      let opener := ((groupPrimitives.find? (·.2 == c)).map (·.1)).getD c
      let flat := #[Raw.ctrl opener p] ++ items
      match frames.back? with
      | some (c', p', items') => frames := frames.pop.push (c', p', items' ++ flat)
      | none => out := out ++ flat
    | none => break
  return out

mutual

/-- The pass that makes every matched group primitive the brace group it
is, whole tree, before the rewrite walk: the walk reads a group where a
document spelled braces, so a declaration inside the pair stays inside it.
The preamble's own top level (`top`: the tree's, and a spliced file's at
that level) keeps its pairs as written: the preamble is a flat list of
declarations, where a group would be content. -/
-- conserves: none — a pair's two words become the group they delimit.
private def pairGroupsRaw (top : Bool) : Raw → Raw
  | .group body p => .group (pairGroupsList false #[] body.toList) p
  | .env n body p =>
    .env n (pairGroupsList (top && (Parse.inputEnvFile? n).isSome) #[] body.toList) p
  | .math d body p => .math d (pairGroupsList false #[] body.toList) p
  | .word s p => .word s p
  | .space => .space
  | .par p => .par p
  | .ctrl n p => .ctrl n p
  | .sym c p => .sym c p
  | .verb env s p => .verb env s p

private def pairGroupsList (top : Bool) (acc : Array Raw) : List Raw → Array Raw
  | [] => if top then acc else pairGroupLevel acc
  | r :: rest => pairGroupsList top (acc.push (pairGroupsRaw top r)) rest

end

/-- One token of a delimited parameter text or of a use's input, as TeX
matches them: a character, a control word, a space, or a whole group. -/
private inductive DelimAtom where
  | ch (c : Char)
  | cs (name : String)
  | sp
  | other
  deriving BEq

/-- A use's input flattened to atoms, each with the raw it stands in and,
for a word's character, its offset: up to the paragraph's end, where a
delimited argument cannot reach. -/
private def delimAtoms (xs : Array Raw) (start : Nat) : Array (DelimAtom × Nat × Nat) := Id.run do
  let mut out := #[]
  for h : i in [start:xs.size] do
    match xs[i] with
    | .word w _ =>
      let mut o := 0
      for c in w.toList do
        out := out.push (.ch c, i, o)
        o := o + 1
    | .sym c _ => out := out.push (.ch c, i, 0)
    | .ctrl n _ => out := out.push (.cs n, i, 0)
    | .space => out := out.push (.sp, i, 0)
    | .par _ => break
    | _ => out := out.push (.other, i, 0)
  return out

/-- A refused delimited definition's parameter text: its literal run before
the first parameter, then each parameter's delimiter. `none` when a
parameter is undelimited or the text is not `#1…#n` in order. -/
private def delimShape (params : Array Raw) : Option (Array DelimAtom × Array (Array DelimAtom)) :=
  Id.run do
  let mut lead : Array DelimAtom := #[]
  let mut delims : Array (Array DelimAtom) := #[]
  let mut cur : Array DelimAtom := #[]
  let mut seen := 0
  let mut i := 0
  for _ in [0:params.size] do
    match (params[i]? : Option Raw), (params[i + 1]? : Option Raw) with
    | some (.sym '#' _), some (.word w _) =>
      let digits := w.toList.takeWhile Char.isDigit
      unless String.ofList digits == toString (seen + 1) do return none
      if seen == 0 then lead := cur else delims := delims.push cur
      seen := seen + 1
      cur := (w.toList.drop digits.length).toArray.map .ch
      i := i + 2
    | some (.word w _), _ => cur := cur ++ w.toList.toArray.map .ch; i := i + 1
    | some (.sym c _), _ => cur := cur.push (.ch c); i := i + 1
    | some (.ctrl n _), _ => cur := cur.push (.cs n); i := i + 1
    | some .space, _ => cur := cur.push .sp; i := i + 1
    | some _, _ => return none
    | none, _ => break
  if seen == 0 then return none
  delims := delims.push cur
  if delims.any (·.isEmpty) then return none
  return some (lead, delims)

/-- Does `pat` stand in `atoms` at `k`? -/
private def atomsAt (atoms : Array (DelimAtom × Nat × Nat)) (k : Nat) (pat : Array DelimAtom) :
    Bool :=
  (List.range pat.size).all fun j => (atoms[k + j]?.map (·.1)) == pat[j]?

/-- The raws of `xs` from atom `a` up to atom `b` (exclusive), a word split
where an atom boundary falls inside it. -/
private def atomRaws (xs : Array Raw) (atoms : Array (DelimAtom × Nat × Nat)) (a b : Nat) :
    Array Raw := Id.run do
  let mut out : Array Raw := #[]
  let mut k := a
  for _ in [a:b] do
    if k ≥ b then break
    match atoms[k]? with
    | none => break
    | some (_, ri, o) =>
      match xs[ri]? with
      | some (.word w p) =>
        -- the run of this word's characters inside [k, b)
        let mut n := 0
        for _ in [k:b] do
          if atoms[k + n]?.any (fun t => t.2.1 == ri) && k + n < b then n := n + 1 else break
        out := out.push (.word (String.ofList ((w.toList.drop o).take n)) p)
        k := k + n
      | some r =>
        out := out.push r
        k := k + 1
      | none => break
  return out

/-- A use of a refused delimited definition, spelled as the braced call its
parameter text reads: the arguments TeX would bind, each a group, with the
delimiters consumed as TeX consumes them. `none` when the input does not
match (a delimiter missing before the paragraph's end), leaving the use as
written. Returns the call and the index past what it consumed. -/
private def delimCall (xs : Array Raw) (i : Nat) (name : String) (pos : Pos)
    (shape : Array DelimAtom × Array (Array DelimAtom)) : Option (Array Raw × Nat) := Id.run do
  let atoms := delimAtoms xs (i + 1)
  let (lead, delims) := shape
  unless atomsAt atoms 0 lead do return none
  let mut k := lead.size
  let mut args : Array Raw := #[]
  for d in delims do
    let mut e := k
    let mut found := false
    for _ in [k:atoms.size] do
      if atomsAt atoms e d then found := true; break
      e := e + 1
    unless found do return none
    args := args.push (.group (atomRaws xs atoms k e) pos)
    k := e + d.size
  -- What the last delimiter leaves of a word stays as that word's tail.
  let (stop, tail) := match atoms[k]?, atoms[k - 1]? with
    | some (_, ri, o), some (_, rj, _) =>
      if ri == rj && o > 0 then
        match xs[ri]? with
        | some (.word w p) => (ri + 1, #[Raw.word (String.ofList (w.toList.drop o)) p])
        | _ => (ri, #[])
      else (ri, #[])
    | none, some (_, rj, _) => (rj + 1, #[])
    | _, _ => (i + 1, #[])
  return some (#[Raw.ctrl name pos] ++ args ++ tail, stop)

/-- The definers after which a name means something new: every one that
replaces a definition, so a delimited signature ends there. `\providecommand`
keeps a definition that stands, so it is not one. -/
private def redefiners : List String :=
  ["def", "gdef", "edef", "xdef", "let", "define", "newcommand", "renewcommand",
   "DeclareRobustCommand", "NewDocumentCommand", "RenewDocumentCommand",
   "DeclareDocumentCommand"]

/-- The command a definer standing at `i` names: the control word after it,
past spaces and a `*`, bare or as a one-word group. -/
private def definedCmd (xs : Array Raw) (i : Nat) : Option String :=
  let j := skipSpaces xs (i + 1)
  let j := if xs[j]? matches some (.sym '*' _) then skipSpaces xs (j + 1) else j
  match xs[j]? with
  | some (.ctrl n _) => some n
  | some (.group g _) =>
    match g.toList.filter (!· matches .space) with
    | [.ctrl n _] => some n
    | _ => none
  | _ => none

private abbrev DelimShape := Array DelimAtom × Array (Array DelimAtom)

/-- Global writes outlive a scope, including signature removals and writes
shadowed by a later local definition. -/
private structure DelimState where
  sigs : Array (String × DelimShape) := #[]
  globals : Array (String × Option DelimShape) := #[]

private def setDelimSig (sigs : Array (String × DelimShape))
    (n : String) (shape : Option DelimShape) : Array (String × DelimShape) :=
  let kept := sigs.filter (·.1 != n)
  match shape with
  | some sh => kept.push (n, sh)
  | none => kept

/-- The signatures in force after the definer at `i`: its name's delimited
parameter text when it is a delimited `\def` or `\gdef`, and none otherwise. -/
private def sigsAfter (st : DelimState) (xs : Array Raw) (i : Nat) (d n : String) :
    DelimState :=
  let shape := if d == "def" || d == "gdef" then
      let params := ((xs.extract (i + 2) xs.size).toList.takeWhile
        fun r => !(r matches .group _ _)).toArray
      delimShape params
    else none
  { sigs := setDelimSig st.sigs n shape
    globals := if definesGlobally xs i d then st.globals.push (n, shape) else st.globals }

/-- Restore the outer locals, replaying only global writes made since this
scope opened. An earlier global must not overwrite a saved local shadow. -/
private def delimClose (saved current : DelimState) : DelimState :=
  let writes := current.globals.extract saved.globals.size current.globals.size
  { current with
    sigs := writes.foldl (fun sigs (n, shape) => setDelimSig sigs n shape) saved.sigs }

mutual

/-- Every use of a refused delimited definition spelled as its braced call
(`delimCall`), whole tree, in document order, before the rewrite walk: the
delimiter is the call's syntax, consumed as TeX consumes it, never ink. A
use reads the signature in force where it stands. Real scopes restore locals
and retain explicit global writes; input wrappers open no scope. The
definition's own head is not a use. -/
-- conserves: none — a use's delimiters are syntax, not text.
private def delimCallsRaw (sigs : DelimState) : Raw → Raw × DelimState
  | .group body p =>
    let (b, next) := delimCallsList sigs body #[] body.toList 0 0
    (.group b p, delimClose sigs next)
  | .env n body p =>
    let (b, next) := delimCallsList sigs body #[] body.toList 0 0
    (.env n b p, if (Parse.inputEnvFile? n).isSome then next else delimClose sigs next)
  | .math d body p => (.math d body p, sigs)
  | .word s p => (.word s p, sigs)
  | .space => (.space, sigs)
  | .par p => (.par p, sigs)
  | .ctrl n p => (.ctrl n p, sigs)
  | .sym c p => (.sym c p, sigs)
  | .verb env s p => (.verb env s p, sigs)

private def delimCallsList (sigs : DelimState)
    (xs : Array Raw) (out : Array Raw) : List Raw → Nat → Nat → Array Raw × DelimState
  | [], _, _ => (out, sigs)
  | _ :: rest, i, skip + 1 => delimCallsList sigs xs out rest (i + 1) skip
  | .ctrl "apptocmd" pos :: rest, i, 0 =>
    -- Definitions inside a patch or either callback are not in force.
    let (_, k, _) := takeHookArgs xs (i + 1)
    delimCallsList sigs xs ((out.push (.ctrl "apptocmd" pos)) ++ xs.extract (i + 1) k)
      rest (i + 1) (k - (i + 1))
  | .ctrl d p :: rest, i, 0 =>
    match (if redefiners.contains d then definedCmd xs i else none) with
    | some n =>
      let sigs := sigsAfter sigs xs i d n
      match xs[i + 1]? with
      | some (.ctrl m q) =>
        delimCallsList sigs xs ((out.push (.ctrl d p)).push (.ctrl m q)) rest (i + 1) 1
      | _ => delimCallsList sigs xs (out.push (.ctrl d p)) rest (i + 1) 0
    | none =>
      match (sigs.sigs.find? (·.1 == d)).bind fun (_, sh) => delimCall xs i d p sh with
      | some (call, stop) => delimCallsList sigs xs (out ++ call) rest (i + 1) (stop - (i + 1))
      | none => delimCallsList sigs xs (out.push (.ctrl d p)) rest (i + 1) 0
  | r :: rest, i, 0 =>
    let (r', sigs) := delimCallsRaw sigs r
    delimCallsList sigs xs (out.push r') rest (i + 1) 0

end

/-- Recover delimited calls in execution order: preamble, replayed hooks,
then body. A hook sees the last preamble signature and earlier hooks, never
a redefinition written later in the body. The same walk gathers signatures
and consumes their calls; no whole-tree pre-scan is needed. -/
private def delimDocument (raws : Array Raw) : M (Array Raw) := do
  let d := (raws.findIdx? (· matches .env "document" _ _)).getD raws.size
  let pre := raws.extract 0 d
  let post := raws.extract d raws.size
  let (pre, sigs) := delimCallsList {} pre #[] pre.toList 0 0
  let mut sigs := sigs
  let mut hooks := #[]
  for (pt, file, pos, body) in (← get).deferred do
    let body := pairGroupsList false #[] body.toList
    let (body, next) := delimCallsList sigs body #[] body.toList 0 0
    sigs := next
    hooks := hooks.push (pt, file, pos, body)
  write fun st => { st with deferred := hooks }
  return pre ++ (delimCallsList sigs post #[] post.toList 0 0).1

/-- Glue a row of boxes can hold between two boxes: a space, or the fill
that takes what the boxes leave of the measure (`\hfill`, `\hfil`). A
paragraph break is not among them — it ends the line the boxes stand on. -/
private def rowGlue : Raw → Bool
  | .space => true
  | .ctrl "hfill" _ => true
  | .ctrl "hfil" _ => true
  | _ => false

/-- A minipage's width group and its content past it, its `[pos]` bracket as
written (classes.dtx §minipage: `[pos][height][inner-pos]{width}`), and
whether a `[height]` or `[inner-pos]` stood after it. `none` without a width
group. -/
private def boxParts (body : Array Raw) : Option (Raw × Array Raw × Array Raw × Bool) :=
  let (_, k1) := takeOpts body 0 1
  let (more, k) := takeOpts body k1 2
  let k := skipSpaces body k
  match body[k]? with
  | some (.group g gp) => some (.group g gp, body.extract (k + 1) body.size, body.extract 0 k1, more)
  | _ => none

/-- Does a paragraph end at `i` — a break, or the end of the level — once
the spaces before it are passed? -/
private def endsPara (rs : Array Raw) (i : Nat) : Bool :=
  match rs[skipSpaces rs i]? with
  | none | some (.par _) => true
  | _ => false

/-- Does a paragraph open at `i`: the level's start, or a break before it
with only spaces between? -/
private def opensPara (rs : Array Raw) (i : Nat) : Bool := Id.run do
  let mut k := i
  for _ in [0:i] do
    match k with
    | 0 => return true
    | k' + 1 =>
      match rs[k']? with
      | some .space => k := k'
      | some (.par _) => return true
      | _ => return false
  return k == 0

/-- The minipage body a group holds, when the group is one minipage box
alone (bar surrounding spaces). This is the one minipage a flow-transparent
link wrapper may stand on, read through for the row the boxes form while the
wrapper stays around the box's content. -/
private def soleMinipage (g : Array Raw) : Option (Array Raw) :=
  let a := skipSpaces g 0
  match g[a]? with
  | some (.env "minipage" mb _) =>
    if skipSpaces g (a + 1) == g.size then some mb else none
  | _ => none

/-- A box at `i` that a row can hold: a bare `\begin{minipage}` box, or one
inside a flow-transparent link wrapper (`\hyperlink`/`\href`, whose second
group is one minipage). Returns the box's width group, the content the
column carries (the wrapper kept around the minipage's own content for a
linked box, so the column keeps one link identity), its `[pos]` bracket,
whether a `[height]`/`[inner-pos]` option stood, the box's position, and the
index past the whole box. `none` when `i` is not a box. -/
private def boxAt (rs : Array Raw) (i : Nat) :
    Option (Raw × Array Raw × Array Raw × Bool × Pos × Nat) :=
  match rs[i]? with
  | some (.env "minipage" b p) =>
    (boxParts b).map fun (w, c, pos, o) => (w, c, pos, o, p, i + 1)
  | some (.ctrl wrapper wp) =>
    if wrapper == "hyperlink" || wrapper == "href" then
      let j := skipSpaces rs (i + 1)
      let j2 := skipSpaces rs (j + 1)
      match rs[j]?, rs[j2]? with
      | some (.group tgt tp), some (.group bodyG bp) =>
        (soleMinipage bodyG).bind fun mb =>
          (boxParts mb).map fun (w, c, pos, o) =>
            (w, #[Raw.ctrl wrapper wp, Raw.group tgt tp, Raw.group c bp], pos, o, wp, j2 + 1)
      | _, _ => none
    else none
  | _ => none

/-- A linked row is only a candidate until elaboration resolves the link
names. Keep the original calls beside the proposed row: an overriding
macro owns its arguments, including boxes it discards. The space makes
this internal environment unspellable as a document environment name. -/
public def linkedBoxRowMark : String := " linked box row"

/-- Each run of minipages at one level whose separators are row glue holding
a fill becomes one `{columns}` row of `{column}`s of the widths the boxes
declare: LaTeX sets such boxes on one line with the fill between them
(`\hfill` is `\hskip 0pt plus 1fill`, TeXbook chapter 12), which is the
columns model's own leftover rule — the measure the declared widths leave
goes into equal gutters between the boxes. A paragraph that is one box with
a declared `[pos]` and then a picture is that line too: LaTeX sets the two
side by side, each on the baseline by its own point, and as a row the
picture's column takes what the box leaves, so it starts where the box
ends. Each box keeps its `[pos]`. A box standing alone, a pair a paragraph
break or other content separates, and a pair of boxes only a space
separates are left as they stand. Returns the level and, for each row,
where it opened, whether a box carried `[height]`/`[inner-pos]`, and
whether it is the box-and-picture line. -/
private def boxRows (rs : Array Raw) : Array Raw × Array (Pos × Bool × Bool) := Id.run do
  let mut out : Array Raw := #[]
  let mut rows : Array (Pos × Bool × Bool) := #[]
  let mut i := 0
  for _ in [0:rs.size + 1] do
    match boxAt rs i with
    | none =>
      match (rs[i]? : Option Raw) with
      | none => break
      | some r =>
        out := out.push r
        i := i + 1
    | some (w0, c0, pos0, o0, cp0, next0) =>
      -- The box-and-picture line is a bare minipage followed by a picture;
      -- a wrapped box does not take that shape here.
      let bare := match rs[i]? with | some (.env "minipage" _ _) => true | _ => false
      let pk := skipSpaces rs next0
      let picLine := bare && (match rs[pk]? with
        | some (.env "tikzpicture" _ _) =>
          opensPara rs i && endsPara rs (pk + 1) && pos0.any (· matches .sym '[' _)
        | _ => false)
      if picLine then
        let pic := rs[pk]!
        let pp := match pic with
          | .env _ _ q => q
          | _ => cp0
        let picPos : Array Raw := #[.sym '[' pp, .word "t" pp, .sym ']' pp]
        out := out.push (.env "columns"
          #[Raw.env "column" (pos0 ++ #[w0] ++ c0) cp0, Raw.env "column" (picPos ++ #[pic]) pp] cp0)
        rows := rows.push (cp0, o0, true)
        i := pk + 1
      else
        let mut cols : Array (Raw × Array Raw × Array Raw × Pos) := #[(w0, c0, pos0, cp0)]
        let mut opts := o0
        let mut j := next0
        for _ in [next0:rs.size + 1] do
          let mut k := j
          let mut fill := false
          for _ in [j:rs.size + 1] do
            match rs[k]? with
            | some r =>
              if rowGlue r then
                if !(r matches .space) then fill := true
                k := k + 1
              else break
            | none => break
          match boxAt rs k with
          | some (w, c, ps, o, cp, nextk) =>
            if fill then
              cols := cols.push (w, c, ps, cp)
              opts := opts || o
              j := nextk
            else break
          | none => break
        if cols.size ≥ 2 then
          let row := Raw.env "columns"
            (cols.map fun (w, c, ps, cp) => Raw.env "column" (ps ++ #[w] ++ c) cp) cp0
          let source := rs.extract i j
          if source.any (fun r => r matches .ctrl "href" _ | .ctrl "hyperlink" _) then
            out := out.push (.env linkedBoxRowMark
              (#[.group source cp0, .group #[row] cp0] ++
                if opts then #[.space] else #[]) cp0)
          else
            out := out.push row
            rows := rows.push (cp0, opts, false)
          i := j
        else
          -- A lone box is left as it stands: push its first token and
          -- advance one, so any following groups (a wrapper's arguments)
          -- flow back through the walk unchanged.
          match (rs[i]? : Option Raw) with
          | none => break
          | some r =>
            out := out.push r
            i := i + 1
  return (out, rows)

/-- One level of rows, formed and named: each row is a translation onto the
columns model (N0100), and a `[height]` or `[inner-pos]` option inside one
is noted where the row opens, since a box takes its content's height. -/
private def boxRowEmit (rs : Array Raw) : M (Array Raw) := do
  let (out, rows) := boxRows rs
  for (p, opts, withPic) in rows do
    if withPic then
      became "\\parbox[pos]{w}{…} \\begin{tikzpicture}…"
        "one row: the box, then the picture where it ends, each on the baseline by its own point"
        p (subject := some "env:box-picture-row")
    else
      became "\\begin{minipage}…\\end{minipage}\\hfill\\begin{minipage}…"
        "one row of boxes, the fill between them" p (subject := some "env:minipage-row")
    if opts then
      sayOnce "env:minipage-row-options" .N0102
        "'minipage' [height] and [inner-pos] options are ignored in a row of boxes: each \
box is as tall as its content" p
  return out

/-- beamer's `\begin{columns}[t]` (and `c`, `b`, `T`) is the point each
column stands on the row's baseline by, unless a `{column}` declares its
own: carried onto every column that declares none, so the column's reader
is the one reader of a position. -/
private def columnsRowPos (body : Array Raw) : Array Raw := Id.run do
  let (o, _) := takeOpt body 0
  let some opts := o | return body
  let some letter := ((opts.splitOn ",").map (·.trimAscii.toString)).find?
    (["t", "c", "b", "T"].contains ·) | return body
  let withPos (r : Raw) : Raw :=
    if let .env "column" cb cp := r then
      if cb[skipSpaces cb 0]? matches some (.sym '[' _) then r
      else .env "column" (#[.sym '[' cp, .word letter cp, .sym ']' cp] ++ cb) cp
    else r
  return body.map withPos

mutual

/-- The pass that sets side-by-side boxes in one row, whole tree, after the
idiom rewrite (so a `\parbox` is the box it became). Structural on `Raw`,
the list walk carrying its accumulator. -/
private def boxRowList (acc : Array Raw) : List Raw → M (Array Raw)
  | [] => pure acc
  | r :: rest => do
    let r' ← boxRowRaw r
    boxRowList (acc.push r') rest

private def boxRowRaw : Raw → M Raw
  | .group body p => do
    let kids ← boxRowList #[] body.toList
    return .group (← boxRowEmit kids) p
  | .env n body p => do
    match Parse.inputEnvFile? n with
    | some file =>
      -- This late pass emits its own row notes after rewriteRaw has
      -- restored the caller's file. Follow the input wrapper again.
      let saved := (← get).file
      write fun st => { st with file := file }
      let kids ← boxRowList #[] body.toList
      let body' ← boxRowEmit kids
      write fun st => { st with file := saved }
      return .env n body' p
    | none =>
      let kids ← boxRowList #[] body.toList
      return .env n (← boxRowEmit (if n == "columns" then columnsRowPos kids else kids)) p
  | .math d body p => pure (.math d body p)
  | .word s p => pure (.word s p)
  | .space => pure .space
  | .par p => pure (.par p)
  | .ctrl n p => pure (.ctrl n p)
  | .sym c p => pure (.sym c p)
  | .verb env s p => pure (.verb env s p)

end

/-- A completion with no pending declaration or hook interpreter. The box
pass may still translate any number of nested rows and report their losses. -/
private def QuietTail (st : St) : Prop :=
  st.head = #[] ∧ st.foot = #[] ∧ st.runFrom ≤ 1 ∧
    st.listResets = #[] ∧ st.listDefs = #[] ∧
    st.deferred = #[] ∧ st.beamerFootline = none

private def TailDiag (d : Diag) (st : St) : Prop :=
  QuietTail st ∧ d ∈ st.diags

private theorem state_bind_inv {α β : Type} (P : St → Prop)
    (act : M α) (next : α → M β) (st : St)
    (ha : P (act st).2) (hn : ∀ a s, P s → P (next a s).2) :
    P ((act >>= next) st).2 :=
  hn (act st).1 (act st).2 ha

private theorem state_bind_apply {α β : Type} (act : M α)
    (next : α → M β) (st : St) :
    (act >>= next) st = next (act st).1 (act st).2 := by rfl

private theorem state_forIn_inv {α β : Type} (P : St → Prop)
    (step : α → β → M (ForInStep β)) :
    ∀ (xs : List α) (init : β) (st : St), P st →
      (∀ a ∈ xs, ∀ b s, P s → P (step a b s).2) →
      P ((forIn xs init step : M β) st).2 := by
  intro xs
  induction xs with
  | nil => intro init st h _; exact h
  | cons a rest ih =>
    intro init st h hs
    have ha := hs a (by simp) init st h
    rw [List.forIn_cons]
    apply state_bind_inv P _ _ st ha
    intro result s hp
    cases result with
    | done b => exact hp
    | yield b =>
      exact ih b s hp (fun x hx => hs x (by simp [hx]))

private theorem state_array_forIn_inv {α β : Type} (P : St → Prop)
    (step : α → β → M (ForInStep β)) (xs : Array α)
    (init : β) (st : St) (h : P st)
    (hs : ∀ a ∈ xs, ∀ b s, P s → P (step a b s).2) :
    P ((forIn xs init step : M β) st).2 := by
  rw [← Array.forIn_toList]
  exact state_forIn_inv P step xs.toList init st h
    (fun a ha => hs a (by simpa using ha))

private theorem say_tailDiag (d : Diag) (code : DiagCode) (msg : String)
    (pos : Pos) (help : Option String) (demote : Bool)
    (subject refused : Option String) (st : St) (h : TailDiag d st) :
    TailDiag d (say code msg pos help demote subject refused st).2 :=
  ⟨h.1, Array.mem_push.mpr (Or.inl h.2)⟩

private theorem sayOnce_minipage_tailDiag (d : Diag) (code : DiagCode)
    (msg : String) (pos : Pos) (help : Option String) (demote : Bool)
    (st : St) (h : TailDiag d st) :
    TailDiag d (sayOnce "env:minipage-row-options" code msg pos help demote st).2 := by
  unfold sayOnce
  apply state_bind_inv (TailDiag d) _ _ st h
  intro observed s hs
  dsimp only
  split <;> apply state_bind_inv (TailDiag d)
  all_goals
    first
    | exact hs
    | intro _ s' hs'; exact say_tailDiag d _ _ _ _ _ _ _ _ hs'

private theorem boxRowEmit_tailDiag (rs : Array Raw) (d : Diag) (st : St)
    (h : TailDiag d st) : TailDiag d (boxRowEmit rs st).2 := by
  unfold boxRowEmit
  generalize boxRows rs = result
  rcases result with ⟨out, rows⟩
  apply state_bind_inv (TailDiag d)
  · apply state_array_forIn_inv (TailDiag d) _ rows () st h
    intro entry _ init s hs
    rcases entry with ⟨p, opts, pic⟩
    cases pic <;> dsimp only
    all_goals
      apply state_bind_inv (TailDiag d)
      · exact say_tailDiag d _ _ _ _ _ _ _ _ hs
      · intro _ s' hs'
        cases opts
        · exact hs'
        · exact state_bind_inv (TailDiag d) _ _ s'
            (sayOnce_minipage_tailDiag d _ _ _ _ _ _ hs') (fun _ _ hp => hp)
  · intro _ s hs; exact hs

mutual

private theorem boxRowList_tailDiag (acc : Array Raw) (rs : List Raw)
    (d : Diag) (st : St) (h : TailDiag d st) :
    TailDiag d (boxRowList acc rs st).2 := by
  cases rs with
  | nil => exact h
  | cons r rest =>
    rw [boxRowList]
    exact state_bind_inv (TailDiag d) _ _ st
      (boxRowRaw_tailDiag r d st h)
      (fun r' s hs => boxRowList_tailDiag (acc.push r') rest d s hs)

private theorem boxRowRaw_tailDiag (r : Raw) (d : Diag) (st : St)
    (h : TailDiag d st) : TailDiag d (boxRowRaw r st).2 := by
  cases r with
  | group body p =>
    rw [boxRowRaw]
    apply state_bind_inv (TailDiag d) _ _ st
      (boxRowList_tailDiag #[] body.toList d st h)
    intro kids s hs
    exact state_bind_inv (TailDiag d) _ _ s
      (boxRowEmit_tailDiag _ d s hs) (fun _ _ hp => hp)
  | env n body p =>
    rw [boxRowRaw]
    cases Parse.inputEnvFile? n with
    | some file =>
      apply state_bind_inv (TailDiag d) _ _ st h
      intro observed s hs
      apply state_bind_inv (TailDiag d) _ _ s hs
      intro _ s' hs'
      apply state_bind_inv (TailDiag d) _ _ s'
        (boxRowList_tailDiag #[] body.toList d s' hs')
      intro kids s'' hs''
      apply state_bind_inv (TailDiag d) _ _ s''
        (boxRowEmit_tailDiag _ d s'' hs'')
      intro body' s''' hs'''
      exact state_bind_inv (TailDiag d) _ _ s''' hs''' (fun _ _ hp => hp)
    | none =>
      apply state_bind_inv (TailDiag d) _ _ st
        (boxRowList_tailDiag #[] body.toList d st h)
      intro kids s hs
      exact state_bind_inv (TailDiag d) _ _ s
        (boxRowEmit_tailDiag _ d s hs) (fun _ _ hp => hp)
  | math | word | space | par | ctrl | sym | verb => exact h

end

/-- Is this raw an overlay spec token? Shape alone, because an item's
boundary is a lexical question: `\onslide<...>` starts an item whatever its
spec says. Whether that spec names a step — and so whether the item can be
an alternative — is the one range definition's answer (`specNumbered`, over
`Ir.overlayRange`), never a second reading of a range spelled here. -/
private def specRaw? : Raw → Option Raw
  | r@(.word w _) =>
    if w.startsWith "<" && w.endsWith ">" && w.length ≥ 3 then some r else none
  | _ => none

/-- The specification word standing at `i`, if one does: `specRaw?`'s shape
test asked of a position rather than a raw, so the lexical question "is this
a spec" has one answer in this module. -/
private def specWordAt (raws : Array Raw) (i : Nat) : Option String :=
  (raws[i]?.bind specRaw?).bind fun r =>
    match r with
    | .word w _ => some w
    | _ => none

/-- The beamer modes whose overlay count decides what a *presentation*
artifact shows. `presentation` is beamer's collective name for the
non-article modes, `beamer` the slide presentation itself, and `all` every
mode (beamer manual §21.1, "Overview of Modes"); `handout`, `trans`,
`second` and `article` each address an artifact this engine is not
producing, so a count declared for one of those decides nothing here. -/
private def presentationModes : List String := ["presentation", "beamer", "all"]

/-- Does this specification declare that the presentation has *no* slides
here? Beamer's mode specification pairs a mode with an overlay
specification — `<presentation:0>` says the presentation modes get zero
overlays, so beamer's own output omits the construct and keeps it for
handout or article mode only (beamer manual §21.2, "Mode Specifications").
The engine ships one presentation, so such a frame is the author saying
*not in this artifact*, and honouring it is not a loss.

Read the way beamer's own decoder reads it (`beamerbasedecode.sty`): the
`|`-separated entries are scanned left to right and each entry naming the
current mode *overwrites* the answer, so the **last** entry naming this
artifact decides — `<all:0|beamer:1->` shows, because `beamer:1-` is read
after `all:0`. An entry with no colon is an overlay specification for the
presentation itself, which is beamer's inserted `beamer:` prefix.

The decision is then a number: the entry silences exactly when its overlay
specification *is* zero, so `<beamer:0,2>` and `<presentation:0-3>` show —
they name a step as well as the zero. A comma separates intervals inside one
entry's specification and never separates entries, which is why it is not
split on: reading `0` out of `0,2` silenced a frame beamer shows. Any range
other than zero is a restriction the step model does not carry, and that
loss is named where the specification is stripped rather than guessed at. -/
public def modeSilencesPresentation (w : String) : Bool :=
  if w.startsWith "<" && w.endsWith ">" && w.length ≥ 3 then
    let inner := ((w.drop 1).dropEnd 1).toString
    let decided := (inner.splitOn "|").foldl (init := none) fun acc e =>
      match e.splitOn ":" with
      | [ov] => some ov
      | [m, ov] => if presentationModes.contains m.trimAscii.toString then some ov else acc
      | _ => acc
    (decided.bind (·.trimAscii.toString.toNat?)) == some 0
  else false

/-- Split an `{overprint}` body into the content before its first item and
the items themselves, each an `\onslide` spec with the content that runs to
the next `\onslide` (beamer manual §9.5, "Dynamically Changing Text or
Images": the items are alternatives, and one of them stands on a given
overlay). The `Bool` reports a body this
rewrite refuses to read as an alternation — an `\onslide` with no spec
token, where beamer's own reading is "on every overlay" and alternation has
no meaning; the caller degrades rather than guessing.

Accumulators rather than a rebuilt tail: the result is one pass, and the
content of an item grows by `push`. -/
private def overprintScan : List Raw → Array Raw → Option (Raw × Array Raw) →
    Array (Raw × Array Raw) → Array Raw × Array (Raw × Array Raw) × Bool
  | [], lead, cur, items =>
    (lead, (match cur with | some it => items.push it | none => items), false)
  | .ctrl "onslide" _ :: s :: rest, lead, cur, items =>
    let items := match cur with | some it => items.push it | none => items
    match specRaw? s with
    | some sp => overprintScan rest lead (some (sp, #[])) items
    | none => (lead, items, true)
  | [.ctrl "onslide" _], lead, cur, items =>
    (lead, (match cur with | some it => items.push it | none => items), true)
  | r :: rest, lead, cur, items =>
    match cur with
    | some (sp, content) => overprintScan rest lead (some (sp, content.push r)) items
    | none => overprintScan rest (lead.push r) none items

/-- Can the step model number this item's specification? Asked of the one
range definition (`Ir.overlayRange`), never of a second parse of a spec: an
item whose spec names steps is an alternative, and one whose spec names none
that arithmetic can place cannot be — which of the two it is has to be the
same question the elaborator's `\alt` arm asks, or the two passes could
disagree about an item and no theorem would notice. -/
private def specNumbered : Raw → Bool
  | .word w _ => (Ir.overlayRange w).isSome
  | _ => false

/-- n-way alternation is nested binary alternation: item one against all the
rest, recursively —
`\alt<s1>{one}{\alt<s2>{two}{\alt<s3>{three}{tail}}}`.

Nesting rather than a new n-ary IR constructor because the selection beamer
specifies is already a total order (the first item whose spec names the
overlay stands), and because every consumer of alternation then needs no
change whatever: each node is an ordinary alternation, so exactly one item
inks per step page by the same fact that holds for two
(`Ir.altShowsFirst`, `alt_backend_agree`), the handout's page count is the
maximum over every item's spec because `Ir.maxStepBlock`'s `.alt` arm
recurses into both groups, and the structure tree keeps declaring each
group exactly once in page order.

`tail` is what stands on an overlay no item's spec names: empty is beamer's
own answer (nothing stands there), and nothing is the one thing that is
never *several items stacked*, which is what keeping the body whole did. An
item whose spec the step model cannot number goes here instead of nowhere —
the steps nothing claims are the honest home for an item whose steps cannot
be enumerated.

The spec travels verbatim at the index the elaborator's `\alt` arm reads,
as `alertOverlay`'s does, so numbering and range membership stay in the one
place that owns them. -/
private def overprintAlt (p : Pos) (tail : Array Raw) : List (Raw × Array Raw) → Array Raw
  | [] => tail
  | (sp, content) :: rest =>
    #[.ctrl "alt" p, sp, .group content p, .group (overprintAlt p tail rest) p]

/-- The head of a nesting is one alternation node and no fifth raw. -/
private theorem overprintAlt_exact (p : Pos) (tail : Array Raw) (sp : Raw) (content : Array Raw)
    (rest : List (Raw × Array Raw)) :
    overprintAlt p tail ((sp, content) :: rest) =
      #[.ctrl "alt" p, sp, .group content p, .group (overprintAlt p tail rest) p] := by rfl

/-- The item is carried whole as the alternation's first alternative: what
the steps its own spec names show, and the only copy of it. -/
private theorem overprintAlt_item_exact (p : Pos) (tail : Array Raw) (sp : Raw) (content : Array Raw)
    (rest : List (Raw × Array Raw)) :
    (overprintAlt p tail ((sp, content) :: rest))[2]? = some (.group content p) := by rfl

/-- The spec reaches the elaborator as written, at the index its `\alt` arm
reads: a spec the step model cannot number is judged there, never here. -/
private theorem overprintAlt_spec_id (p : Pos) (tail : Array Raw) (sp : Raw) (content : Array Raw)
    (rest : List (Raw × Array Raw)) :
    (overprintAlt p tail ((sp, content) :: rest))[1]? = some sp := by rfl

/-- The last item's other alternative is the tail and nothing else: the
overlay no item names shows what stands last, never a second item beside the
first. With no tail — `#[]`, the shape a body of numbered items alone
plans — it shows nothing. -/
private theorem overprintAlt_last_exact (p : Pos) (tail : Array Raw) (sp : Raw)
    (content : Array Raw) :
    (overprintAlt p tail [(sp, content)])[3]? = some (.group tail p) := by rfl

/-- The items that can be alternatives, in the order the body wrote them. -/
private def overprintNumbered (items : Array (Raw × Array Raw)) :
    Array (Raw × Array Raw) :=
  items.filter fun it => specNumbered it.1

/-- The items whose spec the step model cannot number, in body order. -/
private def overprintLoose (items : Array (Raw × Array Raw)) :
    Array (Raw × Array Raw) :=
  items.filter fun it => !specNumbered it.1

/-- `_mem`: an alternative of the plan is an item the body wrote. Refusing a
spec drops items from the nesting; it never invents, reorders or merges one,
so the reading on a page is always some item's, whole. -/
private theorem overprintNumbered_mem (items : Array (Raw × Array Raw))
    (it : Raw × Array Raw) (h : it ∈ overprintNumbered items) : it ∈ items :=
  (Array.mem_filter.mp h).1

/-- `_mem`: the last-resort item is one the body wrote too. -/
private theorem overprintLoose_mem (items : Array (Raw × Array Raw))
    (it : Raw × Array Raw) (h : it ∈ overprintLoose items) : it ∈ items :=
  (Array.mem_filter.mp h).1

/-- An `{overprint}` as alternation with the count of items whose spec the
step model could not number, or `none` for a body this rewrite refuses to
read as an alternation at all — which leaves the environment standing, so
the unknown-environment warning names the loss at elaboration and the body
is kept as ONE reading rather than guessed at.

Content before the first item stays where it was written and shows on every
overlay, which is what an `\onslide`-less run means in beamer.

Every item whose spec names steps stays an alternative, in body order:
refusing one item never removes another, so a deck that spells one
incremental spec keeps every numbered item it wrote. The first item whose
spec cannot be numbered becomes the nesting's last resort — it inks exactly
the steps no numbered item claims, which for a deck that numbers the rest is
the reading beamer gives it — and a second such item cannot, there being one
last resort; the count travels so the caller names both losses.

The paragraph ends on both sides of the alternation because an overprint is
a block environment: the fence is what lets the nesting reach the block
level, where an item holding a list or two paragraphs steps whole instead of
being squeezed through one paragraph. -/
private def overprintPlan (body : Array Raw) (p : Pos) : Option (Array Raw × Nat) :=
  let (lead, items, bad) := overprintScan body.toList #[] none #[]
  if bad || items.isEmpty then none
  else
    let numbered := overprintNumbered items
    let loose := overprintLoose items
    let tail := match loose[0]? with | some (_, content) => content | none => #[]
    some (Id.run do
      let mut out : Array Raw := #[.par p]
      for r in lead do
        out := out.push r
      -- Last item outermost: the nesting is a priority chain, and beamer's
      -- overprint gives priority to the item written last (its items stack in
      -- one overlay area, so a later one covers an earlier). Head-first the
      -- chain is dead code from the first item whose range covers the whole
      -- window: `\onslide<1->` then `\onslide<2->` made item 1 win on every
      -- step, item 2 reachable from none, and the frame shipped two
      -- byte-identical pages with no diagnostic. Point specs are unaffected —
      -- their partitions are singletons either way.
      for r in overprintAlt p tail numbered.toList.reverse do
        out := out.push r
      return out.push (.par p), loose.size)

/-- `_accounts`: a plan that reports no unnumberable item made no refusal —
every item the body wrote is an alternative of the nesting. So an item this
pass could not number is never absent from the caller's count, and the one
caller says W0105 for it (`overprintRaw`): a refused item cannot reach the
artifact wordlessly. -/
private theorem overprintPlan_accounts (body : Array Raw) (p : Pos) (repl : Array Raw)
    (h : overprintPlan body p = some (repl, 0)) :
    overprintNumbered (overprintScan body.toList #[] none #[]).2.1
      = (overprintScan body.toList #[] none #[]).2.1 := by
  simp only [overprintPlan] at h
  split at h
  · exact absurd h (by simp)
  · injection h with h
    injection h with _ hn
    have hloose : overprintLoose (overprintScan body.toList #[] none #[]).2.1 = #[] :=
      Array.eq_empty_of_size_eq_zero hn
    have : ∀ it ∈ (overprintScan body.toList #[] none #[]).2.1, specNumbered it.1 = true := by
      intro it hit
      by_cases hs : specNumbered it.1
      · exact hs
      · have : it ∈ overprintLoose (overprintScan body.toList #[] none #[]).2.1 :=
          Array.mem_filter.mpr ⟨hit, by simp [hs]⟩
        rw [hloose] at this
        exact absurd this (by simp)
    exact Array.filter_eq_self.mpr this

mutual

/-- Splice every `{overprint}` in a raw sequence into its alternation. A
pass of its own, ahead of the idiom rewrite, for two reasons: the
replacement is a SEQUENCE where the environment was one node — wrapping it
in a group instead would offer the group to a frame as its title, which is
what `\begin{frame}{...}` reads — and running first leaves the items'
content to the main pass, so an idiom inside an alternative is rewritten
exactly as it would be anywhere else. -/
private def overprintList : List Raw → Array Raw → Nat → M (Array Raw)
  | [], out, _ => pure out
  | _ :: rest, out, skip + 1 => overprintList rest out skip
  | .ctrl "apptocmd" pos :: rest, out, 0 => do
    -- Overlay bodies inside a patch or callback are not live material.
    let args := rest.toArray
    let (_, k, _) := takeHookArgs args 0
    overprintList rest ((out.push (.ctrl "apptocmd" pos)) ++ args.extract 0 k) k
  | r :: rest, out, 0 => do
    let rs ← overprintRaw r
    overprintList rest (out ++ rs) 0
termination_by structural l _ _ => l

/-- Descend into a group or environment, so an overprint nested anywhere is
found. Split from the list walk so the recursion is structural on `Raw`, as
the idiom rewrite's own pair is. -/
private def overprintRaw : Raw → M (Array Raw)
  | .group body p => do return #[.group (← overprintList body.toList #[] 0) p]
  | .env "overprint" body p => do
    let body' ← overprintList body.toList #[] 0
    match overprintPlan body' p with
    | some (repl, loose) =>
      became "\\begin{overprint}" "\\alt alternation, one item per overlay" p
      -- A spec this pass could not number is named, once for the document:
      -- its item is placed where no numbered item claims an overlay, which
      -- is not where it was declared to stand, and a second such item has
      -- no place left at all. W0105 is the code for a spec that names no
      -- step, and the overlay arms already fire it on this key.
      if loose > 0 then
        let msg :=
          if loose == 1 then
            "an overprint item whose overlay specification does not name a \
step stands on the steps no other item claims"
          else
            "an overprint item whose overlay specification does not name a \
step stands on the steps no other item claims; a second such item is not shown"
        sayOnce "spec:overlay" .W0105 msg p
          (help := "write a numbered spec: <2>, <2->, or <2-3>; incremental \
specs are not modelled")
      return repl
    | none => return #[.env "overprint" body' p]
  | .env n body p => do return #[.env n (← overprintList body.toList #[] 0) p]
  | r => pure #[r]

end

/-- A scope's trailing length metadata. A space cannot occur in a control
word, so a document cannot spell this internal handoff. The keys identify
token sites; only the elaborator knows their resolved opening values. -/
public def lengthRestoreKeys? (name : String) : Option (Array String) :=
  let mark := "length restore "
  if name.startsWith mark then
    some ((name.drop mark.length).toString.splitOn ",").toArray
  else none

/-- TeX restores local assignments at the group's close (TeXbook ch. 24).
Carry names, never saved expressions: a referenced register may have
changed, and native token declarations are not in the rewrite's `lens`. -/
private def restoreLengths (keys : Array String) (p : Pos) : Array Raw :=
  if keys.isEmpty then #[]
  else #[.ctrl ("length restore " ++ String.intercalate "," keys.toList) p]

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
    unless (← get).inPicture do
      write fun st => { st with bodyNext := 1 }
    rewriteList inBody raws (out.push (.ctrl "define" pos)) rest (i + 1) 0
  | .ctrl name pos :: rest, i, 0 => do
    let inPicture := (← get).inPicture
    -- Pictures may leave through the TeX boundary. Native block, length
    -- and font markers have no TeX meaning; preserve their source here.
    -- Plain alert is the shared exception: its textcolor/bfseries bridge
    -- is understood by both the native label reader and standalone TeX.
    let rewritten : Option (Array Raw × Nat) ← if inPicture then do
        if overlayName name == "alert" &&
            (raws[skipSpaces raws (i + 1)]?.bind overlayWord?).isNone then
          pure ((← alertPlain pos raws (i + 1)).map fun (repl, j) =>
            (repl, j - (i + 1)))
        else pure none
      else rewriteCtrl (overlayName name) pos raws (i + 1)
    match rewritten with
    | some (repl, consumed) => rewriteList inBody raws (out ++ repl) rest (i + 1) consumed
    | none =>
      -- Item is a structural delimiter and cannot be redefined by a
      -- document (Elab.builtinNames); its saved meaning is the same token.
      let name := if inPicture || overlayName name == "item" then overlayName name else name
      rewriteList inBody raws (out.push (.ctrl name pos)) rest (i + 1) 0
  -- `#k` is the native parameter `\ak`. The digits may be glued to text
  -- (`#1,`), so the word is split. Outside a body `#` is literal: a colour.
  | .sym '#' p :: .word w wp :: rest, i, 0 => do
    let digits := w.toList.takeWhile Char.isDigit
    let tail := String.ofList (w.toList.drop digits.length)
    if (← get).inPicture || !inBody || digits.isEmpty then
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
  | .group body p => withBeamerScope do
    if (← get).inPicture then
      return .group (← rewriteList inBody body #[] body.toList 0 0) p
    -- A group is a macro body when a definition announced one. The count is
    -- zeroed for the descent and restored one lower on the way out, so a
    -- definition inside the body manages its own following group without
    -- stealing `\newenvironment`'s second half.
    let saved := (← get).bodyNext
    let savedDef := (← get).inDef
    let savedGroup := (← get).inGroup
    let savedLens := (← get).lens
    let savedLengths := (← get).localLengths
    let savedTop := (← get).tableTop
    let savedDefTop := (← get).defTop
    let savedBound := (← get).bound
    let savedCaptures := (← get).beamerCaptures
    write fun st => { st with bodyNext := 0, inDef := st.inDef || saved > 0, inGroup := true,
                              tableTop := false, defTop := saved > 0, localLengths := #[] }
    let body' ← rewriteList (inBody || saved > 0) body #[] body.toList 0 0
    let restores := restoreLengths (← get).localLengths p
    -- A group's assignments end with it (TeXbook ch. 24: an assignment is
    -- local to the group it stands in). Translating stored replacement
    -- text likewise installs none of the definitions it contains.
    write fun st => { st with bodyNext := saved - 1, inDef := savedDef, inGroup := savedGroup,
                              lens := savedLens, localLengths := savedLengths,
                              tableTop := savedTop, defTop := savedDefTop,
                              bound := if saved > 0 then savedBound else st.bound }
    -- premise: beamerTemplateChecks — a consumed local font declaration
    -- leaves no preamble content; nonempty groups still reach its checker.
    if (← get).wholeDoc && !(← get).inDoc && !savedDef && saved == 0 &&
        (← get).beamerCaptures > savedCaptures && !body.all (· == .space) &&
        restores.isEmpty && body'.all (· == .space) then
      return .space
    return .group (body' ++ restores) p
  | .env n body p => do
    -- An `\input` wrapper switches the file its diagnostics name.
    match Parse.inputEnvFile? n with
    | some f =>
      let saved := (← get).file
      write fun st => { st with file := f }
      let body' ← rewriteList inBody body #[] body.toList 0 0
      write fun st => { st with file := saved }
      return .env n body' p
    | none => withBeamerScope do
      if mathEnvs.contains n then
        return .env n body p
      -- premise: pictureBoundaryChecks — requests retain TeX
      -- commands while native styled labels still ship.
      else if (← get).inPicture || pictureEnvs.contains n then
        -- Every nested group/environment remains in the same source
        -- language; no native scope-restoration metadata enters a request.
        let saved := (← get).inPicture
        write fun st => { st with inPicture := true }
        let body' ← rewriteList inBody body #[] body.toList 0 0
        write fun st => { st with inPicture := saved }
        return .env n body' p
      else if n == "otherlanguage" || n == "otherlanguage*" then
        -- The environment form of the switch: the body takes the language
        -- attribute; the starred form differs only in date handling the
        -- engine does not model. The first group is the language.
        let savedTop := (← get).tableTop
        let savedDefTop := (← get).defTop
        write fun st => { st with tableTop := false, defTop := false }
        let body' ← rewriteList inBody body #[] body.toList 0 0
        write fun st => { st with tableTop := savedTop, defTop := savedDefTop }
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
        rewriteDocumentBody (rewriteList inBody body #[] body.toList 0 0) p
      else if n == "frame" then
        -- `Raw.env` carries no argument field, so a frame's `<spec>`, `[opts]`
        -- and `{title}` all arrive at the head of its body, and beamer writes
        -- the spec first (beamer manual §8.1). A reader knowing only
        -- `[opts]{title}` stops at the spec and the whole run, title
        -- included, sets as a paragraph. The spec is a parameter, so it is
        -- resolved here and the elaborator's reader sees what it expects.
        -- Decided before descending: a silenced frame's body must not spend
        -- the once-per-document diagnostics of content that never ships.
        match specWordAt body (skipSpaces body 0) with
        | some w =>
          if (← get).deck && modeSilencesPresentation w then
            say .N0104
              s!"'{w}' declares no presentation slides; this frame ships no page" p
            return .group #[] p
          else
            sayOnce "spec:frame" .W0110
              s!"'\\begin\{frame}{w}' specification is not honoured; a frame's \
steps come from its body" p
              (help := "\\pause and \\uncover step a frame's own content")
            let body' ← rewriteList inBody body #[] body.toList 0 0
            let i := skipSpaces body' 0
            match specWordAt body' i with
            | some _ => return .env n (body'.extract (i + 1) body'.size) p
            | none => return .env n body' p
        | none => return .env n (← rewriteList inBody body #[] body.toList 0 0) p
      else if n == "titlepage" then
        -- article.cls's `titlepage` opens a fresh page, applies the empty
        -- page style, and resets page to one. Its closing newpage resets
        -- again only in oneside mode (classes.dtx, `\titlepage`). Both
        -- declarations are shared IR page-opening marks: an empty style
        -- lasts until a page ships, even when this body is empty.
        -- The body is an ordinary block sequence scoped by
        -- the group that carries it — an environment is a group (ltmiscen.dtx:
        -- `\begin` opens one; TeXbook ch. 5), so a declaration inside ends at
        -- the close and the body elaborates through the top-level block
        -- paths. The isolation is `\pagebreak`'s,
        -- whose vertical distribution and ground stand (`Layout.collectBlocks`,
        -- `.pagebreak`), and adjacent or boundary breaks close only a page
        -- holding content, so an empty or leading title page leaves no blank
        -- page behind. HTML drops the boundaries and their declarations, so
        -- the body stays one continuous semantic flow with no paged artifact.
        let st0 ← get
        write fun st => { st with tableTop := false, defTop := false, localLengths := #[] }
        let body' ← rewriteList inBody body #[] body.toList 0 0
        let restores := restoreLengths (← get).localLengths p
        write fun st => { st with lens := st0.lens, localLengths := st0.localLengths,
                                  tableTop := st0.tableTop, defTop := st0.defTop }
        became "\\begin{titlepage}…\\end{titlepage}"
          "an isolated flow page opening with empty running furniture and folio one" p
        let close := if st0.titlepageReset then
          #[Raw.ctrl "pagebreak" p, Raw.ctrl Ir.titlePageEndRole p]
          else #[Raw.ctrl "pagebreak" p]
        return .group (#[Raw.ctrl "pagebreak" p, Raw.ctrl Ir.titlePageBeginRole p] ++
          body' ++ close ++ restores) p
      else if let some spec := ((← get).discardEnvs.find? (·.1 == n)).map (·.2) then
        -- environ's discarding environment: only the arguments its
        -- signature reads reach the definition, as written; the body is
        -- dropped unread, so nothing of it is judged or ships.
        let k := spec.foldl (fun k c =>
          if c == 'o' then (takeOpt body k).2 else (takeGroups body k 1).2) 0
        return .env n (body.extract 0 k) p
      else
        -- An environment is a group (ltmiscen.dtx: `\begin` opens one), so
        -- a length set inside it ends with it; inside a list, a list
        -- parameter set there is that list's own.
        let st0 ← get
        write fun st => { st with inList := st.inList || listEnvs.contains n,
                                  tableTop := tableEnvs.contains n, defTop := false,
                                  inParacol := n == "paracol", localLengths := #[] }
        let body' ← rewriteList inBody body #[] body.toList 0 0
        let restores := restoreLengths (← get).localLengths p
        write fun st => { st with lens := st0.lens, localLengths := st0.localLengths,
                                  inList := st0.inList,
                                  tableTop := st0.tableTop, defTop := st0.defTop,
                                  inParacol := st0.inParacol }
        if n == "paracol" then
          paracolEnv st0.paracolRatio body' p restores
        else return .env n (body' ++ restores) p
  | r => pure r

end

private theorem rewriteCtrlAt_named_scope (name : String) (pos : Pos)
    (raws : Array Raw) (start : Nat) (s : St)
    (hd : (s.wholeDoc && s.deck && !s.inDoc && !s.inDef) = false)
    (hl : St.inList s = false)
    (hLit : literalReplace.lookup name = none)
    (hCite : (name == "cite") = false)
    (hAppendix : (name == "appendix") = false)
    (hKernel : kernelSkip (name ++ "amount") = none)
    (hSimple : simpleNative.lookup name = none)
    (hHooks : deferredHooks.lookup name = none)
    (hAssign : plainAssign? name raws start = none) :
    rewriteCtrl.rewriteCtrlAt name pos raws start s =
      rewriteCtrlNamed name pos raws start s := by
  have hSettings : listSettings? s name = none := by
    simp [listSettings?, hl]
  simp only [rewriteCtrl.rewriteCtrlAt]
  simp [bind, StateT.bind, pure, get, getThe, MonadStateOf.get,
    StateT.get, hd, hLit, hCite, hAppendix, hSimple, hHooks, hAssign]
  cases hLens : (St.lens s).find? (fun x => x.1 == name ++ "amount") with
  | none =>
    dsimp only [bind, StateT.bind, StateT.get, pure]
    simp only [hSettings]
  | some entry =>
    cases entry
    simp only [hKernel, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    dsimp only [bind, StateT.bind, StateT.get, pure]
    simp only [hSettings]

private theorem rewriteCtrlAt_named_exact (name : String) (pos : Pos)
    (raws : Array Raw) (start : Nat) (s : St)
    (hd : St.inDoc s = true) (hl : St.inList s = false)
    (hLit : literalReplace.lookup name = none)
    (hCite : (name == "cite") = false)
    (hAppendix : (name == "appendix") = false)
    (hKernel : kernelSkip (name ++ "amount") = none)
    (hSimple : simpleNative.lookup name = none)
    (hHooks : deferredHooks.lookup name = none)
    (hAssign : plainAssign? name raws start = none) :
    rewriteCtrl.rewriteCtrlAt name pos raws start s =
      rewriteCtrlNamed name pos raws start s :=
  rewriteCtrlAt_named_scope name pos raws start s (by simp [hd]) hl
    hLit hCite hAppendix hKernel hSimple hHooks hAssign

private theorem rewriteCtrl_package_named (command names : String) (pos gp np : Pos)
    (st : St) (hc : command = "usepackage" ∨ command = "RequirePackage")
    (hd : st.wholeDoc = false) (hl : st.inList = false) :
    rewriteCtrl.rewriteCtrlAt command pos (packageCall command names pos gp np) 1 st =
      rewriteCtrlNamed command pos (packageCall command names pos gp np) 1 st := by
  apply rewriteCtrlAt_named_scope _ _ _ _ _ (by simp [hd]) hl
  all_goals rcases hc with rfl | rfl <;> rfl

private theorem rewriteCtrlNamed_package_external_exact
    (command names : String) (pos gp np : Pos) (st : St)
    (hc : command = "usepackage" ∨ command = "RequirePackage")
    (hd : st.inDoc = false) (hdef : st.inDef = false)
    (hn : ∀ p ∈ names.trimAscii.toString.splitOn "," |>.map (·.trimAscii.toString),
      nativePackages.contains p = false)
    (hb : ∀ p ∈ names.trimAscii.toString.splitOn "," |>.map (·.trimAscii.toString),
      (boundaryPkgs.contains p && st.boundaryOpen) = false)
    (ht : ∀ p ∈ names.trimAscii.toString.splitOn "," |>.map (·.trimAscii.toString),
      themeSlotOfPackage? p = none) :
    rewriteCtrlNamed command pos (packageCall command names pos gp np) 1 st =
      (some (#[], 2), { st with diags := st.diags ++
        ((names.trimAscii.toString.splitOn ",").map fun p =>
          atSource st pos (packageRefusal st.file pos p.trimAscii.toString)).toArray }) := by
  have hread := packageCall_readers command names pos gp np
  have hempty : (#[#[Raw.word names np]] : Array (Array Raw)).isEmpty = false := by rfl
  have hsrc : rawSrc ((#[#[Raw.word names np]] : Array (Array Raw)).getD 0 #[]) =
      names.trimAscii.toString := by simp [rawSrc, rawSrcList, rawSrcOne]
  have hpkgs := rewritePackages_external_exact command
    ((names.trimAscii.toString.splitOn ",").map (·.trimAscii.toString)) none pos st hn hb ht
  rcases hc with rfl | rfl <;>
    simp only [rewriteCtrlNamed, bind, StateT.bind, get, getThe,
      MonadStateOf.get, StateT.get, hd, hdef, Bool.false_eq_true, ↓reduceIte,
      hread.2.1, hread.2.2, hempty, hsrc, hpkgs, pure, StateT.pure, List.map_map,
      Function.comp_def]

private theorem rewriteCtrl_package_external_exact
    (command names : String) (pos gp np : Pos) (st : St)
    (hc : command = "usepackage" ∨ command = "RequirePackage")
    (hd : st.inDoc = false) (hdef : st.inDef = false)
    (hw : st.wholeDoc = false) (hl : st.inList = false)
    (hn : ∀ p ∈ names.trimAscii.toString.splitOn "," |>.map (·.trimAscii.toString),
      nativePackages.contains p = false)
    (hb : ∀ p ∈ names.trimAscii.toString.splitOn "," |>.map (·.trimAscii.toString),
      (boundaryPkgs.contains p && st.boundaryOpen) = false)
    (ht : ∀ p ∈ names.trimAscii.toString.splitOn "," |>.map (·.trimAscii.toString),
      themeSlotOfPackage? p = none)
    (part : String) (hp : part ∈ names.trimAscii.toString.splitOn ",") :
    rewriteCtrl command pos (packageCall command names pos gp np) 1 st =
      (some (#[], 1), { st with diags := st.diags ++
        ((names.trimAscii.toString.splitOn ",").map fun p =>
          atSource st pos (packageRefusal st.file pos p.trimAscii.toString)).toArray }) := by
  have hlen := List.length_pos_of_mem hp
  have hsize : (st.diags ++
      ((names.trimAscii.toString.splitOn ",").map fun p =>
        atSource st pos (packageRefusal st.file pos p.trimAscii.toString)).toArray).size >
      st.diags.size := by
    simp only [Array.size_append, List.size_toArray, List.length_map]
    omega
  simp only [rewriteCtrl, rewriteCtrl_package_named command names pos gp np st hc hw hl,
    rewriteCtrlNamed_package_external_exact command names pos gp np st hc hd hdef hn hb ht,
    Array.isEmpty_empty, ↓reduceIte, account]
  rw [ite_eq_left (Or.inl hsize)]

private theorem rewriteCtrl_value_exact (name : String) (pos : Pos)
    (raws : Array Raw) (start : Nat) (s : St) :
    (rewriteCtrl name pos raws start s).1 =
      (rewriteCtrl.rewriteCtrlAt name pos raws start s).1.map
        (fun (rs, k) => (rs, k - start)) := by
  unfold rewriteCtrl
  cases h : rewriteCtrl.rewriteCtrlAt name pos raws start s with
  | mk result st =>
    cases result with
    | none => rfl
    | some entry =>
      cases entry
      rfl

private theorem meaningFree_routes_exact (name : String) (n : Nat) (note : Option String)
    (hm : (name, n, note) ∈ meaningFree) (pos : Pos) (raws : Array Raw) (start : Nat) :
    literalReplace.lookup name = none ∧
    (name == "cite") = false ∧
    (name == "appendix") = false ∧
    kernelSkip (name ++ "amount") = none ∧
    simpleNative.lookup name = none ∧
    deferredHooks.lookup name = none ∧
    plainAssign? name raws start = none ∧
    rewriteCtrlNamed name pos raws start = rewriteCtrlLater name pos raws start ∧
    styOptionsRequest name pos raws start = pure none ∧
    rewriteCtrlLaterNamed name pos raws start = (do
      let (_, k) := takeGroups raws start n
      meaningFreeReport name pos note
      return some (#[], k)) := by
  simp only [meaningFree, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hm
  rcases hm with h | h | h |
    h | h | h |
    h | h | h |
    h | h | h |
    h | h | h |
    h | h | h |
    h | h | h |
    h | h | h |
    h | h | h |
    h | h | h |
    h | h | h
  all_goals
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem rewriteCtrl_meaningFree_exact (s : St) (pos : Pos)
    (raws : Array Raw) (start : Nat) (name : String) (n : Nat) (note : Option String)
    (hm : (name, n, note) ∈ meaningFree)
    (hd : St.inDoc s = true) (hl : St.inList s = false) :
    (rewriteCtrl name pos raws start s).1 =
      some (#[], (takeGroups raws start n).2 - start) := by
  obtain ⟨hLit, hCite, hAppendix, hKernel, hSimple, hHooks, hAssign,
    hNamed, hOptions, hLater⟩ := meaningFree_routes_exact name n note hm pos raws start
  rw [rewriteCtrl_value_exact, rewriteCtrlAt_named_exact name pos raws start s hd hl
    hLit hCite hAppendix hKernel hSimple hHooks hAssign, hNamed]
  simp only [rewriteCtrlLater, hOptions, bind, StateT.bind, pure]
  rw [hLater]
  cases note <;> rfl

/-- The descriptor's only state effect, including the dispatcher's guard.
There is deliberately no source-array or operand parameter. -/
private def meaningFreeState (s : St) (name : String) (pos : Pos)
    (note : Option String) : St :=
  (account name pos s (meaningFreeReport name pos note s).2).2

private def configSkipState (s : St) (name : String) (pos : Pos)
    (msg : String) (help : Option String) : St :=
  (account name pos s (configSkipReport name pos msg help s).2).2

private theorem rewriteCtrl_meaningFree_state (s : St) (pos : Pos)
    (raws : Array Raw) (start : Nat) (name : String) (n : Nat) (note : Option String)
    (hm : (name, n, note) ∈ meaningFree)
    (hd : St.inDoc s = true) (hl : St.inList s = false) :
    (rewriteCtrl name pos raws start s).2 = meaningFreeState s name pos note := by
  obtain ⟨hLit, hCite, hAppendix, hKernel, hSimple, hHooks, hAssign,
    hNamed, hOptions, hLater⟩ := meaningFree_routes_exact name n note hm pos raws start
  unfold rewriteCtrl
  rw [rewriteCtrlAt_named_exact name pos raws start s hd hl
    hLit hCite hAppendix hKernel hSimple hHooks hAssign, hNamed]
  simp only [rewriteCtrlLater, hOptions, bind, StateT.bind, pure]
  rw [hLater]
  cases note <;> rfl

private theorem rewriteCtrl_configSkip_exact (s : St) (pos : Pos)
    (raws : Array Raw) (start : Nat) (name : String) (n : Nat)
    (msg : String) (help : Option String)
    (hm : (name, n, msg, help) ∈ configSkip)
    (hd : St.inDoc s = true) (hl : St.inList s = false) :
    (rewriteCtrl name pos raws start s).1 =
      some (#[], (takeGroups raws start n).2 - start) := by
  simp only [configSkip, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
  rw [rewriteCtrl_value_exact, rewriteCtrlAt_named_exact "sloppy" pos raws start s hd hl
    rfl rfl rfl rfl rfl rfl rfl]
  rfl

private theorem rewriteCtrl_configSkip_state (s : St) (pos : Pos)
    (raws : Array Raw) (start : Nat) (name : String) (n : Nat)
    (msg : String) (help : Option String)
    (hm : (name, n, msg, help) ∈ configSkip)
    (hd : St.inDoc s = true) (hl : St.inList s = false) :
    (rewriteCtrl name pos raws start s).2 = configSkipState s name pos msg help := by
  simp only [configSkip, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
  unfold rewriteCtrl
  rw [rewriteCtrlAt_named_exact "sloppy" pos raws start s hd hl
    rfl rfl rfl rfl rfl rfl rfl]
  rfl

private theorem rewriteCtrl_unknown_exact (s : St) (pos : Pos)
    (raws : Array Raw) (start : Nat)
    (hd : St.inDoc s = true) (hl : St.inList s = false) :
    rewriteCtrl "zzNotAControl" pos raws start s = (none, s) := by
  have hAt : rewriteCtrl.rewriteCtrlAt "zzNotAControl" pos raws start s = (none, s) := by
    rw [rewriteCtrlAt_named_exact "zzNotAControl" pos raws start s hd hl
      rfl rfl rfl rfl rfl rfl rfl]
    rfl
  unfold rewriteCtrl
  rw [hAt]

private theorem meaningFree_names_exact (name : String) (n : Nat) (note : Option String)
    (hm : (name, n, note) ∈ meaningFree) :
    name ≠ "define" ∧ overlayName name = name := by
  simp only [meaningFree, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hm
  rcases hm with h | h | h |
    h | h | h |
    h | h | h |
    h | h | h |
    h | h | h |
    h | h | h |
    h | h | h |
    h | h | h |
    h | h | h |
    h | h | h |
    h | h | h
  all_goals
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨by simp, by simp [overlayName, String.startsWith_string_iff]⟩

private theorem rewriteList_skip_exact (inBody : Bool) (raws out : Array Raw)
    (taken rest : List Raw) (i : Nat) :
    rewriteList inBody raws out (taken ++ rest) i taken.length =
      rewriteList inBody raws out rest (i + taken.length) 0 := by
  induction taken generalizing i with
  | nil => simp
  | cons x taken ih =>
    simp only [List.cons_append, List.length_cons]
    rw [rewriteList, ih]
    congr 1 <;> omega

/-- Literal material surrounding an ordinary body control. Its text is
arbitrary; there is no command reader whose operands could cross the hole.
The raw syntax, rather than a test of the rewritten result, states this
boundary. -/
public inductive LiteralRaws : List Raw → Prop where
  | nil : LiteralRaws []
  | word (text : String) (pos : Pos) : LiteralRaws rest →
      LiteralRaws (.word text pos :: rest)
  | space : LiteralRaws rest → LiteralRaws (.space :: rest)
  | par (pos : Pos) : LiteralRaws rest → LiteralRaws (.par pos :: rest)
  | verb (env text : String) (pos : Pos) : LiteralRaws rest →
      LiteralRaws (.verb env text pos :: rest)

private theorem rewriteList_literal_prefix (inBody : Bool) (raws out : Array Raw)
    (pre rest : List Raw) (i : Nat) (hpre : LiteralRaws pre) :
    rewriteList inBody raws out (pre ++ rest) i 0 =
      rewriteList inBody raws (out ++ pre.toArray) rest (i + pre.length) 0 := by
  induction hpre generalizing out i with
  | nil => simp
  | word text pos _ ih
  | space _ ih
  | par pos _ ih
  | verb env text pos _ ih =>
    rw [List.cons_append, rewriteList]
    all_goals try simp
    change rewriteList inBody raws (out.push _) (_ ++ rest) (i + 1) 0 = _
    rw [ih]
    congr 1
    · apply Array.toList_inj.mp
      simp only [Array.toList_append, Array.toList_push,
        List.append_assoc, List.singleton_append]
    · omega

private theorem rewriteList_literal_exact (inBody : Bool) (raws out : Array Raw)
    (rest : List Raw) (i : Nat) (st : St) (hrest : LiteralRaws rest) :
    rewriteList inBody raws out rest i 0 st = (out ++ rest.toArray, st) := by
  have h := rewriteList_literal_prefix inBody raws out rest [] i hrest
  simp only [List.append_nil, rewriteList] at h
  exact congrFun h st

private theorem rewriteList_control_exact (inBody : Bool) (raws out : Array Raw)
    (name : String) (pos : Pos) (taken rest : List Raw) (i : Nat) (s s' : St)
    (hdef : name ≠ "define") (hpic : St.inPicture s = false)
    (hstep : rewriteCtrl (overlayName name) pos raws (i + 1) s =
      (some (#[], taken.length), s')) :
    rewriteList inBody raws out (.ctrl name pos :: (taken ++ rest)) i 0 s =
      rewriteList inBody raws out rest (i + 1 + taken.length) 0 s' := by
  rw [rewriteList]
  case x_3 => exact fun h => hdef h
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, hpic, Bool.false_eq_true, ↓reduceIte, hstep, Array.append_empty]
  rw [rewriteList_skip_exact]

private theorem rewriteList_package_external_exact
    (command names : String) (pos gp np : Pos) (st : St)
    (hc : command = "usepackage" ∨ command = "RequirePackage")
    (hd : st.inDoc = false) (hf : st.inDef = false) (hw : st.wholeDoc = false)
    (hl : st.inList = false) (hpic : st.inPicture = false)
    (hn : ∀ p ∈ names.trimAscii.toString.splitOn "," |>.map (·.trimAscii.toString),
      nativePackages.contains p = false)
    (hb : ∀ p ∈ names.trimAscii.toString.splitOn "," |>.map (·.trimAscii.toString),
      (boundaryPkgs.contains p && st.boundaryOpen) = false)
    (ht : ∀ p ∈ names.trimAscii.toString.splitOn "," |>.map (·.trimAscii.toString),
      themeSlotOfPackage? p = none)
    (part : String) (hp : part ∈ names.trimAscii.toString.splitOn ",") :
    rewriteList false (packageCall command names pos gp np) #[]
      (packageCall command names pos gp np).toList 0 0 st =
      (#[], { st with diags := st.diags ++
        ((names.trimAscii.toString.splitOn ",").map fun p =>
          atSource st pos (packageRefusal st.file pos p.trimAscii.toString)).toArray }) := by
  have hdef : command ≠ "define" := by rcases hc with rfl | rfl <;> simp
  have ho : overlayName command = command := by
    rcases hc with rfl | rfl <;> simp [overlayName, String.startsWith_string_iff]
  have hstep := rewriteCtrl_package_external_exact command names pos gp np st
    hc hd hf hw hl hn hb ht part hp
  have h := rewriteList_control_exact false (packageCall command names pos gp np) #[]
    command pos [.group #[.word names np] gp] [] 0 st _ hdef hpic
    (by simpa only [ho, Nat.zero_add, List.length_cons, List.length_nil] using hstep)
  exact h

private theorem rewriteList_meaningFree_exact (inBody : Bool) (raws out : Array Raw)
    (name : String) (n : Nat) (note : Option String) (pos : Pos)
    (args : List (Array Raw)) (taken rest : List Raw) (i : Nat) (s : St)
    (hm : (name, n, note) ∈ meaningFree)
    (hd : St.inDoc s = true) (hl : St.inList s = false) (hp : St.inPicture s = false)
    (hn : args.length = n)
    (hg : GroupPrefix raws (i + 1) args (i + 1 + taken.length)) :
    rewriteList inBody raws out (.ctrl name pos :: (taken ++ rest)) i 0 s =
      rewriteList inBody raws out rest (i + 1 + taken.length) 0
        (rewriteCtrl name pos raws (i + 1) s).2 := by
  have hvalue := rewriteCtrl_meaningFree_exact s pos raws (i + 1) name n note hm hd hl
  have hread := takeGroups_prefix_exact hg
  rw [hn] at hread
  rw [hread] at hvalue
  simp only [Nat.add_sub_cancel_left] at hvalue
  obtain ⟨hdef, hoverlay⟩ := meaningFree_names_exact name n note hm
  apply rewriteList_control_exact inBody raws out name pos taken rest i s _ hdef hp
  rw [hoverlay]
  exact Prod.ext hvalue rfl

private theorem rewriteList_unknown_exact (inBody : Bool) (raws out : Array Raw)
    (pos : Pos) (rest : List Raw) (i : Nat) (s : St)
    (hd : St.inDoc s = true) (hl : St.inList s = false) (hp : St.inPicture s = false) :
    rewriteList inBody raws out (.ctrl "zzNotAControl" pos :: rest) i 0 s =
      rewriteList inBody raws (out.push (.ctrl "zzNotAControl" pos)) rest (i + 1) 0 s := by
  rw [rewriteList]
  case x_3 => simp
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, hp, Bool.false_eq_true, ↓reduceIte]
  have hoverlay : overlayName "zzNotAControl" = "zzNotAControl" := by
    simp [overlayName, String.startsWith_string_iff]
  rw [hoverlay, rewriteCtrl_unknown_exact s pos raws (i + 1) hd hl]
  rfl

private theorem rewriteList_configSkip_exact (inBody : Bool) (raws out : Array Raw)
    (name : String) (n : Nat) (msg : String) (help : Option String) (pos : Pos)
    (args : List (Array Raw)) (taken rest : List Raw) (i : Nat) (s : St)
    (hm : (name, n, msg, help) ∈ configSkip)
    (hd : St.inDoc s = true) (hl : St.inList s = false) (hp : St.inPicture s = false)
    (hn : args.length = n)
    (hg : GroupPrefix raws (i + 1) args (i + 1 + taken.length)) :
    rewriteList inBody raws out (.ctrl name pos :: (taken ++ rest)) i 0 s =
      rewriteList inBody raws out rest (i + 1 + taken.length) 0
        (rewriteCtrl name pos raws (i + 1) s).2 := by
  have hvalue := rewriteCtrl_configSkip_exact s pos raws (i + 1) name n msg help hm hd hl
  have hread := takeGroups_prefix_exact hg
  rw [hn] at hread
  rw [hread] at hvalue
  simp only [Nat.add_sub_cancel_left] at hvalue
  have hnames : name ≠ "define" ∧ overlayName name = name := by
    simp only [configSkip, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
    exact ⟨by simp, by simp [overlayName, String.startsWith_string_iff]⟩
  apply rewriteList_control_exact inBody raws out name pos taken rest i s _ hnames.1 hp
  rw [hnames.2]
  exact Prod.ext hvalue rfl

private theorem rewriteList_meaningFree_body_exact (inBody : Bool)
    (raws out : Array Raw) (name : String) (n : Nat) (note : Option String)
    (pos : Pos) (pre taken post : List Raw) (args : List (Array Raw))
    (i : Nat) (s : St) (hm : (name, n, note) ∈ meaningFree)
    (hd : s.inDoc = true) (hl : s.inList = false) (hp : s.inPicture = false)
    (hpre : LiteralRaws pre) (hpost : LiteralRaws post) (hn : args.length = n)
    (hg : GroupPrefix raws (i + pre.length + 1) args
      (i + pre.length + 1 + taken.length)) :
    rewriteList inBody raws out (pre ++ .ctrl name pos :: (taken ++ post)) i 0 s =
      (out ++ pre.toArray ++ post.toArray, meaningFreeState s name pos note) := by
  rw [rewriteList_literal_prefix _ _ _ _ _ _ hpre,
    rewriteList_meaningFree_exact _ _ _ _ _ _ _ _ _ _ _ _ hm hd hl hp hn hg,
    rewriteCtrl_meaningFree_state _ _ _ _ _ _ _ hm hd hl,
    rewriteList_literal_exact _ _ _ _ _ _ hpost]

private theorem rewriteList_configSkip_body_exact (inBody : Bool)
    (raws out : Array Raw) (name : String) (n : Nat) (msg : String)
    (help : Option String) (pos : Pos) (pre taken post : List Raw)
    (args : List (Array Raw)) (i : Nat) (s : St)
    (hm : (name, n, msg, help) ∈ configSkip)
    (hd : s.inDoc = true) (hl : s.inList = false) (hp : s.inPicture = false)
    (hpre : LiteralRaws pre) (hpost : LiteralRaws post) (hn : args.length = n)
    (hg : GroupPrefix raws (i + pre.length + 1) args
      (i + pre.length + 1 + taken.length)) :
    rewriteList inBody raws out (pre ++ .ctrl name pos :: (taken ++ post)) i 0 s =
      (out ++ pre.toArray ++ post.toArray, configSkipState s name pos msg help) := by
  rw [rewriteList_literal_prefix _ _ _ _ _ _ hpre,
    rewriteList_configSkip_exact _ _ _ _ _ _ _ _ _ _ _ _ _ hm hd hl hp hn hg,
    rewriteCtrl_configSkip_state _ _ _ _ _ _ _ _ hm hd hl,
    rewriteList_literal_exact _ _ _ _ _ _ hpost]

/-- An ordinary body control consumes exactly its declared argument prefix.
The source cursor agrees with the array the actual dispatcher reads.
Arguments and continuation are arbitrary; `GroupPrefix` includes intervening
spaces. The complete walk equals its continuation with the dispatcher's
post-state, and that dispatch adds a diagnostic or records a write.

This is a contract of the compatibility stream, before elaboration. The body
state excludes list-parameter dispatch and picture pass-through. -/
public def ControlGroupsConsumed (name : String) (arity : Nat) : Prop :=
  ∀ (inBody : Bool) (raws out : Array Raw) (pos : Pos)
    (args : List (Array Raw)) (taken rest : List Raw) (i : Nat) (s : St),
    St.inDoc s = true → St.inList s = false → St.inPicture s = false →
    raws.toList.drop i = .ctrl name pos :: (taken ++ rest) →
    args.length = arity →
    GroupPrefix raws (i + 1) args (i + 1 + taken.length) →
    let dispatched := rewriteCtrl name pos raws (i + 1) s
    dispatched.1 = some (#[], taken.length) ∧
    rewriteList inBody raws out (raws.toList.drop i) i 0 s =
      rewriteList inBody raws out rest (i + 1 + taken.length) 0 dispatched.2 ∧
    ((St.diags dispatched.2).size > (St.diags s).size ∨
      St.writes dispatched.2 > St.writes s)

/-- The actual dispatcher leaves a command and every following raw available
to elaboration. This does not assert what elaboration's recovery emits. -/
public def UnknownControlPreserved (name : String) : Prop :=
  ∀ (inBody : Bool) (raws out : Array Raw) (pos : Pos)
    (rest : List Raw) (i : Nat) (s : St),
    St.inDoc s = true → St.inList s = false → St.inPicture s = false →
    raws.toList.drop i = .ctrl name pos :: rest →
    rewriteCtrl name pos raws (i + 1) s = (none, s) ∧
    rewriteList inBody raws out (raws.toList.drop i) i 0 s =
      rewriteList inBody raws (out.push (.ctrl name pos)) rest (i + 1) 0 s

public theorem meaningFree_control_contract (row : String × Nat × Option String)
    (hm : row ∈ meaningFree) : ControlGroupsConsumed row.1 row.2.1 := by
  rcases row with ⟨name, n, note⟩
  intro inBody raws out pos args taken rest i s hd hl hp hsource hn hg
  dsimp only
  have hvalue := rewriteCtrl_meaningFree_exact s pos raws (i + 1) name n note hm hd hl
  have hread := takeGroups_prefix_exact hg
  rw [hn] at hread
  rw [hread] at hvalue
  simp only [Nat.add_sub_cancel_left] at hvalue
  refine ⟨hvalue, ?_, ?_⟩
  · rw [hsource]
    exact rewriteList_meaningFree_exact inBody raws out name n note pos
      args taken rest i s hm hd hl hp hn hg
  · exact rewriteCtrl_accounts name pos raws (i + 1) s _ taken.length
      (Prod.ext hvalue rfl)

public theorem configSkip_control_contract (row : String × Nat × String × Option String)
    (hm : row ∈ configSkip) : ControlGroupsConsumed row.1 row.2.1 := by
  rcases row with ⟨name, n, msg, help⟩
  intro inBody raws out pos args taken rest i s hd hl hp hsource hn hg
  dsimp only
  have hvalue := rewriteCtrl_configSkip_exact s pos raws (i + 1) name n msg help hm hd hl
  have hread := takeGroups_prefix_exact hg
  rw [hn] at hread
  rw [hread] at hvalue
  simp only [Nat.add_sub_cancel_left] at hvalue
  refine ⟨hvalue, ?_, ?_⟩
  · rw [hsource]
    exact rewriteList_configSkip_exact inBody raws out name n msg help pos
      args taken rest i s hm hd hl hp hn hg
  · exact rewriteCtrl_accounts name pos raws (i + 1) s _ taken.length
      (Prod.ext hvalue rfl)

public theorem unknown_control_contract : UnknownControlPreserved "zzNotAControl" := by
  intro inBody raws out pos rest i s hd hl hp hsource
  refine ⟨rewriteCtrl_unknown_exact s pos raws (i + 1) hd hl, ?_⟩
  rw [hsource]
  exact rewriteList_unknown_exact inBody raws out pos rest i s hd hl hp

/-- A checkpoint of the production compatibility walk. The source array is
kept intact because command readers address it by index. `out` is the
already rewritten prefix; the remaining input is exactly `raws.drop index`.
The execution state is opaque outside its owner module. -/
public structure RewriteCursor where
  inBody : Bool
  raws : Array Raw
  out : Array Raw := #[]
  index : Nat := 0
  private state : St
  private complete : (Array Raw × St) → (Array Raw × St) := id

/-- The ordinary document-body dispatch, excluding the list-parameter and
picture interpreters which give the same token a different meaning. -/
public def RewriteCursor.inDocument (cursor : RewriteCursor) : Prop :=
  cursor.state.inDoc = true ∧ cursor.state.inList = false ∧
    cursor.state.inPicture = false

/-- The scope permits entry into an ordinary document environment. -/
public def RewriteCursor.outsidePicture (cursor : RewriteCursor) : Prop :=
  cursor.state.inPicture = false

/-- The ordinary document entry does not inherit a list-parameter scope. -/
public def RewriteCursor.outsideList (cursor : RewriteCursor) : Prop :=
  cursor.state.inList = false

/-- Replace the unread final document at a checkpoint while retaining its
already executed state, output prefix and enclosing continuation. This
boundary is after macro/input execution: operands may themselves have had
effects before reaching it. -/
public def RewriteCursor.withDocument (cursor : RewriteCursor) (body : Array Raw)
    (pos : Pos) : RewriteCursor :=
  { cursor with raws := #[.env "document" body pos], index := 0 }

/-- Resume the actual walk at a checkpoint. This is also the operation used
by whole-document compatibility completion. -/
private def rewriteCursor (cursor : RewriteCursor) : Array Raw × St :=
  cursor.complete (rewriteList cursor.inBody cursor.raws cursor.out
    (cursor.raws.toList.drop cursor.index) cursor.index 0 cursor.state)

/-- The continuation after an accounted control has consumed its groups.
Only the command dispatch runs: no raw from the consumed prefix is rewritten
or appended to the output. -/
public def RewriteCursor.afterControl (cursor : RewriteCursor) (name : String)
    (pos : Pos) (consumed : Nat) : RewriteCursor :=
  { cursor with
    index := cursor.index + 1 + consumed
    state := (rewriteCtrl name pos cursor.raws (cursor.index + 1) cursor.state).2 }

/-- Descend into the document environment at this checkpoint. Its return
continuation restores the real enclosing scope and resumes the containing
walk. In particular the document's consumed groups do not become a separate
top-level compatibility run. -/
public def RewriteCursor.enterDocument (cursor : RewriteCursor)
    (body : Array Raw) (pos : Pos) : RewriteCursor :=
  { inBody := cursor.inBody
    raws := body
    state := (openDocumentBody cursor.state).2
    complete := fun result =>
      let (raw, st) := closeBeamerScope cursor.state (closeDocumentBody pos result)
      cursor.complete (rewriteList cursor.inBody cursor.raws (cursor.out.push raw)
        (cursor.raws.toList.drop (cursor.index + 1)) (cursor.index + 1) 0 st) }

private theorem rewriteRaw_document_exact (inBody : Bool) (body : Array Raw)
    (pos : Pos) (st : St) (hp : st.inPicture = false) :
    rewriteRaw inBody (.env "document" body pos) st =
      closeBeamerScope st
        (rewriteDocumentBody (rewriteList inBody body #[] body.toList 0 0) pos st) := by
  rw [rewriteRaw]
  simp only [Parse.inputEnvFile?, String.startsWith_string_iff]
  simp [withBeamerScope, closeBeamerScope, mathEnvs, pictureEnvs, hp,
    bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure]

private theorem rewriteCursor_document_exact (cursor : RewriteCursor)
    (body : Array Raw) (pos : Pos) (rest : List Raw)
    (hp : cursor.state.inPicture = false)
    (hs : cursor.raws.toList.drop cursor.index = .env "document" body pos :: rest) :
    rewriteCursor cursor = rewriteCursor (cursor.enterDocument body pos) := by
  have ht : cursor.raws.toList.drop (cursor.index + 1) = rest := by
    rw [← List.drop_drop, hs]
    rfl
  simp only [rewriteCursor, hs]
  rw [rewriteList]
  case x_3 => simp
  case x_4 => simp
  case x_5 => simp
  simp only [bind, StateT.bind, rewriteRaw_document_exact _ _ _ _ hp,
    RewriteCursor.enterDocument, List.drop_zero, ht, rewriteDocumentBody]

private def closeLastDocument (cursor : RewriteCursor) (pos : Pos)
    (result : Array Raw × St) : Array Raw × St :=
  let (raw, st) := closeBeamerScope cursor.state (closeDocumentBody pos result)
  cursor.complete (cursor.out.push raw, st)

private theorem rewriteCursor_last_document_exact (cursor : RewriteCursor)
    (body : Array Raw) (pos : Pos) (hp : cursor.outsidePicture)
    (hs : cursor.raws.toList.drop cursor.index = [.env "document" body pos]) :
    rewriteCursor cursor =
      closeLastDocument cursor pos
        (rewriteList cursor.inBody body #[] body.toList 0 0
          (openDocumentBody cursor.state).2) := by
  rw [rewriteCursor_document_exact cursor body pos [] hp hs]
  have ht : cursor.raws.toList.drop (cursor.index + 1) = [] := by
    rw [← List.drop_drop, hs]
    rfl
  simp only [rewriteCursor, RewriteCursor.enterDocument, List.drop_zero, ht,
    rewriteList, closeLastDocument]
  rfl

private theorem drop_control_rest (raws : Array Raw) (i : Nat)
    (name : String) (pos : Pos) (taken rest : List Raw)
    (h : raws.toList.drop i = .ctrl name pos :: (taken ++ rest)) :
    raws.toList.drop (i + 1 + taken.length) = rest := by
  rw [Nat.add_assoc, ← List.drop_drop, h, Nat.add_comm 1,
    List.drop_succ_cons, List.drop_left]

/-- Registered controls erase their operands at the production checkpoint,
including arbitrary nested raws in those operands. The result is the entire
remaining walk and its state, not just the control's replacement array. -/
private theorem rewriteCursor_control_exact (cursor : RewriteCursor)
    (name : String) (arity : Nat) (hc : ControlGroupsConsumed name arity)
    (pos : Pos) (args : List (Array Raw)) (taken rest : List Raw)
    (hd : cursor.inDocument)
    (hs : cursor.raws.toList.drop cursor.index = .ctrl name pos :: (taken ++ rest))
    (hn : args.length = arity)
    (hg : GroupPrefix cursor.raws (cursor.index + 1) args
      (cursor.index + 1 + taken.length)) :
    rewriteCursor cursor =
      rewriteCursor (cursor.afterControl name pos taken.length) := by
  obtain ⟨hd, hl, hp⟩ := hd
  have h := (hc cursor.inBody cursor.raws cursor.out pos args taken rest
    cursor.index cursor.state hd hl hp hs hn hg).2.1
  simpa only [rewriteCursor, RewriteCursor.afterControl,
    drop_control_rest _ _ _ _ _ _ hs] using congrArg cursor.complete h

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

private theorem flushRunning_quiet (st : St) (h : QuietTail st) :
    flushRunning st = (#[], st) := by
  simp only [flushRunning, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, h.1, h.2.1, Array.isEmpty_empty,
    Bool.false_eq_true, ↓reduceIte, Nat.not_lt.mpr h.2.2.1, decide_false,
    Bool.false_and]
  rfl

private theorem flushListLevels_quiet (st : St) (h : QuietTail st) :
    flushListLevels st = (#[], { st with writes := st.writes + 1 }) := by
  simp only [flushListLevels, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, h.2.2.2.1, h.2.2.2.2.1, state_array_forIn_empty, pure,
    Array.isEmpty_empty, ↓reduceIte]
  simp only [StateT.pure, write_eq]
  change (#[], { st with writes := st.writes + 1 }) =
    (#[], { st with listDefs := #[], listResets := #[], writes := st.writes + 1 })
  simp only [← h.2.2.2.1, ← h.2.2.2.2.1]

private theorem flushBeamerFootline_quiet (st : St) (h : QuietTail st) :
    flushBeamerFootline st = ((#[], #[]), st) := by
  simp only [flushBeamerFootline, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, h.2.2.2.2.2.2]
  rfl

/-- Split the raws of a replayed hook body across the seam
`\begin{document}` is: the native declarations the preamble reads
(`hookPreambleSide`, with their optional argument and complete groups) to the
preamble side, everything else to the body side. Both halves keep their
order.

The seam has two sides because LaTeX's own `\begin{document}` does: at that
instant a layout assignment and typeset text are both legal, and this engine
realizes the instant structurally — declarations before the `document`
environment, content inside it. Routing per raw is what lets one mechanism
serve a hook carrying configuration and a hook carrying content, which is
what real documents put in them. -/
private def seamSplit (raws : Array Raw) : List Raw → Nat → Nat →
    Array Raw × Array Raw → Array Raw × Array Raw
  | [], _, _, acc => acc
  | _ :: rest, i, skip + 1, acc => seamSplit raws rest (i + 1) skip acc
  | .ctrl name pos :: rest, i, 0, (pre, body) =>
    if hookPreambleSide.contains name then
      let (_, j) := takeOpt raws (i + 1)
      let (_, k) := takeGroups raws j (if name == "style" then 2 else 1)
      seamSplit raws rest (i + 1) (k - (i + 1))
        (pre ++ raws.extract i k, body)
    else
      seamSplit raws rest (i + 1) 0 (pre, body.push (.ctrl name pos))
  | r :: rest, i, 0, (pre, body) =>
    seamSplit raws rest (i + 1) 0 (pre, body.push r)

mutual

/-- Apply the preamble's completed block hook to parsed block environments,
including those inside macro definitions. The existing native spacer is
inserted after the mandatory title; missing titles retain their own error.
This pass runs only when a supported, nonempty hook was declared. -/
-- conserves: none — adds native spacing commands, without changing authored text.
private def blockHookRaw (spacing : Array Raw) : Raw → Raw
  | .group body p => .group (blockHookList spacing #[] body.toList) p
  | .env n body p =>
    let body := blockHookList spacing #[] body.toList
    let i := skipSpaces body 0
    let body := if n == "block" then
        match body[i]? with
        | some (.group _ _) =>
          body.extract 0 (i + 1) ++ spacing ++ body.extract (i + 1) body.size
        | _ => body
      else body
    .env n body p
  | .math d body p => .math d (blockHookList spacing #[] body.toList) p
  | .word s p => .word s p
  | .space => .space
  | .par p => .par p
  | .ctrl n p => .ctrl n p
  | .sym c p => .sym c p
  | .verb env s p => .verb env s p

private def blockHookList (spacing : Array Raw) (out : Array Raw) : List Raw → Array Raw
  | [] => out
  | r :: rest => blockHookList spacing (out.push (blockHookRaw spacing r)) rest

end

/-- The executed surface and the state its compatibility rewrite must
continue from. Keeping them together prevents a second execution of flags,
hooks or file effects while the driver resolves other document requests. -/
public structure Executed where
  raws : Array Raw
  private state : St

/-- Replace the already-executed surface after resolving data requests while
retaining its compatibility state and input receipts. -/
public def Executed.withRaws (executed : Executed) (raws : Array Raw) : Executed :=
  { executed with raws := raws }

/-- The original source index survives execution and included-file fulfilment. -/
public def Executed.sourceTriggers (executed : Executed) : SourceTriggers :=
  executed.state.sourceTriggers

/-- Exact reader receipts retained by the production evaluator. -/
public def Executed.inputAttempts (executed : Executed) : Array InputAttempt :=
  executed.state.inputAttempts

/-- Resolving other requests changes the surface alone. The original source
index and actual input-reader receipts remain available to the continuation. -/
public theorem Executed.withRaws_contract (executed : Executed) (raws : Array Raw) :
    (executed.withRaws raws).raws = raws ∧
      (executed.withRaws raws).sourceTriggers = executed.sourceTriggers ∧
      (executed.withRaws raws).inputAttempts = executed.inputAttempts := by
  exact ⟨rfl, rfl, rfl⟩

private def executionState (reading : Bool) (file : String) (raws : Array Raw)
    (provideKeeps : List String) (warned : Array String) (diags : Array Diag) : St :=
  { file := file, provideKeeps := provideKeeps, warned := warned, diags := diags
    sourceTriggers := sourceTriggers file {} raws.toList
    fileTop := reading, boundaryOpen := !boundaryRefused raws
    wholeDoc := raws.any (· matches .env "document" _ _), docFile := file }

private def executeBy [Monad m] (reader : Option (InputReader m))
    (file : String) (raws : Array Raw) (provideKeeps : List String)
    (warned : Array String) (inherited : List String) (diags : Array Diag) :
    m Executed := do
  let go : EvalM m (Array Raw) := do
    -- latex.ltx's \def\space{ }: expansion, copying and local redefinition
    -- share the ordinary meaning table, including the opening space scan.
    recordValue "space"
      (some { raws := #[.space], long := false, prot := false, live := true }) false
    -- A fragment's caller owns these meanings. Their text is unread here;
    -- local definitions can still replace them and scope restores them.
    for n in inherited do setBind n none
    condDocument reader raws
  let (raws, state) ← go.run
    (executionState reader.isSome file raws provideKeeps warned diags)
  return { raws := raws, state := state }

/-- Execute a file-free surface once, retaining the same source evidence as
the input-fulfilling path. Compatibility and elaboration can share it. -/
public def execute (file : String) (raws : Array Raw) (provideKeeps : List String := [])
    (warned : Array String := #[]) (inherited : List String := []) : Executed :=
  executeBy (m := Id) none file raws provideKeeps warned inherited #[]

/-- Execute the document with a driver that fulfils file requests at their
uses. All macro recursion retains its existing binding-order bound; the
driver owns the input stack and returns parsed fragments through
`resumeInput`. -/
public def executeInputs [Monad m] (reader : InputReader m) (file : String)
    (raws : Array Raw) (provideKeeps : List String := []) (diags : Array Diag := #[]) :
    m Executed :=
  executeBy (some reader) file raws provideKeeps #[] [] diags

private theorem executeInputs_condDocument_exact (reader : InputReader Id)
    (file : String) (raws : Array Raw) (keeps : List String) (ds : Array Diag) :
    executeInputs reader file raws keeps ds =
      let result := condDocument (some reader) raws
        (withSpaceBinding (executionState true file raws keeps #[] ds))
      { raws := result.1, state := result.2 } := by
  simp only [executeInputs, executeBy, Option.isSome_some, StateT.run,
    evalLift_id, bind, StateT.bind, recordValue_space_exact]
  rfl

private def packageInitialState (file command names : String) (pos gp np : Pos)
    (keeps : List String) (ds : Array Diag) : St :=
  withSpaceBinding (executionState true file (packageCall command names pos gp np) keeps #[] ds)

private def packageExecutedState (file command names : String) (pos gp np : Pos)
    (keeps : List String) (ds : Array Diag) : St :=
  let st := packageInitialState file command names pos gp np keeps ds
  { packageFailed command names pos gp np st with writes := st.writes + 10 }

private theorem executeInputs_package_failed_exact (reader : InputReader Id)
    (file command names : String) (pos gp np : Pos) (keeps : List String) (ds : Array Diag)
    (hc : command = "usepackage" ∨ command = "RequirePackage")
    (hr : ∀ request context, reader request context = (none, context)) :
    executeInputs reader file (packageCall command names pos gp np) keeps ds =
      { raws := packageCall command names pos gp np
        state := packageExecutedState file command names pos gp np keeps ds } := by
  have hn : command ≠ "space" := by rcases hc with rfl | rfl <;> decide
  have hv : condValueOf
      (packageInitialState file command names pos gp np keeps ds).binds command = none := by
    simp [packageInitialState, withSpaceBinding, executionState, condValueOf, Ne.symm hn]
  rw [executeInputs_condDocument_exact]
  have heq := condDocument_package_failed_exact reader command names pos gp np
    (packageInitialState file command names pos gp np keeps ds)
    hc rfl rfl rfl rfl rfl rfl hv hr
  change condDocument (some reader) (packageCall command names pos gp np)
    (withSpaceBinding (executionState true file
      (packageCall command names pos gp np) keeps #[] ds)) = _ at heq
  simp only [heq]
  rfl

private theorem pairGroupLevel_word_exact (names : String) (np : Pos) :
    pairGroupLevel #[.word names np] = #[.word names np] := by
  simp [pairGroupLevel]

private theorem overlayInputs_package_exact (command names : String) (pos gp np : Pos)
    (hc : command = "usepackage" ∨ command = "RequirePackage") :
    overlayInputs (packageCall command names pos gp np) =
      packageCall command names pos gp np := by
  have ha : overlayArity? command = none := by
    rcases hc with rfl | rfl <;>
      simp [overlayArity?, overlayName, String.startsWith_string_iff]
  simp [overlayInputs, packageCall, overlayInputsList, overlayInputsRaw,
    overlayVariant, overlayNext, overlayNext.advance, ha]

private theorem pairGroups_package_exact (command names : String) (pos gp np : Pos) :
    pairGroupsList true #[] (packageCall command names pos gp np).toList =
      packageCall command names pos gp np := by
  simp [packageCall, pairGroupsList, pairGroupsRaw, pairGroupLevel_word_exact]

private theorem delimDocument_package_exact (command names : String) (pos gp np : Pos)
    (hc : command = "usepackage" ∨ command = "RequirePackage") (st : St)
    (hd : st.deferred = #[]) :
    delimDocument (packageCall command names pos gp np) st =
      (packageCall command names pos gp np,
        { st with deferred := #[], writes := st.writes + 1 }) := by
  have hs : (packageCall command names pos gp np).findIdx?
      (· matches .env "document" _ _) = none := by simp [packageCall]
  have ht : (packageCall command names pos gp np).extract
      (packageCall command names pos gp np).size
      (packageCall command names pos gp np).size = #[] :=
    Array.extract_empty_of_stop_le_start (Nat.le_refl _)
  simp only [delimDocument, hs, Option.getD_none, Array.extract_size, ht]
  rcases hc with rfl | rfl <;>
    simp [packageCall, delimCallsList, delimCallsRaw, delimClose,
      redefiners, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      hd, write_eq, pure, StateT.pure]

private theorem splitColumns_package_exact (command names : String) (pos gp np : Pos) :
    (splitColumnsList (packageCall command names pos gp np).toList).toArray =
      packageCall command names pos gp np := by rfl

private theorem overprint_package_exact (command names : String) (pos gp np : Pos)
    (hc : command = "usepackage" ∨ command = "RequirePackage") (st : St) :
    overprintList (packageCall command names pos gp np).toList #[] 0 st =
      (packageCall command names pos gp np, st) := by
  have hn : command ≠ "apptocmd" := by rcases hc with rfl | rfl <;> decide
  simp [packageCall, overprintList, overprintRaw, hn, bind, StateT.bind,
    pure, StateT.pure]

/-- The production passes before the compatibility walk: overlay inputs,
live groups, delimiters, columns and overprints. Execution and file effects
have already happened and are not replayed when this cursor resumes. -/
public def beginRewrite (executed : Executed) : RewriteCursor :=
  let raws := overlayInputs executed.raws
  let go : M (Array Raw) := do
    -- After the conditionals: only a live pair is a group.
    let raws := pairGroupsList true #[] raws.toList
    let raws ← delimDocument raws
    let raws := (splitColumnsList raws.toList).toArray
    overprintList raws.toList #[] 0
  let st0 : St :=
    { executed.state with
      boundaryOpen := !boundaryRefused raws,
      wholeDoc := raws.any (· matches .env "document" _ _) }
  let (raws, st) := go.run st0
  { inBody := false, raws := raws, state := st }

private def packageRewriteState (st : St) (command names : String) (pos gp np : Pos) : St :=
  { st with
    boundaryOpen := !boundaryRefused (packageCall command names pos gp np)
    wholeDoc := false, deferred := #[], writes := st.writes + 1 }

private theorem beginRewrite_package_exact (command names : String) (pos gp np : Pos)
    (st : St) (hc : command = "usepackage" ∨ command = "RequirePackage")
    (hd : st.deferred = #[]) :
    beginRewrite { raws := packageCall command names pos gp np, state := st } =
      { inBody := false
        raws := packageCall command names pos gp np
        state := packageRewriteState st command names pos gp np } := by
  simp only [beginRewrite, overlayInputs_package_exact _ _ _ _ _ hc]
  have hw : (packageCall command names pos gp np).any
      (· matches .env "document" _ _) = false := by simp [packageCall]
  have hdelim := delimDocument_package_exact command names pos gp np hc
    { st with
      boundaryOpen := !boundaryRefused (packageCall command names pos gp np)
      wholeDoc := false } hd
  have hcols : splitColumnsList (packageCall command names pos gp np).toList =
      (packageCall command names pos gp np).toList := by rfl
  simp only [hw, StateT.run, bind, StateT.bind,
    pairGroups_package_exact, hdelim,
    hcols, overprint_package_exact _ _ _ _ _ hc,
    packageRewriteState]

/-- Interpret the gathered declarations and deferred bodies after row
lowering. This is the same final continuation for a whole document and a
resumed rewrite checkpoint. -/
private def finishDeclarations (out : Array Raw) : M (Array Raw) := do
  let running ← flushRunning
  let running := running ++ (← flushListLevels)
  let running ← rewriteList false running #[] running.toList 0 0
  -- Replay. Each body is rewritten as the preamble material it was
  -- declared as (`inDoc` restored to false for the pass), then routed
  -- across the seam by `seamSplit`. `endPreamble` bodies are all
  -- preamble side by their point's definition.
  let saved := (← get).inDoc
  let savedFile := (← get).file
  write fun st => { st with inDoc := false }
  let mut preSide : Array Raw := #[]
  let mut bodySide : Array Raw := #[]
  for (pt, file, pos, body) in (← get).deferred do
    write fun st => { st with file := file, seam := pt == .beginDocument }
    let body := overlayInputs body
    let body ← rewriteList false body #[] body.toList 0 0
    -- A hook declared inside an `\input`'ed file replays inside that
    -- file's wrapper, so what the engine refuses in it is still named at
    -- the file that wrote it — the wrapper is how a position names its
    -- file (a `Raw` carries only a line and a column).
    let wrap (rs : Array Raw) : Array Raw :=
      if rs.isEmpty || file == savedFile then rs
      else #[Raw.env (Parse.inputEnv file) rs pos]
    match pt with
    | .endPreamble => preSide := preSide ++ wrap body
    | .beginDocument =>
      let (p, b) := seamSplit body body.toList 0 0 (#[], #[])
      preSide := preSide ++ wrap p
      bodySide := bodySide ++ wrap b
  let (footerPre, footerBody) ← flushBeamerFootline
  preSide := preSide ++ footerPre
  let footerBody ← rewriteList false footerBody #[] footerBody.toList 0 0
  bodySide := footerBody ++ bodySide
  write fun st => { st with inDoc := saved, file := savedFile, seam := false }
  let counters := (← get).preCounters
  let isBody : Raw → Bool
    | .env "document" _ _ => true
    | _ => false
  return match out.findIdx? isBody with
    | some i =>
      let tail := match out[i]? with
        | some (.env n dbody p) =>
          #[Raw.env n (counters ++ bodySide ++ dbody) p]
        | some r => #[r]
        | none => #[]
      out.extract 0 i ++ running ++ preSide ++ tail ++ out.extract (i + 1) out.size
    | none => out ++ running ++ preSide ++ bodySide

private theorem finishDeclarations_diags (out : Array Raw) (st : St)
    (h : QuietTail st) :
    (finishDeclarations out st).2.diags = st.diags := by
  unfold finishDeclarations
  rw [state_bind_apply, flushRunning_quiet st h]
  dsimp only
  rw [state_bind_apply, flushListLevels_quiet st h]
  dsimp only
  simp only [Array.empty_append, Array.toList_empty, rewriteList]
  simp only [bind, StateT.bind, pure, StateT.pure, get, getThe,
    MonadStateOf.get, StateT.get, write_eq, h.2.2.2.2.2.1,
    state_array_forIn_empty, flushBeamerFootline]
  simp only [h.2.2.2.2.2.2, Array.empty_append]
  rfl

/-- State returned by the production tail. Keeping the record before its
output projection makes diagnostic preservation independent of the final
raw array's shape. -/
private def finishRewrittenState (result : Array Raw × St) : Array Raw × St :=
  let go : M (Array Raw) := do
    -- After the idiom rewrite, so a `\parbox` is the box it became.
    let out ← boxRowList #[] result.1.toList
    let out ← boxRowEmit out
    finishDeclarations out
  go.run result.2

/-- The production tail after the compatibility walk, shared by whole
documents and checkpoint completion. -/
private def finishRewritten (result : Array Raw × St) :
    Array Raw × Array Diag × Array String :=
  let (out, st) := finishRewrittenState result
  let out := if st.beamerBlockBegin.isEmpty then out
    else blockHookList st.beamerBlockBegin #[] out.toList
  (out, st.diags, st.warned)

attribute [local irreducible] boxRowList boxRowEmit finishDeclarations
  finishRewrittenState in
private theorem finishRewritten_named (result : Array Raw × St) (d : Diag)
    (h : TailDiag d result.2) : d ∈ (finishRewritten result).2.1 := by
  have hbox := boxRowList_tailDiag #[] result.1.toList d result.2 h
  have hemit := boxRowEmit_tailDiag (boxRowList #[] result.1.toList result.2).1
    d (boxRowList #[] result.1.toList result.2).2 hbox
  have hfinish := finishDeclarations_diags
    (boxRowEmit (boxRowList #[] result.1.toList result.2).1
      (boxRowList #[] result.1.toList result.2).2).1
    (boxRowEmit (boxRowList #[] result.1.toList result.2).1
      (boxRowList #[] result.1.toList result.2).2).2 hemit.1
  simp only [finishRewritten, finishRewrittenState, StateT.run, bind, StateT.bind]
  generalize hb : boxRowList #[] result.1.toList result.2 = boxed at *
  rcases boxed with ⟨out, st⟩
  generalize he : boxRowEmit out st = emitted at *
  rcases emitted with ⟨out', st'⟩
  dsimp only at hfinish hemit ⊢
  rw [he, hfinish]
  exact hemit.2

/-- Complete a production rewrite checkpoint, including boxes, running
content, deferred hooks, counters and block hooks. -/
public def finishRewrite (cursor : RewriteCursor) : Array Raw × Array Diag × Array String :=
  finishRewritten (rewriteCursor cursor)

/-- Finish the compatibility rewrite after execution and file fulfilment.
The gathered running content lands just before the document, and deferred
text is translated at its recorded seam without executing it again. -/
@[expose] public def rewriteExecuted (executed : Executed) : Array Raw × Array Diag × Array String :=
  finishRewrite (beginRewrite executed)

/-- Names for which the package dispatcher has no native, external-picture
or installed-theme interpretation. The condition is on the loading call's
operands, before execution or diagnostics. Empty comma fields do not name
files and are deliberately excluded. -/
@[expose] public def ExternalPackageNames (names : String) : Prop :=
  ∀ part ∈ names.trimAscii.toString.splitOn ",",
    part.trimAscii.toString.isEmpty = false ∧
    nativePackages.contains part.trimAscii.toString = false ∧
    boundaryPkgs.contains part.trimAscii.toString = false ∧
    themeSlotOfPackage? part.trimAscii.toString = none

attribute [local irreducible] finishRewritten in
/-- A failed reader answer to a live package declaration is both recorded
and named by the actual compatibility producer. This crosses execution,
the compatibility prepasses, command dispatch and declaration completion;
diagnostic membership is a conclusion, never a premise.

The domain is a live literal loading call, with arbitrary comma-separated
external names and source positions. Dormant definitions and calls inside
consumed control operands do not satisfy this execution domain. -/
public theorem executeInputs_package_refusal_contract (reader : InputReader Id)
    (file command names : String) (pos groupPos namePos : Pos)
    (keeps : List String) (ds : Array Diag)
    (hc : command = "usepackage" ∨ command = "RequirePackage")
    (hnames : ExternalPackageNames names)
    (hr : ∀ request context, reader request context = (none, context)) :
    let executed := executeInputs reader file
      (packageCall command names pos groupPos namePos) keeps ds
    executed.inputAttempts =
        #[⟨⟨command, file, pos, pos, #[.group #[.word names namePos] groupPos]⟩, false⟩] ∧
      ∀ part ∈ names.trimAscii.toString.splitOn ",",
        executed.sourceTriggers.attribute
          (packageRefusal file pos part.trimAscii.toString) ∈
            (rewriteExecuted executed).2.1 := by
  rw [executeInputs_package_failed_exact reader file command names pos groupPos namePos
    keeps ds hc hr]
  let initial := packageExecutedState file command names pos groupPos namePos keeps ds
  let st := packageRewriteState initial command names pos groupPos namePos
  constructor
  · rfl
  · intro part hpart
    have hn : ∀ p ∈ (names.trimAscii.toString.splitOn ",").map (·.trimAscii.toString),
        nativePackages.contains p = false := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact (hnames q hq).2.1
    have hb : ∀ p ∈ (names.trimAscii.toString.splitOn ",").map (·.trimAscii.toString),
        (boundaryPkgs.contains p && st.boundaryOpen) = false := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      simp only [(hnames q hq).2.2.1, Bool.false_and]
    have ht : ∀ p ∈ (names.trimAscii.toString.splitOn ",").map (·.trimAscii.toString),
        themeSlotOfPackage? p = none := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact (hnames q hq).2.2.2
    have hstep := rewriteList_package_external_exact command names pos groupPos namePos st
      hc rfl rfl rfl rfl rfl hn hb ht part hpart
    let reports := ((names.trimAscii.toString.splitOn ",").map fun p =>
      atSource st pos (packageRefusal st.file pos p.trimAscii.toString)).toArray
    let after := { st with diags := st.diags ++ reports }
    have hquiet : QuietTail after := by
      exact ⟨rfl, rfl, Nat.le_refl 1, rfl, rfl, rfl, rfl⟩
    have hmem : atSource st pos (packageRefusal st.file pos part.trimAscii.toString) ∈
        after.diags := by
      apply Array.mem_append.mpr
      apply Or.inr
      exact List.mem_toArray.mpr (List.mem_map.mpr ⟨part, hpart, rfl⟩)
    have hfinish := finishRewritten_named (#[], after)
      (atSource st pos (packageRefusal st.file pos part.trimAscii.toString)) ⟨hquiet, hmem⟩
    unfold rewriteExecuted finishRewrite
    rw [beginRewrite_package_exact command names pos groupPos namePos initial hc rfl]
    simp only [rewriteCursor, List.drop_zero, id_eq]
    rw [hstep]
    change st.sourceTriggers.attribute (packageRefusal st.file pos part.trimAscii.toString) ∈
      (finishRewritten (#[], after)).2.1
    rw [← atSource_package_exact st pos part.trimAscii.toString]
    exact hfinish

/-- The checkpoint and completion are the actual whole-document path. -/
public theorem rewriteExecuted_cursor_exact (executed : Executed) :
    rewriteExecuted executed = finishRewrite (beginRewrite executed) := by rfl

/-- Entering the actual document body preserves the whole compatibility
result, including its enclosing continuation and final diagnostics. -/
public theorem finishRewrite_document_exact (cursor : RewriteCursor)
    (body : Array Raw) (pos : Pos) (rest : List Raw)
    (hp : cursor.outsidePicture)
    (hs : cursor.raws.toList.drop cursor.index = .env "document" body pos :: rest) :
    finishRewrite cursor = finishRewrite (cursor.enterDocument body pos) :=
  congrArg finishRewritten (rewriteCursor_document_exact cursor body pos rest hp hs)

/-- Consumed groups cannot reach any later compatibility pass. The entire
completed result agrees with the continuation after the accounted dispatch,
including deferred material and the returned diagnostics. -/
public theorem finishRewrite_control_exact (cursor : RewriteCursor)
    (name : String) (arity : Nat) (hc : ControlGroupsConsumed name arity)
    (pos : Pos) (args : List (Array Raw)) (taken rest : List Raw)
    (hd : cursor.inDocument)
    (hs : cursor.raws.toList.drop cursor.index = .ctrl name pos :: (taken ++ rest))
    (hn : args.length = arity)
    (hg : GroupPrefix cursor.raws (cursor.index + 1) args
      (cursor.index + 1 + taken.length)) :
    finishRewrite cursor = finishRewrite (cursor.afterControl name pos taken.length) :=
  congrArg finishRewritten
    (rewriteCursor_control_exact cursor name arity hc pos args taken rest hd hs hn hg)

/-- Complete a consumed control's document using only the retained body
and its registered reporting effect. No operand or operand position is
read by this completion. The enclosing scope and deferred hooks still run. -/
public def finishMeaningFreeDocument (cursor : RewriteCursor) (name : String)
    (note : Option String) (pos docPos : Pos) (kept : Array Raw) :
    Array Raw × Array Diag × Array String :=
  finishRewritten (closeLastDocument cursor docPos
    (kept, meaningFreeState (openDocumentBody cursor.state).2 name pos note))

public def finishConfigSkipDocument (cursor : RewriteCursor) (name msg : String)
    (help : Option String) (pos docPos : Pos) (kept : Array Raw) :
    Array Raw × Array Diag × Array String :=
  finishRewritten (closeLastDocument cursor docPos
    (kept, configSkipState (openDocumentBody cursor.state).2 name pos msg help))

/-- The consumed operands cannot be read indirectly through the cursor's
source field either. The final-document completion reads only the saved
state, retained output prefix and enclosing continuation. -/
public theorem finishMeaningFreeDocument_source_exact (cursor : RewriteCursor)
    (body kept : Array Raw) (name : String) (note : Option String) (pos docPos : Pos) :
    finishMeaningFreeDocument (cursor.withDocument body docPos) name note pos docPos kept =
      finishMeaningFreeDocument cursor name note pos docPos kept := by rfl

public theorem finishConfigSkipDocument_source_exact (cursor : RewriteCursor)
    (body kept : Array Raw) (name msg : String) (help : Option String) (pos docPos : Pos) :
    finishConfigSkipDocument (cursor.withDocument body docPos) name msg help pos docPos kept =
      finishConfigSkipDocument cursor name msg help pos docPos kept := by rfl

/-- Exact completed document for every consuming row. The surrounding
literal material is arbitrary, as are the consumed groups and their nested
syntax. Execution has already run; this is the compatibility-to-elaboration
boundary. The complete result depends only on `pre ++ post` and the
descriptor's report, including every later hook and diagnostic. -/
public theorem finishRewrite_meaningFree_document_exact (cursor : RewriteCursor)
    (body : Array Raw) (name : String) (n : Nat) (note : Option String)
    (pos docPos : Pos) (pre taken post : List Raw) (args : List (Array Raw))
    (hm : (name, n, note) ∈ meaningFree)
    (hp : cursor.outsidePicture) (hl : cursor.outsideList)
    (hs : cursor.raws.toList.drop cursor.index = [.env "document" body docPos])
    (hb : body.toList = pre ++ .ctrl name pos :: (taken ++ post))
    (hpre : LiteralRaws pre) (hpost : LiteralRaws post) (hn : args.length = n)
    (hg : GroupPrefix body (pre.length + 1) args (pre.length + 1 + taken.length)) :
    finishRewrite cursor =
      finishMeaningFreeDocument cursor name note pos docPos (pre.toArray ++ post.toArray) := by
  unfold finishRewrite
  rw [rewriteCursor_last_document_exact cursor body docPos hp hs, hb]
  have hbody := rewriteList_meaningFree_body_exact cursor.inBody body #[] name n note
    pos pre taken post args 0 (openDocumentBody cursor.state).2 hm rfl hl hp
    hpre hpost hn (by simpa only [Nat.zero_add] using hg)
  rw [hbody]
  simp only [Array.empty_append, finishMeaningFreeDocument]

public theorem finishRewrite_configSkip_document_exact (cursor : RewriteCursor)
    (body : Array Raw) (name : String) (n : Nat) (msg : String) (help : Option String)
    (pos docPos : Pos) (pre taken post : List Raw) (args : List (Array Raw))
    (hm : (name, n, msg, help) ∈ configSkip)
    (hp : cursor.outsidePicture) (hl : cursor.outsideList)
    (hs : cursor.raws.toList.drop cursor.index = [.env "document" body docPos])
    (hb : body.toList = pre ++ .ctrl name pos :: (taken ++ post))
    (hpre : LiteralRaws pre) (hpost : LiteralRaws post) (hn : args.length = n)
    (hg : GroupPrefix body (pre.length + 1) args (pre.length + 1 + taken.length)) :
    finishRewrite cursor =
      finishConfigSkipDocument cursor name msg help pos docPos
        (pre.toArray ++ post.toArray) := by
  unfold finishRewrite
  rw [rewriteCursor_last_document_exact cursor body docPos hp hs, hb]
  have hbody := rewriteList_configSkip_body_exact cursor.inBody body #[] name n msg help
    pos pre taken post args 0 (openDocumentBody cursor.state).2 hm rfl hl hp
    hpre hpost hn (by simpa only [Nat.zero_add] using hg)
  rw [hbody]
  simp only [Array.empty_append, finishConfigSkipDocument]

/-- Rewrite a whole parsed document. The gathered running content lands just
before `\begin{document}`, where a declaration belongs.

`warned` in and out is the warn-once key set as data: a once-per-document
diagnostic is a promise about the DOCUMENT, not about whichever pass first
met a cause, and this pass and the elaborator both fire on some of the same
keys (`spec:overlay` is the one two arms share today — an unnumberable
overprint item here, an unnumberable `\alt` there). A set per pass makes the
promise per pass, which is how a deck spelling both got W0105 twice. The set
therefore travels with the document, out of here and into the state the
elaborator starts from, the way `Ir.overlayRange` became the one
numberability reader both passes ask: one notion of "already said", one
place it lives. It travels as a value the caller chains
(`Elab.runRawsSpanned`), never as ambient state.

`inherited` names are already defined by a fragment's caller. Their
replacement texts are unread here and remain for that caller to expand;
definitions inside the fragment still replace and restore them normally. -/
public def rewrite (file : String) (raws : Array Raw) (provideKeeps : List String := [])
    (warned : Array String := #[]) (inherited : List String := []) :
    Array Raw × Array Diag × Array String :=
  rewriteExecuted (execute file raws provideKeeps warned inherited)

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

/-- Diagnostic codes that carry a refused name, checked in both directions
by `nameRefusalRegistryChecks`. A code alone does not identify a file-loading
door: native `\theme` also emits W0319, and `ulem` options emit W0103.
The loading-call contract is `CompatContract.nameRefusals_asked`, over the
expanded call inspected by the input reader. -/
public def nameRefusalAsk : List (DiagCode × String) :=
  [(.W0103, ""), (.W0319, "beamertheme")]

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
  | .ctrl cn _ :: rest, i, 0 =>
    -- beamer's own file rule for the theme family (beamerbasethemes.sty:
    -- `\usetheme{n}` reads `beamerthemen.sty` from the input path, and so
    -- for each sub-theme slot): the prefixed name is the candidate a theme
    -- beside the document answers. A shipped bundle of the same name does
    -- not suppress the candidate — the two compose (`spliceTheme`).
    match themeAsking.lookup cn with
    | some pre =>
      let (_, j) := takeOpt raws (i + 1)
      let (args, k) := takeGroups raws j 1
      let nm := (rawSrc (args.getD 0 #[])).trimAscii.toString
      let out := if nm.isEmpty then out else
        let p := pre ++ nm
        if out.contains p then out else out.push p
      styCandList raws out rest (i + 1) (k - (i + 1))
    | none => styCandList raws out rest (i + 1) 0
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

/-- Style-file candidates from a source stream. The input reader calls this
on each expanded loading request's `call`; the original, unexpanded document
need not contain a macro-produced name. Native packages do not ask for files.
`CompatContract.nameRefusals_asked` states the loading-call contract, including
options, comma-separated package names, and every theme-family prefix. -/
public def localStyCandidates (raws : Array Raw) : Array String :=
  styCandList raws #[] raws.toList 0 0

private theorem packageStep_mem (out : Array String) (p nm : String) :
    nm ∈ (if p.isEmpty || nativePackages.contains p || out.contains p then out else out.push p) ↔
    nm ∈ out ∨ (p = nm ∧ nm.isEmpty = false ∧ nativePackages.contains nm = false) := by
  split
  · next h =>
    simp only [Bool.or_eq_true, Array.contains_iff_mem] at h
    constructor
    · exact Or.inl
    · rintro (hm | ⟨rfl, he, hn⟩)
      · exact hm
      · rcases h with ((h | h) | h)
        · simp_all
        · simp_all
        · exact h
  · next h =>
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
    rw [Array.mem_push]
    constructor
    · rintro (hm | rfl)
      · exact Or.inl hm
      · exact Or.inr ⟨rfl, h.1.1, h.1.2⟩
    · rintro (hm | ⟨rfl, _, _⟩)
      · exact Or.inl hm
      · exact Or.inr rfl

private theorem packageFold_mem (parts : List String) (out : Array String) (nm : String) :
    nm ∈ (parts.foldl (init := out) fun acc p =>
      let p := p.trimAscii.toString
      if p.isEmpty || nativePackages.contains p || acc.contains p then acc else acc.push p) ↔
    nm ∈ out ∨ ∃ p ∈ parts, p.trimAscii.toString = nm ∧
      nm.isEmpty = false ∧ nativePackages.contains nm = false := by
  induction parts generalizing out with
  | nil => simp
  | cons p rest ih =>
    simp only [List.foldl_cons, ih, packageStep_mem, List.mem_cons]
    constructor
    · rintro ((hm | hp) | ⟨q, hq, hn⟩)
      · exact Or.inl hm
      · exact Or.inr ⟨p, Or.inl rfl, hp⟩
      · exact Or.inr ⟨q, Or.inr hq, hn⟩
    · rintro (hm | ⟨q, (rfl | hq), hn⟩)
      · exact Or.inl (Or.inl hm)
      · exact Or.inl (Or.inr hn)
      · exact Or.inr ⟨q, hq, hn⟩

private theorem themeStep_monotone (out : Array String) (pre nm target : String)
    (hm : target ∈ out) :
    target ∈ (if nm.isEmpty then out else
      let p := pre ++ nm
      if out.contains p then out else out.push p) := by
  split
  · exact hm
  · dsimp only
    split
    · exact hm
    · exact Array.mem_push.mpr (Or.inl hm)

mutual
private theorem styCandList_monotone (raws : Array Raw) (out : Array String)
    (xs : List Raw) (i skip : Nat) (nm : String) (hm : nm ∈ out) :
    nm ∈ styCandList raws out xs i skip := by
  cases xs with
  | nil => exact hm
  | cons x xs =>
    cases skip with
    | succ skip =>
      rw [styCandList]
      exact styCandList_monotone raws out xs (i + 1) skip nm hm
    | zero =>
      cases x with
      | ctrl cn pos =>
        by_cases hup : cn = "usepackage"
        · subst cn
          rw [styCandList]
          apply styCandList_monotone
          exact (packageFold_mem _ out nm).mpr (Or.inl hm)
        · by_cases hrp : cn = "RequirePackage"
          · subst cn
            rw [styCandList]
            apply styCandList_monotone
            exact (packageFold_mem _ out nm).mpr (Or.inl hm)
          · rw [styCandList]
            case x_3 => exact fun h => hup h
            case x_4 => exact fun h => hrp h
            split
            · apply styCandList_monotone
              exact themeStep_monotone out _ _ nm hm
            · exact styCandList_monotone raws out xs (i + 1) 0 nm hm
      | word w pos | sym c pos | group body pos | math display body pos | env name body pos | verb name body pos | par pos | space =>
        rw [styCandList]
        · apply styCandList_monotone
          exact styCandRaw_monotone out _ nm hm
        all_goals simp
termination_by sizeOf xs

private theorem styCandRaw_monotone (out : Array String) (r : Raw) (nm : String)
    (hm : nm ∈ out) : nm ∈ styCandRaw out r := by
  cases r with
  | env name body pos =>
    simp only [styCandRaw]
    split
    · have hb : sizeOf body = 1 + sizeOf body.toList := by rfl
      exact styCandList_monotone body out body.toList 0 0 nm hm
    · exact hm
  | word w pos | ctrl cn pos | sym c pos | group body pos | math display body pos | verb name body pos | par pos | space => exact hm
termination_by sizeOf r
end

/-- Every nonempty, non-native package name read at this expanded loading
call remains a candidate after scanning arbitrary trailing input. -/
public theorem localStyCandidates_package_covers (cn : String) (pos : Pos)
    (tail : Array Raw) (nm : String)
    (hcn : cn = "usepackage" ∨ cn = "RequirePackage")
    (hname : ∃ p ∈ (rawSrc ((takeGroups (#[.ctrl cn pos] ++ tail)
        (takeOpt (#[.ctrl cn pos] ++ tail) 1).2 1).1.getD 0 #[])).splitOn ",",
      p.trimAscii.toString = nm)
    (hne : nm.isEmpty = false) (hnative : nativePackages.contains nm = false) :
    nm ∈ localStyCandidates (#[.ctrl cn pos] ++ tail) := by
  rcases hcn with rfl | rfl <;>
    simp only [localStyCandidates, Array.toList_append, List.singleton_append]
  all_goals
    rw [styCandList]
    apply styCandList_monotone
    apply (packageFold_mem _ _ nm).mpr
    obtain ⟨p, hp, hpn⟩ := hname
    exact Or.inr ⟨p, hp, hpn, hne, hnative⟩

/-- Every nonempty theme name read at this expanded loading call remains
its registry-prefixed candidate after scanning arbitrary trailing input. -/
public theorem localStyCandidates_theme_covers (cn pre : String) (pos : Pos)
    (tail : Array Raw) (nm : String)
    (hup : cn ≠ "usepackage") (hrp : cn ≠ "RequirePackage")
    (hpre : themeAsking.lookup cn = some pre)
    (hname : (rawSrc ((takeGroups (#[.ctrl cn pos] ++ tail)
      (takeOpt (#[.ctrl cn pos] ++ tail) 1).2 1).1.getD 0 #[])).trimAscii.toString = nm)
    (hne : nm.isEmpty = false) :
    pre ++ nm ∈ localStyCandidates (#[.ctrl cn pos] ++ tail) := by
  simp only [localStyCandidates, Array.toList_append, List.singleton_append]
  rw [styCandList]
  case x_3 => exact fun h => hup h
  case x_4 => exact fun h => hrp h
  simp only [hpre, Nat.zero_add, hname, hne, Bool.false_eq_true, ↓reduceIte,
    Array.contains_empty, Array.push_empty]
  apply styCandList_monotone
  simp

/-- One slot of the theme-loading family, read through the argument layer:
the scan's answer for a preamble holding only that command. The two
inequalities are the arms `styCandList` tries first (`\\usepackage` and
`\\RequirePackage` share an arm and read a comma list, not a prefixed
name), and they are what makes the registry arm the one that fires. -/
private theorem localSty_theme (cn pre nm : String) (pos : Pos)
    (hlk : themeAsking.lookup cn = some pre)
    (hne : nm.trimAscii.toString = nm) (hnz : nm ≠ "")
    (hup : cn ≠ "usepackage") (hrp : cn ≠ "RequirePackage") :
    localStyCandidates #[.ctrl cn pos, .group #[.word nm pos] pos] = #[pre ++ nm] := by
  have hne2 : nm.trimAscii.copy = nm := by simpa using hne
  have hnm : nm.isEmpty = false := by simpa using hnz
  have harg : (#[#[Raw.word nm pos]] : Array (Array Raw))[0]?.getD #[] = #[Raw.word nm pos] := by
    simp
  have hs : skipSpaces #[Raw.ctrl cn pos, Raw.group #[Raw.word nm pos] pos] 1 = 1 := by
    rw [skipSpaces]; simp
  have hopt : takeOpt #[Raw.ctrl cn pos, Raw.group #[Raw.word nm pos] pos] 1 = (none, 1) := by
    simp [takeOpt, takeRawOpt, hs, Id.run]
  have hgrp : takeGroups #[Raw.ctrl cn pos, Raw.group #[Raw.word nm pos] pos] 1 1
      = (#[#[Raw.word nm pos]], 2) := by
    simp [takeGroups, hs]
  have hsrc : rawSrc #[Raw.word nm pos] = nm := by
    simp [rawSrc, rawSrcList, rawSrcOne, hne2]
  simp only [localStyCandidates]
  rw [styCandList]
  case x_3 => exact fun h => absurd h hup
  case x_4 => exact fun h => absurd h hrp
  simp only [hlk, Nat.zero_add, hopt, hgrp, Array.getD_eq_getD_getElem?, harg, hsrc, hne, hnm,
    Bool.false_eq_true, ite_false, Array.contains_empty, Array.push_empty]
  rw [styCandList]
  rfl

/-- **Every slot of beamer's theme-loading family asks the input path for
exactly its prefixed file.** A preamble holding only that command yields
exactly that one candidate, so a theme file beside the document is opened
before the name can be refused — the invariant whose absence let
`\\usetheme{X}` be declared unknown with `beamerthemeX.sty` sitting
unopened next to the document, costing it its whole palette.

Quantified over the registry the candidate scan and the splice both read
(`themeAsking`), so adding a slot is entering the contract rather than
adding a case. `themeAskingChecks` keeps the rows as an executable floor
over the fixtures. -/
public theorem themeAsking_candidates (nm : String) (pos : Pos) (hne : nm.trimAscii.toString = nm)
    (hnz : nm ≠ "") :
    ∀ p ∈ themeAsking,
      localStyCandidates #[.ctrl p.1 pos, .group #[.word nm pos] pos]
        = #[p.2 ++ nm] := by
  intro p hp
  simp only [themeAsking, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  all_goals exact localSty_theme _ _ nm pos rfl hne hnz (by decide) (by decide)


/-- The option scheduler emits content and diagnostic requests in source
order. Requests must cross conditional selection with that content: reporting
while reading the file would warn about an unselected load.
`processed` also distinguishes a live, empty process from no process at all. -/
private inductive StyOptionStep where
  | raw (value : Raw)
  | processed (pos : Pos)
  | unhandled (option : String) (pos : Pos)
  deriving Repr, BEq

/-- One slot per declared name, in first-declaration order. Redeclaring a
name replaces its body without moving the slot (ltclass.dtx). `none` is a
spent handler; `some #[]` is a defined, empty handler and suppresses the
catch-all. `packageOptionChecks` observes both through repeated processing. -/
private def declareStyOption (declared : Array (String × Option (Array Raw)))
    (name : String) (body : Array Raw) : Array (String × Option (Array Raw)) :=
  if declared.any (·.1 == name) then
    declared.map fun (nm, old) => (nm, if nm == name then some body else old)
  else declared.push (name, some body)

private def styOptionBody (declared : Array (String × Option (Array Raw)))
    (name : String) : Option (Array Raw) :=
  (declared.find? (·.1 == name)).bind (·.2)

/-- Literal package option scheduling (ltclass.dtx):
`\\DeclareOption{name}{body}` binds a body; `\\DeclareOption*{body}` binds
the catch-all. `\\ExecuteOptions{list}` runs known bodies in list order,
without consuming them or invoking the catch-all. `\\ProcessOptions` runs
known names once in declaration order, then unknowns in caller order;
`\\ProcessOptions*` follows caller order, including duplicates. Processing
spends the named handlers. LuaLaTeX probes in `scripts/package-options.lean`
hold ordering, whitespace, empty items and handler lifetime to its kernel.

Bodies enter the existing compatibility passes unchanged: this is not a
TeX expansion runtime. The driver supplies direct and forwarded package
options; global class options are not available here. An unknown caller option
without a catch-all emits an explicit request, settled as W0110 only when
its site is live. `\\ProvidesPackage` and `\\NeedsTeXFormat` identify the
file and produce nothing. -/
private def resolveStyOptions (passed : List String) (raws : Array Raw) : Array StyOptionStep := Id.run do
  let mut out : Array StyOptionStep := #[]
  let mut declared : Array (String × Option (Array Raw)) := #[]
  let mut fallback : Option (Array Raw) := none
  let passed := passed.map (·.replace " " "")
  let mut i := 0
  for _ in [0:raws.size] do
    if h : i < raws.size then
      match raws[i] with
      | .ctrl "DeclareOption" _ =>
        let j := skipSpaces raws (i + 1)
        let k := skipStar raws j
        let starred := k != j
        let (args, k) := takeGroups raws k (if starred then 1 else 2)
        if starred then
          if h1 : args.size = 1 then fallback := some args[0]
        else if h2 : args.size = 2 then
          declared := declareStyOption declared (rawSrc args[0]) args[1]
        i := max k (i + 1)
      | .ctrl "ExecuteOptions" _ =>
        let (args, k) := takeGroups raws (i + 1) 1
        let opts := (rawSrc (args.getD 0 #[])).replace " " ""
        -- TeX's @for skips an empty list, but retains empty items in a
        -- nonempty list; an explicitly declared empty name can run here.
        unless opts.isEmpty do
          for nm in opts.splitOn "," do
            if let some body := styOptionBody declared nm then
              out := out ++ body.map StyOptionStep.raw
        i := max k (i + 1)
      | .ctrl "ProcessOptions" pos =>
        out := out.push (.processed pos)
        let j := skipSpaces raws (i + 1)
        let k := skipStar raws j
        if k == j then
          for (nm, body) in declared do
            unless nm.isEmpty do
              if passed.contains nm then
                out := out ++ (body.getD #[]).map StyOptionStep.raw
                declared := declareStyOption declared nm #[]
        -- ProcessOptions makes the empty-name handler empty before either
        -- pass. Known names consumed above stay defined and bypass fallback.
        for nm in passed do
          unless nm.isEmpty do
            match (styOptionBody declared nm).orElse (fun _ => fallback) with
            | some body => out := out ++ body.map StyOptionStep.raw
            | none => out := out.push (.unhandled nm pos)
        declared := declared.map fun (nm, _) => (nm, none)
        let k := skipSpaces raws k
        i := match raws[k]? with
          | some (.ctrl "relax" _) => k + 1
          | _ => k
      | .ctrl "ProvidesPackage" _ | .ctrl "NeedsTeXFormat" _ =>
        let (_, k) := takeGroups raws (i + 1) 1
        let (_, k2) := takeOpt raws k
        i := max k2 (i + 1)
      | r =>
        out := out.push (.raw r)
        i := i + 1
  return out

/-- Encode the scheduler's requests in the existing raw stream, without
re-parsing option text. The enclosing input wrapper supplies the style-file
span. Its first line names options left unprocessed at the end of the load,
even when `\endinput` or a false branch removes every process request. -/
private def spliceStyOptions (pkg : String) (passed : List String) (raws : Array Raw) :
    Array Raw := Id.run do
  let p : Pos := { line := 1, col := 1 }
  let names := passed.map (·.replace " " "") |>.filter (!·.isEmpty)
  let mut out : Array Raw := #[]
  unless names.isEmpty do
    out := #[.ctrl styOptionsLoadMark p, .group #[.word pkg p] p,
      .group (names.toArray.map fun nm => .word nm p) p]
  for step in resolveStyOptions passed raws do
    match step with
    | .raw r => out := out.push r
    | .processed pos => out := out.push (.ctrl styOptionsProcessedMark pos)
    | .unhandled nm pos =>
      out := out ++ #[.ctrl styOptionsUnhandledMark pos,
        .group #[.word pkg pos] pos, .group #[.word nm pos] pos]
  return out

/-- The shipped bundle a theme file stands on, as the raws that install it
before the file's own content. **Precedence is composition, not a contest**
(PLAN 2026-09-24): the bundle installs first and the file's declarations
land on top, so a role the file declares is the file's and a role it leaves
alone keeps the bundle's. One function because both splice paths owe the
same floor — a theme read under `\usetheme{X}` and the same theme read
under `\usepackage{beamerthemeX}` are one ask, and only the slot path had
it. Only the full-theme prefix carries a bundle: a token bundle is whole,
so no sub-theme slot installs one. -/
private def bundleFloor (pre nm : String) (pos : Pos) : Array Raw :=
  let nm := themeAlias nm
  if pre == "beamertheme" && (Theme.find? nm).isSome then
    #[.ctrl "theme" pos, .group #[.word nm pos] pos]
  else #[]

/-- Splice one admitted file. The driver reserves the package before
resuming this fragment, so a recursive require cannot splice it again.
Both package and theme spellings share the same option scheduler and
bundle floor; every declaration keeps its original execution order. -/
public def spliceLocalPackage (name : String) (passed : List String)
    (raws : Array Raw) (pos : Pos) : Array Raw :=
  let floor := match themeSlotOfPackage? name with
    | some (_, pre, nm) => bundleFloor pre nm pos
    | none => #[]
  floor.push (.env (Parse.inputEnv (name ++ ".sty")) (spliceStyOptions name passed raws) pos)

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
  let passed := PackageImports.literalOptions (opt.getD "")
  let mut keep : Array String := #[]
  let mut splice : Array Raw := #[]
  let mut recs : Array (String × Option String × Pos) := #[]
  for p in pkgs do
    match stys.find? (·.1 == p) with
    | some (_, sraws) =>
      splice := splice ++ spliceLocalPackage p passed sraws pos
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

/-- The replacement for one member of the theme family at `i`: the theme
file's input fragment when the prefixed file was read (beamer's own file
rule — `\\usetheme{X}` reads `beamerthemeX.sty`), `none` otherwise, leaving
the command to its existing arm. Options ride into the file's own option
machinery, as `\\usepackage[opts]{}` does, because that is what beamer's
family expands to.

**Where the engine also ships a bundle of that name, the two compose**: the
bundle installs first and the file's declarations land on top, so a role the
file declares is the file's and a role it leaves alone keeps the bundle's.
Neither extreme is right on its own. Reading only the bundle would drop the
author's deliberate edit to a theme sitting in their own directory. Reading
only the file would trade a complete, contrast-proved design
(`Contrast.builtin_designs_legible` ranges over `Theme.builtin` and over
nothing a `.sty` can add) for the fragments of it this engine can absorb —
and since dropping the native `\\theme` also drops `sawTheme`, a deck would
then fall to the *default* bundle plus fragments, which is further from the
author's ask than the bundle they named. Composition is the engine's own
rule for a `\\theme` followed by `\\palette`, so nothing new is invented and
nothing is silently ignored: `styRead` names both sides. -/
private def spliceTheme (stys : Array (String × Array Raw)) (raws : Array Raw)
    (pre : String) (pos : Pos) (i : Nat) :
    Option (Array Raw × Array (String × Option String × Pos) × Nat) := Id.run do
  if stys.isEmpty then return none
  let (opt, j) := takeOpt raws (i + 1)
  let (args, k) := takeGroups raws j 1
  if args.isEmpty then return none
  let nm := (rawSrc (args.getD 0 #[])).trimAscii.toString
  let p := pre ++ nm
  match stys.find? (·.1 == p) with
  | some (_, sraws) =>
    let passed := PackageImports.literalOptions (opt.getD "")
    return some (spliceLocalPackage p passed sraws pos,
      #[(p ++ ".sty", none, pos)], k)
  | none => return none

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
      match themeAsking.lookup cn with
      | some pre =>
        match spliceTheme stys raws pre pos i with
        | some (repl, rs, k) =>
          applyStyList stys raws (out ++ repl) (recs ++ rs) rest (i + 1) (k - (i + 1))
        | none => applyStyList stys raws (out.push (.ctrl cn pos)) recs rest (i + 1) 0
      | none =>
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
public def applyLocalSty (raws : Array Raw) (stys : Array (String × Array Raw)) :
    Array Raw × Array (String × Option String × Pos) :=
  applyStyList stys raws #[] #[] raws.toList 0 0

private theorem spliceUse_empty (raws : Array Raw) (cn : String) (pos : Pos) (i : Nat) :
    spliceUse #[] raws cn pos i = none := by rfl

private theorem spliceTheme_empty (raws : Array Raw) (pre : String) (pos : Pos) (i : Nat) :
    spliceTheme #[] raws pre pos i = none := by rfl

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
      · split
        · rw [spliceTheme_empty]
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
public theorem applyLocalSty_id (raws : Array Raw) : applyLocalSty raws #[] = (raws, #[]) := by
  rw [applyLocalSty, applyStyList_empty]
  simp

/-- What a spliced `.sty` yielded, counted after elaboration: a construct
was honoured when its translation note (N0100) carries the file, named
when a warning does, and a TeX internal refused when a demoted refusal
does — a note that kept its W0301/W0357/W0391 code is the demotion's
signature, and at this point in the run nothing else makes one (`\allow`
acceptance resolves later, in the driver). -/
public def styCounts (sty : String) (diags : Array Diag) : Nat × Nat × Nat :=
  let mine := diags.filter fun d => d.span.any (·.file == sty)
  ((mine.filter (·.code == "N0100")).size,
   (mine.filter (·.severity == .warning)).size,
   (mine.filter fun d =>
     d.severity == .note &&
       (d.code == "W0301" || d.code == "W0357" || d.code == "W0391")).size)

/-- The one N0020 construction — the note that says the file was looked
at, and how much of it took. Built after elaboration, from the splice
records `applyLocalSty` returns: the counts do not exist before it. The
spelling is compact — three counts and a long file name must fit the
message-length lint.

A theme file that shadows a shipped bundle says so instead: the two compose
(`spliceTheme`), and a note that named only one of them would leave the
other silent. -/
public def styRead (docFile sty : String) (pos : Pos) (diags : Array Diag) : Diag :=
  let (honoured, named, refused) := styCounts sty diags
  let counts := s!"honoured: {honoured}, named: {named}, TeX internals refused: {refused}"
  let over := if sty.startsWith "beamertheme" && sty.endsWith ".sty" then
      let nm := (sty.drop "beamertheme".length).dropEnd ".sty".length
      if (Theme.find? nm.toString).isSome then some nm.toString else none
    else none
  let lead := match over with
    | some nm => s!"'{sty}' overrides the {nm} bundle"
    | none => s!"'{sty}' beside the document is read into the preamble"
  Diag.of .N0020 (lead ++ " — " ++ counts) (some ⟨docFile, pos⟩)

/-! # listings and siunitx (pkg-text's section)

A second rewrite pass, run by `Elab.runRaws` right after `rewrite`: it
lives at the file's end, in its own section, so the arms elsewhere in
this file rebase clean around it.

`\lstset{keys}` is listings' stateful configuration: the accepted entries
travel into the option head of every following `{lstlisting}` capture,
where the elaborator judges each key once (`Elab.listingBlock`) — one
validation site, the environment's own keys overriding `\lstset`'s
(listings' precedence; later entries win at elaboration, so the
environment's stand last).

The siunitx commands (`\num`, `\SI`/`\qty`, `\si`/`\unit`, `\ang`,
`\numrange`/`\qtyrange`) spell their text natively: digit grouping and
the decimal marker from the locale record, `e` exponents as ×10ⁿ with
real superscript glyphs, unit symbols from the table below. A name a
document `\define`s itself is left alone — the definition wins, as it
does at elaboration. -/

/-- The unit symbols, transcribed from siunitx's own declarations
(`\siunitx_declare_unit:Nn`, siunitx.sty v3 — the implementation of the
manual's unit tables: SI base and derived units, and the accepted
non-SI units). Ω is spelled U+03A9: the input path NFC-normalizes, so
one spelling reaches the fonts. `\kilogram` and `\decibel` carry their
composed symbols. -/
private def siUnits : List (String × String) :=
  [("kilogram", "kg"), ("metre", "m"), ("meter", "m"), ("mole", "mol"),
   ("second", "s"), ("ampere", "A"), ("kelvin", "K"), ("candela", "cd"),
   ("gram", "g"),
   ("becquerel", "Bq"), ("degreeCelsius", "°C"), ("coulomb", "C"),
   ("farad", "F"), ("gray", "Gy"), ("hertz", "Hz"), ("henry", "H"),
   ("joule", "J"), ("katal", "kat"), ("lumen", "lm"), ("lux", "lx"),
   ("newton", "N"), ("ohm", "Ω"), ("pascal", "Pa"), ("radian", "rad"),
   ("siemens", "S"), ("sievert", "Sv"), ("steradian", "sr"),
   ("tesla", "T"), ("volt", "V"), ("watt", "W"), ("weber", "Wb"),
   ("astronomicalunit", "au"), ("bel", "B"), ("decibel", "dB"),
   ("dalton", "Da"), ("day", "d"), ("electronvolt", "eV"),
   ("hectare", "ha"), ("hour", "h"), ("litre", "L"), ("liter", "L"),
   ("minute", "min"), ("neper", "Np"), ("tonne", "t"),
   ("arcminute", "\u02B9"), ("arcsecond", "\u02BA"), ("degree", "°"),
   ("percent", "%")]

/-- The SI prefixes, from the same declarations
(`\siunitx_declare_prefix:Nnn`, siunitx.sty v3): quecto through quetta.
µ is U+03BC, siunitx's own scalar for `\micro`. -/
private def siPrefixes : List (String × String) :=
  [("quecto", "q"), ("ronto", "r"), ("yocto", "y"), ("zepto", "z"),
   ("atto", "a"), ("femto", "f"), ("pico", "p"), ("nano", "n"),
   ("micro", "\u03BC"), ("milli", "m"), ("centi", "c"), ("deci", "d"),
   ("deca", "da"), ("deka", "da"), ("hecto", "h"), ("kilo", "k"),
   ("mega", "M"), ("giga", "G"), ("tera", "T"), ("peta", "P"),
   ("exa", "E"), ("zetta", "Z"), ("yotta", "Y"), ("ronna", "R"),
   ("quetta", "Q")]

/-- A real superscript glyph per digit (U+2070–U+2079, with ¹²³ at their
Latin-1 points) and the superscript minus U+207B: what exponents and
unit powers render with. -/
private def supChar : Char → Char
  | '0' => '⁰' | '1' => '¹' | '2' => '²' | '3' => '³' | '4' => '⁴'
  | '5' => '⁵' | '6' => '⁶' | '7' => '⁷' | '8' => '⁸' | '9' => '⁹'
  | '-' => '⁻' | c => c

private def toSup (s : String) : String :=
  String.ofList (s.toList.map supChar)

/-- Group a digit run in threes with the locale's separator, only when it
carries five or more digits — siunitx's own thresholds
(`group-minimum-digits = 5`, `group-digits = all`). `fromRight` is the
integer part's direction; a fraction part groups from the left. -/
private def groupDigits (loc : Locale) (ds : String) (fromRight : Bool) : String :=
  if ds.length < 5 then ds else Id.run do
    let cs := if fromRight then ds.toList.reverse else ds.toList
    let mut out : List Char := []
    let mut n := 0
    for c in cs do
      if n > 0 && n % 3 == 0 then
        out := loc.group.toList.reverse ++ out
      out := c :: out
      n := n + 1
    return String.ofList (if fromRight then out else out.reverse)

/-- `\num`'s output for one plain number
`[+-]digits[.digits][e[+-]digits]` (a `,` reads as the input decimal
marker, as siunitx accepts): grouped digits, the locale's decimal marker,
and the exponent as ×10ⁿ — `exponent-product`'s × between real
superscript digits, `10ⁿ` alone when no significand stands before the
`e`. Input outside that shape is kept exactly as written: a form the
formatter cannot read must never be silently reshaped. -/
private def fmtNum (loc : Locale) (src0 : String) : String := Id.run do
  let src := String.ofList (src0.toList.filter (· != ' '))
  let (mant, expPart) := match src.splitOn "e" with
    | [m] =>
      (match m.splitOn "E" with
        | [m1] => (m1, none)
        | [m1, e1] => (m1, some e1)
        | _ => ("", none))
    | [m, e] => (m, some e)
    | _ => ("", none)
  -- validate and split the significand
  let (sign, rest) :=
    if mant.startsWith "-" then ("\u2212", (mant.drop 1).toString)
    else if mant.startsWith "+" then ("", (mant.drop 1).toString)
    else ("", mant)
  let parts := (rest.replace "," ".").splitOn "."
  let ok (s : String) := s.toList.all (·.isDigit)
  let mantOut : Option String := match parts with
    | [i] => if ok i && !i.isEmpty then some (sign ++ groupDigits loc i true) else
        if i.isEmpty && sign.isEmpty then some "" else none
    | [i, f] => if ok i && ok f && !(i.isEmpty && f.isEmpty) then
        some (sign ++ groupDigits loc i true ++ loc.decimal ++ groupDigits loc f false)
      else none
    | _ => none
  let expOut : Option (Option String) := match expPart with
    | none => some none
    | some e =>
      let e := if e.startsWith "+" then (e.drop 1).toString else e
      let (es, ed) := if e.startsWith "-" then ("-", (e.drop 1).toString) else ("", e)
      if ok ed && !ed.isEmpty then
        let ed := String.ofList (ed.toList.dropWhile (· == '0'))
        some (some (es ++ (if ed.isEmpty then "0" else ed)))
      else none
  match mantOut, expOut with
  | some m, some none => if m.isEmpty then src0 else m
  | some m, some (some e) =>
    let es := toSup e
    if m.isEmpty then "10" ++ es
    else m ++ "\u2009×\u200910" ++ es
  | _, _ => src0

mutual

/-- The group-flatten a unit argument needs: `{\kilo\metre}` and bare
`\kilo\metre` read the same. -/
-- conserves: none — a projection to the atoms a unit expression reads.
private def unitAtoms (out : Array Raw) : List Raw → Array Raw
  | [] => out
  | r :: rest => unitAtoms (unitAtomOne out r) rest

private def unitAtomOne (out : Array Raw) : Raw → Array Raw
  | .group b _ => unitAtoms out b.toList
  | r => out.push r

end

/-- One unit group's symbols. Prefixes glue to the unit they precede;
`\per` negates the next unit's power, `\square`/`\cubic` set it and
`\squared`/`\cubed` multiply the one before (siunitx's power syntax,
default `per-mode = power`: m s⁻¹, never a slash); factors join by thin
space. Literal text in the group is kept as written. A name outside the
table is W0381, set as its ASCII spelling — degraded, never silent. -/
private def fmtUnit (body : Array Raw) (pos : Pos) : M String := do
  let atoms := unitAtoms #[] body.toList
  let mut factors : Array (String × Int) := #[]
  let mut pre := ""
  let mut nextPow : Int := 1
  let mut perNext := false
  for r in atoms do
    match r with
    | .ctrl n _ =>
      if let some g := siPrefixes.lookup n then
        pre := pre ++ g
      else if n == "per" then
        perNext := true
      else if n == "square" then
        nextPow := 2
      else if n == "cubic" then
        nextPow := 3
      else if n == "squared" || n == "cubed" then
        let k : Int := if n == "squared" then 2 else 3
        match factors.back? with
        | some (g, p) => factors := factors.pop.push (g, p * k)
        | none => pure ()
      else
        let g ← match siUnits.lookup n with
          | some g => pure g
          | none => do
            say .W0381 s!"no unit symbol for '\\{n}'; set as its ASCII spelling" pos
              (help := "write the symbol as literal text in the unit braces: \
\\qty{1}{kPa}")
            pure n
        factors := factors.push (pre ++ g, nextPow * (if perNext then -1 else 1))
        pre := ""
        nextPow := 1
        perNext := false
    | .word w _ => factors := factors.push (w, 1)
    | .sym c _ => factors := factors.push (String.ofList [c], 1)
    | _ => pure ()
  return String.intercalate "\u2009"
    ((factors.map fun (g, p) =>
      g ++ (if p == 1 then "" else toSup (toString p))).toList)

/-- `\ang`'s degrees, arcminutes, arcseconds: the `;`-separated parts each
take the angle symbols siunitx sets (`\degree`, `\arcminute`,
`\arcsecond` — °, U+02B9, U+02BA). -/
private def fmtAng (loc : Locale) (src : String) : String := Id.run do
  let parts := src.splitOn ";"
  let marks := ["°", "\u02B9", "\u02BA"]
  let mut out := ""
  let mut i := 0
  for p in parts do
    let p := p.trimAscii.toString
    unless p.isEmpty do
      out := out ++ fmtNum loc p ++ (marks[i]?.getD "")
    i := i + 1
  return out

/-- The state the text pass threads in flow order. -/
private structure TextSt where
  /-- `\lstset` entries standing, injected ahead of every following
  listing's own option head. -/
  lstOpts : Array String := #[]
  /-- Minted's global and exact-lexer defaults are separate layers:
  language defaults override even a later global declaration. -/
  mintedOpts : Array String := #[]
  mintedLangOpts : Array (String × Array String) := #[]
  /-- Names the document defines; a defined `\num` is the document's. -/
  defined : Array String := #[]

/-- Standing entries precede the environment's own options, which win.
Appending declarations within a layer updates keys individually. -/
private def injectListingOpts (opts : Array String) (s : String) : String :=
  if opts.isEmpty then s else
  let joined := String.intercalate "," opts.toList
  match Parse.listingOptHead s with
  | some (o, past) => "[" ++ joined ++ "," ++ o ++ "]" ++ (s.drop past).toString
  | none => "[" ++ joined ++ "]" ++ s

/-- One siunitx command's replacement: the text raws standing in its
place and the index past its arguments. Number and unit join by
U+202F, a no-break thin space — siunitx's `quantity-product = \,` —
inside one word, so a quantity never breaks across lines. A range takes
siunitx's own default phrase (`range-phrase`, " to "), units repeated on
both ends (`range-units = repeat`). Options on a command are named
W0110, never silently dropped. -/
private def siCtrl (loc : Locale) (n : String) (pos : Pos) (raws : Array Raw)
    (start : Nat) : M (Array Raw × Nat) := do
  sayOnce ("si:" ++ n) .N0100
    s!"'\\{n}' spells its text natively: locale digits and unit symbols (siunitx)" pos
  let (opt, j) := takeOpt raws start
  if opt.isSome then
    say .W0110 s!"'\\{n}' options are not honoured; ignored" pos
  let word (s : String) : Raw := .word s pos
  match n with
  | "num" =>
    let (args, k) := takeGroups raws j 1
    return (#[word (fmtNum loc (rawSrc (args.getD 0 #[])))], k)
  | "ang" =>
    let (args, k) := takeGroups raws j 1
    return (#[word (fmtAng loc (rawSrc (args.getD 0 #[])))], k)
  | "si" | "unit" =>
    let (args, k) := takeGroups raws j 1
    return (#[word (← fmtUnit (args.getD 0 #[]) pos)], k)
  | "SI" | "qty" =>
    let (args, k) := takeGroups raws j 2
    let num := fmtNum loc (rawSrc (args.getD 0 #[]))
    let u ← fmtUnit (args.getD 1 #[]) pos
    return (#[word (num ++ "\u202F" ++ u)], k)
  | "numrange" =>
    let (args, k) := takeGroups raws j 2
    return (#[word (fmtNum loc (rawSrc (args.getD 0 #[]))), .space, word "to",
      .space, word (fmtNum loc (rawSrc (args.getD 1 #[])))], k)
  | "qtyrange" | "SIrange" =>
    let (args, k) := takeGroups raws j 3
    let u ← fmtUnit (args.getD 2 #[]) pos
    return (#[word (fmtNum loc (rawSrc (args.getD 0 #[])) ++ "\u202F" ++ u),
      .space, word "to", .space,
      word (fmtNum loc (rawSrc (args.getD 1 #[])) ++ "\u202F" ++ u)], k)
  | _ => return (#[], j)

/-- The siunitx command names this pass answers. -/
private def siCtrls : List String :=
  ["num", "ang", "si", "unit", "SI", "qty", "numrange", "qtyrange", "SIrange"]

mutual

/-- The listings/siunitx pass, `rewriteList`'s shape with the flow state
threaded: the list drives the recursion, the array gives argument access,
`skip` counts elements a replacement consumed. -/
-- conserves: none — the rewrite spells siunitx constructs as their output
-- text and consumes listing defaults into following option heads.
private def textList (loc : Locale) (st : TextSt) (raws : Array Raw)
    (out : Array Raw) : List Raw → Nat → Nat → M (Array Raw × TextSt)
  | [], _, _ => return (out, st)
  | _ :: rest, i, skip + 1 => textList loc st raws out rest (i + 1) skip
  | .ctrl n pos :: rest, i, 0 => do
    if n == "define" then
      -- The definition wins: its name is the document's from here on.
      let j := skipSpaces raws (i + 1)
      let st := match raws[j]?.bind boundName with
        | some b => { st with defined := st.defined.push b }
        | none => st
      textList loc st raws (out.push (.ctrl n pos)) rest (i + 1) 0
    else if (n == "lstset" || n == "setminted") && !st.defined.contains n then
      let (lang, j) := if n == "setminted" then takeOpt raws (i + 1)
        else (none, i + 1)
      let (args, k) := takeGroups raws j 1
      let entries := (Decl.splitEntries (rawSrc (args.getD 0 #[]))).filterMap
        fun e => let e := e.trimAscii.toString
          if e.isEmpty then none else some e
      let entries := entries.toArray
      let st := if n == "lstset" then
          { st with lstOpts := st.lstOpts ++ entries }
        else match lang with
          | none => { st with mintedOpts := st.mintedOpts ++ entries }
          | some lang =>
            let lang := lang.trimAscii.toString
            let old := ((st.mintedLangOpts.find? (·.1 == lang)).map (·.2)).getD #[]
            { st with mintedLangOpts :=
              (st.mintedLangOpts.filter (·.1 != lang)).push (lang, old ++ entries) }
      textList loc st raws out rest (i + 1) (k - (i + 1))
    else if siCtrls.contains n && !st.defined.contains n then
      let (repl, k) ← siCtrl loc n pos raws (i + 1)
      textList loc st raws (out ++ repl) rest (i + 1) (k - (i + 1))
    else
      textList loc st raws (out.push (.ctrl n pos)) rest (i + 1) 0
  | .verb env s vpos :: rest, i, 0 =>
    let s := if env == "lstlisting" then injectListingOpts st.lstOpts s
      else if env == "minted" then
        let afterOpt := ((Parse.listingOptHead s).map (·.2)).getD 0
        let lang := ((Parse.mintedLangHead s afterOpt).map (·.1.trimAscii.toString)).getD ""
        let opts := ((st.mintedLangOpts.find? (·.1 == lang)).map (·.2)).getD #[]
        injectListingOpts (st.mintedOpts ++ opts) s
      else s
    textList loc st raws (out.push (.verb env s vpos)) rest (i + 1) 0
  | r :: rest, i, 0 => do
    let (r, st) ← textRaw loc st r
    textList loc st raws (out.push r) rest (i + 1) 0

/-- Listing defaults are TeX-local to groups and environments. An input
wrapper is transparent: input does not open a TeX group. This matches
LuaLaTeX's synthetic minted/listings probe (`mintedSettingsChecks`). -/
private def textRaw (loc : Locale) (st : TextSt) : Raw → M (Raw × TextSt)
  | .group body p => do
    let (body, inner) ← textList loc st body #[] body.toList 0 0
    return (.group body p, { st with defined := inner.defined })
  | .env n body p => do
    if let some file := Parse.inputEnvFile? n then
      let savedFile := (← get).file
      write fun s => { s with file := file }
      let (body, inner) ← textList loc st body #[] body.toList 0 0
      write fun s => { s with file := savedFile }
      return (.env n body p, inner)
    let (body, inner) ← textList loc st body #[] body.toList 0 0
    return (.env n body p, { st with defined := inner.defined })
  | r => return (r, st)

end

mutual

/-- The document's declared language tag, for the number spellings: the
`\pdfmeta{ language = "…" }` the babel arm rewrites to (or a document
declares itself), found wherever it stands. -/
private def declaredTagList : List Raw → Option String
  | [] => none
  | .ctrl "pdfmeta" _ :: rest =>
    match (rest.dropWhile (· matches .space)).head? with
    | some (.group g _) =>
      match (Decl.splitEntries (rawSrc g)).findSome? (fun e =>
          match Decl.splitEntry e with
          | some ("language", v) =>
            some (((v.replace "\"" "").trimAscii).toString)
          | _ => none) with
      | some tag => some tag
      | none => declaredTagList rest
    | _ => declaredTagList rest
  | r :: rest =>
    match declaredTagOne r with
    | some t => some t
    | none => declaredTagList rest

private def declaredTagOne : Raw → Option String
  | .env _ body _ => declaredTagList body.toList
  | _ => none

end

mutual

/-- Whether the pass has anything to do: listing defaults or a siunitx command
anywhere. A read-only scan, so the common document — which has neither —
never pays for the rebuilding walk (`scripts/bench.lean` is the check). -/
private def textNeededList : List Raw → Bool
  | [] => false
  | .ctrl n _ :: rest =>
    n == "lstset" || n == "setminted" || siCtrls.contains n || textNeededList rest
  | r :: rest => textNeededOne r || textNeededList rest

private def textNeededOne : Raw → Bool
  | .group b _ => textNeededList b.toList
  | .env _ b _ => textNeededList b.toList
  | _ => false

end

/-- The listings/siunitx pass, run right after `rewrite`: `\lstset` and
`\setminted` fold into the listings that follow, and siunitx commands become their
spelled text under the document's own locale. Third in the document's
warn-once chain (`rewrite`'s docstring carries why the set travels): the
keys it receives are the ones `rewrite` fired, the keys it returns go on to
the elaborator. -/
public def rewriteText (file : String) (raws : Array Raw) (warned : Array String := #[]) :
    Array Raw × Array Diag × Array String :=
  if !textNeededList raws.toList then (raws, #[], warned) else
  let loc := ((declaredTagList raws.toList).bind Locale.forTag).getD Locale.en
  let go : M (Array Raw) := do
    let (out, _) ← textList loc {} raws #[] raws.toList 0 0
    return out
  let (out, st) := go.run
    { file := file, warned := warned, sourceTriggers := sourceTriggers file {} raws.toList }
  (out, st.diags, st.warned)

end LeanTex.Core.Compat
