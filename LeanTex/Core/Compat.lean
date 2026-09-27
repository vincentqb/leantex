import LeanTex.Core.Lex
import LeanTex.Core.Parse
import LeanTex.Core.Theme
import LeanTex.Core.Decl
import LeanTex.Core.Ir
import LeanTex.Core.TitleTemplate
import LeanTex.Core.BibStyle

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
E0333 names each shape outside it; `appendix`'s mark and its environment
are the sectioning walk's own, and its contents-page apparatus is W0301
where it stands, as `\nicefrac` and `\multirow` are when
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
   "caption", "subcaption", "nicefrac", "multirow", "crop",
   "appendixnumberbeamer", "natbib",
   "times", "mathptmx", "palatino", "mathpazo", "helvet", "courier",
   "libertine", "carlito", "xspace", "float", "biblatex", "appendix",
   "cleveref", "listings", "minted", "siunitx",
   "algorithm2e", "algorithmicx", "algpseudocode", "algorithm", "lineno", "environ", "amsthm"]

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
placements are one bar — moloch itself derives its two placement variants
from `progress bar` with `parent=`, so the collapse is the inheritance it
declares — and `footline` and `page number in head/foot` are the one footer
ink. `background canvas` has a ground and no ink: beamer's default canvas
template reads only its `bg`, painting it as a full-page rule
(beamerouterthemedefault.sty, `\defbeamertemplate*{background canvas}`), so
it is the page's `bg`, and in the body the ground of the frames after it. -/
def beamerColorRoles : List (String × String × String) :=
  [("normal text", "fg", "bg"),
   ("background canvas", "", "bg"),
   ("frametitle", "frametitlefg", "frametitlebg"),
   ("headline", "frametitlefg", "frametitlebg"),
   ("block title", "blocktitlefg", "blocktitlebg"),
   ("block title alerted", "alerttitlefg", "alerttitlebg"),
   ("block title example", "exampletitlefg", "exampletitlebg"),
   ("alerted text", "alert", ""),
   ("example text", "example", ""),
   ("standout", "standoutfg", "standoutbg"),
   ("progress bar", "progressfg", "progressbg"),
   ("progress bar in head/foot", "progressfg", "progressbg"),
   ("progress bar in section page", "progressfg", "progressbg"),
   ("title separator", "separator", ""),
   ("footline", "muted", ""),
   ("page number in head/foot", "muted", "")]

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
def beamerFontElements : List (String × String × String) :=
  [("frametitle", "frametitle", "font"),
   ("standout", "standout", "font"),
   ("section title", "sectionpage", "font"),
   ("title", "titlepage", "font"),
   ("author", "titlepage", "author-font"),
   ("abstract title", "abstract", "font")]

/-- Beamer's font keys, whose values are already TeX font commands (beamer's
"Fonts" part, beamerbasefont.sty): the value *is* the translation, so the
engine adds no vocabulary and invents no canonical order — the commands
compose in the order the author wrote them, which is what a
`\fontsize{..}{..}\selectfont` value needs. `parent` is inheritance the
engine does not model and is named where it stands. -/
def beamerFontKeys : List String := ["size", "series", "shape", "family"]

/-- Classes that are an `article` with different defaults. -/
def articleClasses : List String :=
  ["scrartcl", "scrreprt", "scrbook", "report", "book", "memoir", "letter"]

/-- Résumé classes: the same flow model with the résumé genre's contract —
`moderncv` and `res` map onto the native `resume` class, as `beamer` maps
onto `slides`. -/
def resumeClasses : List String :=
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
def fontPackages : List (String × String) :=
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
the engine sets uniformly either way; `nointerlineskip` suppresses
interline glue that is never accumulated here; lineno's `linenomath`
pair wraps displays that are numbered like every galley line already
(the recorded divergence in tests/compat-index/lineno.txt);
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
def meaningFree : List (String × Nat × Option String) :=
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
   ("nointerlineskip", 0,
    some "vertical space is declared per block, never accumulated interline glue"),
   ("frenchspacing", 0, some "inter-sentence space is uniform here either way"),
   ("nonfrenchspacing", 0, some "inter-sentence space is uniform here either way"),
   ("selectfont", 0, some "font declarations apply where they stand"),
   ("linenomath", 0, some "display math lines are numbered like every galley line"),
   ("endlinenomath", 0, some "display math lines are numbered like every galley line")]

/-- Declarations whose loss is real — justification, breaking tolerance,
hyphenation language, page furniture — skipped with a warning that names
what changed, never silently: they used to sit in the silent list under a
comment claiming they say nothing about the document, and they do. Each
entry: arguments consumed, the message, the help. -/
def configSkip : List (String × Nat × String × Option String) :=
  [-- The four ragged-setting declarations are not here: the block walk gives
   -- the rest of the scope the setting it declares, on the side it declares
   -- (Ir.Block.ragged carries the flush side).
   ("sloppy", 0,
    "'\\sloppy' loosens TeX's line-breaking tolerance; the breaker keeps \
its own and an overfull line warns by itself", none),
   -- The vertical-distribution pair: a page-opening ask the `vdist`
   -- obligation will own (AGENTS table), named until it lands.
   ("raggedbottom", 0,
    "'\\raggedbottom' picks a vertical distribution; pages keep their declared distribution",
    none),
   ("flushbottom", 0,
    "'\\flushbottom' picks a vertical distribution; pages keep their declared distribution",
    none)]

/-- Where a LaTeX length parameter's value goes, decided by what LaTeX's
own code does with it and by which engine site reads it. -/
inductive ParamSite where
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
def listEnvs : List String := ["itemize", "enumerate", "description"]

/-- The kernel and booktabs length parameters, each with its site. A name
not here is a length of the document's own: a token of its name. -/
def paramSites : List (String × ParamSite) :=
  [("parskip", .page "parskip"),
   ("abovecaptionskip", .token "captionsep"),
   ("topsep", .token "topsep"),
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
   ("abovedisplayshortskip", .sizeReset (.unmodelled
      "spaces a display after a short line; a display here opens its long skip")),
   ("belowdisplayshortskip", .sizeReset (.unmodelled
      "spaces a display after a short line; a display here opens its long skip")),
   ("baselineskip", .sizeReset (.unmodelled
      "sets the leading; the leading here is the page's")),
   ("leftmargin", .listReset), ("itemsep", .listReset), ("parsep", .listReset),
   ("itemindent", .listReset), ("listparindent", .listReset), ("rightmargin", .listReset),
   ("parindent", .unmodelled "indents a paragraph's first line; paragraphs here are set flush"),
   ("partopsep", .unmodelled
      "adds to a list's opening space after a blank line, which the engine does not record"),
   ("labelsep", .unmodelled "separates a list label from its item; the gap here is half an em"),
   ("labelwidth", .unmodelled "boxes a list label; a label here sets at its own width"),
   ("footnotesep", .unmodelled "struts a footnote's first line; the strut here follows the type"),
   ("columnsep", .unmodelled "separates a two-column page's columns; the text here is one column"),
   ("arraycolsep", .unmodelled "pads an array's columns; the padding here is half an em"),
   ("jot", .unmodelled "adds space between an alignment's rows, which no site here reads"),
   ("fboxsep", .unmodelled "pads a framed box, which no site here reads"),
   ("fboxrule", .unmodelled "rules a framed box, which no site here reads"),
   ("arrayrulewidth", .unmodelled "sets a table rule's thickness, which no site here reads"),
   ("unitlength", .unmodelled "scales a picture environment, which no site here reads")]

/-- Is `n` a parameter `\normalsize` sets again (`ParamSite.sizeReset`)? -/
def sizeReset (n : String) : Bool :=
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
def beamerConfig : List (String × Nat) :=
  [("usecolortheme", 1),
   ("useinnertheme", 1),
   ("useoutertheme", 1),
   ("addtobeamertemplate", 3),
   ("metroset", 1),
   ("beamertemplatenavigationsymbolsempty", 0)]

/-- The native spelling a skipped beamer construct now has, named in its
warning's help: a warning the author can act on beats a dead end. -/
def beamerNative : List (String × String) :=
  [("usecolortheme", "\\theme{name} selects a token bundle; \\palette overrides its entries"),
   ("usefonttheme", "\\fonts selects families; \\style{element}{ font = {...} } styles one element"),
   ("setbeamercolor", "declare the colour with \\palette{ name = #RRGGBB }"),
   ("setbeamerfont", "declare it with \\style{element}{ font = {...} }"),
   ("metroset", "\\theme selects a token bundle; \\tokens and \\palette declare \
its entries directly"),
   ("setbeamertemplate", "'frame footer' translates to \\framefoot{...}; \\style{element}{...} \
styles elements; \\runningfoot sets a document footer"),
   ("addtobeamertemplate", "\\style{element}{...} styles elements; \\framefoot sets a frame footer")]

/-- Classes that produce a presentation: `beamer` (which rewrites to
`slides`) and `slides` itself. What a beamer mode specification is read
against — beamer's article mode keeps a frame the presentation omits. -/
def presentationClasses : List String := ["beamer", "slides"]

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
def themeAsking : List (String × String) :=
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
def themeAlias (nm : String) : String :=
  if nm == "metropolis" || nm == "m" then "moloch" else nm

/-- beamer's file-name spelling of a theme-family member, resolved to the
slot it names, that slot's prefix, and the theme name: `beamerthemeX` is
`\usetheme{X}`, `beamercolorthemeX` is `\usecolortheme{X}`, and so for each
slot. `themeAsking` read backwards — the same identity, so neither spelling
can mean something the other does not. The prefixes are mutually exclusive
(they differ at the character after `beamer`), so the first match is the
only match. -/
def themeSlotOfPackage? (p : String) : Option (String × String × String) :=
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
def boxShape : List (String × Nat × Nat) :=
  [("mbox", 0, 0), ("makebox", 2, 0), ("parbox", 3, 1)]

/-- Where a deferred declaration replays. A hook is a deferred declaration,
and every hook LaTeX documents names one of these points; the engine has one
deferral mechanism and each hook is a row in `deferredHooks`, never an arm of
its own.

`endPreamble` is the last position of the preamble, `beginDocument` the
instant `\\begin{document}` opens — the seam, whose two sides this engine
realizes structurally: declarations before the `document` environment,
content inside it. -/
inductive DeferPoint where
  | endPreamble
  | beginDocument
deriving BEq, Repr

/-- The deferral table: one row per hook. `\\AtBeginDocument` (ltfiles.dtx,
the begindocument hook) replays at `\\begin{document}`;
`\\AtEndPreamble` (etoolbox manual §3) replays at the end of the preamble.
A further hook costs a row here and nothing else. -/
def deferredHooks : List (String × DeferPoint) :=
  [("AtBeginDocument", .beginDocument), ("AtEndPreamble", .endPreamble)]

/-- The native declarations the *preamble* reads and the body refuses, so a
hook body's declaration half rides to the seam's preamble side rather than
being named misplaced. It restates `Elab.declCtrl ++ Elab.runningCtrl`,
which sits above this module and cannot be imported here; the restatement is
not allowed to drift — `hookSeamChecks` fails the moment the two disagree,
in either direction. -/
def hookPreambleSide : List String :=
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
def nativeDeclarations : List String := hookPreambleSide ++ ["framefoot"]

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
def translationRefused : List (String × String) :=
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
   ("addtobeamertemplate", "the body is arbitrary TeX spliced at a named \
point inside a template the engine does not model; where such a body carries \
content the loss is E0111's, which is a dropped body and not a style key")]

/-- A definition the conditional pass can read: its replacement text and the
two prefixes its meaning carries, `\long` and e-TeX's `\protected`, which
`\ifx` compares beside the text (TeXbook chapter 20: a `\long` macro and its
short twin are different meanings). `live`: the text does something only a
use can decide — it holds a conditional, sets a flag or makes a definition,
itself or through a macro it uses — so the pass expands the macro where it
is used rather than leave it to an expansion that has no conditionals.
`serial` orders definitions: a macro's text expands only macros defined
before it, the elaborator's own visibility rule, which is what makes the
expansion terminate. -/
private structure CondVal where
  raws : Array Raw
  long : Bool
  prot : Bool
  live : Bool := false
  serial : Nat := 0

/-- One change the conditional pass made to its definition state, with what
it replaced (`none`: the name was not bound, or the flag not declared). -/
private inductive CondUndo where
  | bind (n : String) (prev : Option (Option CondVal))
  | flag (n : String) (prev : Option Bool)

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

/-- What the package- and class-loaded tests read (`resolveLoaded`): the loads
written so far, in flow order. A package carries the option list its first
load passed — a second load of a loaded package passes nothing new, the
kernel's clash check aside (latex.ltx, `\@onefilewithoptions`) — and `none`
for a local style file, whose passed options the splice resolves inside the
file and does not carry. `passed` holds every `\PassOptionsToPackage` list
per package, and the class half mirrors the package half. -/
structure LoadSet where
  pkgs : Array (String × Option (Array String)) := #[]
  passed : Array (String × Array String) := #[]
  cls : Option (String × Array String) := none
  clsPassed : Array (String × Array String) := #[]
  deriving Repr, BEq, Inhabited

/-- One TeX parameter assignment, as TeX scans it (TeXbook ch. 24:
⟨variable⟩[=]⟨value⟩, and `\advance`⟨variable⟩[by]⟨value⟩): the parameter,
whether the value adds to it, and the raws of the value. -/
structure TexAssign where
  name : String
  add : Bool
  value : Array Raw
  deriving Repr

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
  /-- environ's environments whose code never places `\BODY`, with the
  signature letters their arguments read: each use keeps its arguments
  and drops the body, which environ collects and discards. -/
  discardEnvs : Array (String × String) := #[]
  /-- A `\usetheme` was seen: `\alert` then maps to the theme's alert colour
  rather than the unthemed bold stand-in. -/
  themed : Bool := false
  /-- The declared class produces a presentation. What a beamer *mode*
  specification is read against: `<presentation:0>` suppresses a frame only
  where the artifact is the presentation it addresses — beamer's article mode
  keeps exactly those frames, so a class-blind reading deletes content. -/
  deck : Bool := false
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
  /-- Constructs already warned about: forty frames sharing one unsupported
  idiom are one problem, not forty. -/
  warned : Array String := #[]
  /-- Every control word the conditional pass has seen bound, with the
  parameterless value when one is readable: presence is what `\ifdefined`
  reads, the value what `\ifnum`, `\ifodd`, `\ifcase` and `\ifx` read, at
  the site that reads them. `none` is a name bound in a way no value can be
  read from — a parameter text, an expanding definer over unread names, a
  `\let` to a name with no readable value, a definition inside a group the
  pass has left. An environment is a TeX group, so what it binds ends with
  it, a global definition excepted; a brace group keeps its names bound —
  as often as not it is an argument (a hook) whose definitions are not
  scoped to it, and that reading only ever errs toward "defined", the one
  that keeps a guarded branch — but no value set inside it is read past it. -/
  binds : Std.HashMap String (Option CondVal) := {}
  /-- `\newif` flags by base name (`\newif\ifshowdetail` records
  `showdetail`, initially false — plain TeX's `\newif` sets `\iffalse`)
  with the value the last `\Xtrue`/`\Xfalse` gave. Scoped like a value. -/
  flags : Std.HashMap String Bool := {}
  /-- The save stack (tex.web §268): each change to `binds` and `flags`, with
  what it replaced, so the close of the environment the change was made in
  undoes it. It holds only what changed, so a group costs what it binds. -/
  undo : Array CondUndo := #[]
  /-- Every global definition, in the order made (`\gdef`, `\xdef`,
  `\global`): what outlives the environment it was made in. -/
  globals : Array (String × Option CondVal) := #[]
  /-- The names the picture being walked binds for itself — a `\foreach`
  variable, a `\pgfmathsetmacro` target. pgf binds them in the picture's
  own scope, so a test that reads one is the picture's to evaluate. -/
  picBound : Array String := #[]
  /-- Definitions the conditional pass has recorded, the clock `CondVal.serial`
  reads. -/
  serial : Nat := 0
  /-- Where the macro being expanded by the conditional pass is used: the
  site its decisions are named at, since that is where TeX makes them. -/
  useSite : Option Pos := none
  /-- The conditional pass is inside a picture: a document macro there is
  read at the picture's own site, so the pass puts the value in force there
  into the picture rather than leave the walk a table for the whole
  document. -/
  inPicture : Bool := false
  /-- The document body has begun: a definition made from here on is read
  by the elaborator where it is made, not at the preamble's end. -/
  condInDoc : Bool := false
  /-- Preamble definitions whose texts the pass took its decisions out of,
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
  /-- Command names the rewrite walk has bound so far, in document order:
  what `\providecommand`'s keep-existing policy reads. Separate from
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
  /-- Names the caller declares the engine renders or reserves: what
  `\providecommand`'s keep-existing policy reads for commands this
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
  /-- The loads the loaded-test pass has read so far (`resolveLoaded`). -/
  loads : LoadSet := {}
  /-- A theme's own beamer font elements, as `\setbeamerfont` declared
  them: what `\usebeamerfont{<element>}` selects in a template the engine
  reads (`TitleTemplate.read`). Latest declaration wins. -/
  beamerFonts : Array (String × TitleTemplate.Font) := #[]

private abbrev M := StateM St

/-- The one door for a state mutation: `f`, then the `writes` bump the
dispatcher's silence guard reads. Every `modify`/`set` in this file outside
`say`/`write`/`account` is rejected by the pre-commit hook, so an arm
cannot mutate state invisibly to the guard. -/
private def write (f : St → St) : M Unit :=
  modify fun st => { f st with writes := st.writes + 1 }

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
def codeInternal (name : String) : Bool :=
  name.contains '@'

/-- Is a site in `file` package code — a style or class file the document
loads — rather than the document's own text? The splice names every span of
a local `.sty` by its file (the input wrapper), and a hook such a file
registers replays inside that wrapper (`rewrite`), so the file a site stands
in is the boundary. A class file would be `.cls`; none is read today. -/
def packageFile (file : String) : Bool :=
  file.endsWith ".sty" || file.endsWith ".cls"

/-- A refusal of `name` at a site in `file` demotes exactly when the site is
inside package code — the only door a `.sty` span enters by is the splice
(`\input` reads `.tex`) — and the name is a TeX internal. The author can act
on a per-line warning in their own files; in a venue's style file they
cannot, and N0020 already names that file once. -/
def styInternal (file name : String) : Bool :=
  packageFile file && texInternal name

/-- The one door a diagnostic lands through here: a push, never a write —
the silence guard reads `diags.size` growth on its own. `subject` is the
census key of the loss, so "this loss is named" stays a lookup and
`Diag.tallySites` can count its sites. -/
private def say (code : DiagCode) (msg : String) (pos : Pos) (help : Option String := none)
    (demote : Bool := false) (subject : Option String := none)
    (refused : Option String := none) : M Unit :=
  modify fun st => { st with
    diags := st.diags.push (
      let d := Diag.of code msg (some ⟨st.file, pos⟩) help subject refused
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
  | .verb env s _ => .verb env s p

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

/-- Up to `n` brace groups. A bare control word or single word counts as a
group too, as in TeX: `\newcommand\x` and `\textbf x` are legal. -/
def takeGroups (raws : Array Raw) (i n : Nat) : Array (Array Raw) × Nat := Id.run do
  let mut out : Array (Array Raw) := #[]
  let mut j := i
  for _ in [0:n] do
    let k := skipSpaces raws j
    match raws[k]? with
    | some (.group body _) => out := out.push body; j := k + 1
    | some (r@(.ctrl _ _)) => out := out.push #[r]; j := k + 1
    | _ => break
  return (out, j)

/-- The alert style around a body, one spelling for both `\alert` forms:
themed, the theme's alert colour AND bold — colour alone would be the only
signal distinguishing the run, which WCAG 2.2 SC 1.4.1 forbids (metropolis
itself colours only; the divergence is deliberate); unthemed there is no
alert colour and bold stands in. -/
def alertStyled (themed : Bool) (body : Array Raw) (pos : Pos) : Array Raw :=
  if themed then
    #[.ctrl "textcolor" pos, .group #[.word "alert" pos] pos,
      .group #[.ctrl "textbf" pos, .group body pos] pos]
  else #[.ctrl "textbf" pos, .group body pos]

/-- `\alert<spec>{body}` is beamer's own equation,
`\alt<spec>{\alert{body}}{body}`: the alert style on the spec's steps, the
plain body on every other step, and nothing covered — alternation, not
transparency. The stopgap it replaces was `\uncover<spec>{\alert{body}}`,
taken when no IR constructor could vary style per step: one copy carrying
the alert style throughout, dimmed before its step, so the run was alert
from step one and the reader saw the change as undimming rather than as
becoming alert. `Ir.Inline.alt` varies content per step page and both
backends select one group from it (`alt_backend_agree`), so the faithful
rewrite costs nothing the census would call a doubling: the two
alternatives are declared once each and exactly one is inked per page.

The spec word travels as written for the elaborator's one overlay reader
(its `\alt` arm numbers it or keeps the honest W0105 and shows the
alternatives), so there is still no second overlay implementation here.
The styled alternative comes first because that is the order the arm reads:
`\alt<spec>{active}{otherwise}`. -/
def alertOverlay (themed : Bool) (spec : Raw) (body : Array Raw) (pos : Pos) : Array Raw :=
  #[.ctrl "alt" pos, spec, .group (alertStyled themed body pos) pos, .group body pos]

/-- Text conservation for the two `\alert` spellings is stated where text
exists: a raw has no text census (which words are content and which are a
colour name is the elaborator's knowledge), so the fact is over the
elaborated inlines — `alertOverlayChecks` holds the shipped-page census of
the styled and the plain alternative, the body's text appearing exactly
once on every step page and covered on none. On the raws the statement is
structural: the body is carried whole, untouched, by the styled
alternative (`alertOverlay_styled_exact`) and by the plain one
(`alertOverlay_plain_exact`), and the overlay is those four raws and no
fifth (`alertOverlay_exact`) — so the two alternatives are the only copies
of the body, which is what the doubling defect needs pinned rather than
left to the definition. -/
theorem alertOverlay_exact (themed : Bool) (spec : Raw) (body : Array Raw) (pos : Pos) :
    alertOverlay themed spec body pos =
      #[.ctrl "alt" pos, spec, .group (alertStyled themed body pos) pos,
        .group body pos] := rfl

theorem alertOverlay_styled_exact (themed : Bool) (spec : Raw) (body : Array Raw)
    (pos : Pos) :
    (alertOverlay themed spec body pos)[2]? = some (.group (alertStyled themed body pos) pos) :=
  rfl

/-- The other alternative is the body itself, plain: what every step
outside the spec shows, unstyled and uncovered. -/
theorem alertOverlay_plain_exact (themed : Bool) (spec : Raw) (body : Array Raw)
    (pos : Pos) :
    (alertOverlay themed spec body pos)[3]? = some (.group body pos) := rfl

/-- The spec reaches the elaborator as written: the overlay carries it at
the position the `\alt` arm reads, so a spec the step model cannot number
is judged there (W0105), never silently dropped here. -/
theorem alertOverlay_spec_id (themed : Bool) (spec : Raw) (body : Array Raw) (pos : Pos) :
    (alertOverlay themed spec body pos)[1]? = some spec := rfl

/-- The boundary's set-line vocabulary: with the boundary open (the
default) these preamble lines are the standalone's, collected as written
and consumed silently — the real TikZ reads them where the engine's subset
cannot. A declared refusal (`\pictures{ tool = none }`) makes them unknown
commands again. Colours are not on this list: `\definecolor` folds into
the palette, and the palette is the one resolving site — the request
carries the roles a picture mentions with their resolved values
(`Ir.paletteDecls`), so a `\definecolor` and its `\palette` spelling
state one request (the conservation oracle holds them equal). -/
def boundaryCtrls : List String :=
  ["usetikzlibrary", "tikzset", "gtrset", "pgfplotsset"]

/-- The set lines the engine reads *itself*: their key lists address the
picture machinery, and the engine has picture machinery of its own
(`Picture.readStyleList` takes the `/.style` definitions out of a
`\tikzset`). Such a line is therefore never the sentence's and never an
unknown command, whichever renderer ends up drawing — it still rides to
the boundary as well (`boundaryCtrls` keeps it), because a picture the
subset draws nothing of is drawn there and needs the same definitions.
A subset of `boundaryCtrls`. -/
def nativeSetCtrls : List String := ["tikzset"]

/-- Picture packages, whose whole meaning is drawing: with the boundary
open (the default), their loads belong to the boundary standalone's
preamble (`boundaryDecls` carries each with its options) rather than being
W0103's named loss — the real TeX at the edge is what reads them. A closed
list, extended when a document brings the next one; a package with body
commands outside pictures does not belong here. -/
def boundaryPkgs : List String := ["genealogytree", "pgfplots", "circuitikz"]

/-- The document refused the boundary: a `\pictures` block declaring
`tool = none`. Read over the unrewritten preamble exactly as
`boundaryDecls` reads its lines (order-free, `\input` wrappers spliced);
the one consumer is the `\usepackage` dispatch, which must know whether a
picture package's load rides to the boundary or is W0103's named loss.
The elaborator reads the same declaration through `scanDecls`. -/
def boundaryRefused (raws0 : Array Raw) : Bool := Id.run do
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
def pictureEnvs : List String := ["tikzpicture", "external"]

/-- The control words the picture walk gives a meaning of its own — its
statement heads, `\else` and `\fi` (`Picture.walkCtrls`, which a test holds
equal to this list). The conditional pass puts no document macro of such a
name into a picture: the walk names it where it stands. -/
def picWalkCtrls : List String :=
  ["fill", "node", "draw", "path", "foreach", "pgfmathsetmacro",
   "pgfmathtruncatemacro", "else", "fi"]

/-- What one tree walk collects for the renderers of a document's
pictures: `pre` is the boundary standalone's preamble, as written; `sets`
is the same collection read natively — one entry per `nativeSetCtrls`
line, its key list beside the position of the line that wrote it. One
accumulator, so the two readings cannot disagree about which definitions
reached a picture. -/
structure BoundaryScan where
  pre : String := ""
  sets : Array (Pos × Array Raw) := #[]

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
private def boundaryLevel (raws : Array Raw) (out : BoundaryScan) :
    List Raw → Nat → Nat → BoundaryScan
  | [], _, _ => out
  | _ :: rest, i, skip + 1 => boundaryLevel raws out rest (i + 1) skip
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
      boundaryLevel raws out rest (i + 1) (k - (i + 1))
    else if boundaryCtrls.contains name then
      let (args, k) := takeGroups raws (i + 1) 1
      let groups := String.join (args.toList.map fun g => s!"\{{rawSrc g}}")
      let out := { out with pre := out.pre ++ s!"\\{name}" ++ groups ++ "\n" }
      let out :=
        if nativeSetCtrls.contains name then
          { out with sets := out.sets.push (p, args.getD 0 #[]) }
        else out
      boundaryLevel raws out rest (i + 1) (k - (i + 1))
    else boundaryLevel raws out rest (i + 1) 0
  | r :: rest, i, 0 => boundaryLevel raws (boundaryRaw out r) rest (i + 1) 0

/-- Descend into a group or an environment. Split from the list walk so
the recursion is structural on `Raw`: the body is a field of the head, not
a tail of the list — `rewriteList`/`rewriteRaw`'s shape. -/
private def boundaryRaw (out : BoundaryScan) : Raw → BoundaryScan
  | .group body _ => boundaryLevel body out body.toList 0 0
  | .env n body _ =>
    if pictureEnvs.contains n then out
    else boundaryLevel body out body.toList 0 0
  | .math _ body _ => boundaryLevel body out body.toList 0 0
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
def boundaryScan (raws : Array Raw) : BoundaryScan :=
  boundaryLevel raws {} raws.toList 0 0

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
def boundaryDecls (raws : Array Raw) : String :=
  (boundaryScan raws).pre

/-- The key lists the engine reads itself, in source order, each with the
position of the `\tikzset` that wrote it. Read from the *unrewritten* tree
for the same reason `boundaryDecls` is, and from the whole tree for the
same reason: where the author wrote a definition says nothing about which
pictures need it. The one consumer is the elaborator, which folds the
`/.style` entries into every picture's bundles (`Picture.readStyleList`)
and names what it could not read at the line above. -/
def tikzsetKeys (raws : Array Raw) : Array (Pos × Array Raw) :=
  (boundaryScan raws).sets

/-- **A set line reaches the boundary wherever it stands.** Wrapping a run
of declarations in the document environment leaves the standalone's
preamble exactly what it was — the invariant whose absence was the defect:
the preamble-only walk returned nothing for this tree, so a `\tikzset`
written beside its picture (a figure kept in its own file) never reached
pgf, the boundary failed on an arrow tip or a shape it had no definition
for, and the page shipped an empty box. -/
theorem boundaryDecls_covers (raws : Array Raw) (p : Pos) :
    boundaryDecls #[.env "document" raws p] = boundaryDecls raws := by
  simp [boundaryDecls, boundaryScan, boundaryLevel, boundaryRaw, pictureEnvs]

/-- **And it reaches the engine's own renderer wherever it stands**, which
is the same claim for the native reading: a style defined beside its
picture, inside the document body, is the style that picture draws with.
Stated over the same walk the boundary's copy comes from, so neither
reading can gain a definition the other lost. -/
theorem tikzsetKeys_covers (raws : Array Raw) (p : Pos) :
    tikzsetKeys #[.env "document" raws p] = tikzsetKeys raws := by
  simp [tikzsetKeys, boundaryScan, boundaryLevel, boundaryRaw, pictureEnvs]

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
drops it silently. In the body natbib applies them from where they stand;
the engine reads natbib's punctuation for the whole document, so a body
declaration is named (W0340) and its groups consumed. -/
private def natbibStyleArm (name : String) (pos : Pos) (raws : Array Raw) (start : Nat) :
    M (Option (Array Raw × Nat)) := do
  let punct := name == "bibpunct"
  let (opt, j) := if punct then takeOpt raws start else (none, start)
  let (args, k) := takeGroups raws j (if punct then 6 else 1)
  if args.size != (if punct then 6 else 1) then return none
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
    else Bib.citeItems (src 0)
  let dropped := decls.filter (!Bib.CitePunct.reads ·)
  unless dropped.isEmpty do
    say .W0101 s!"'\\{name}' keywords without a native equivalent were dropped: \
{String.intercalate ", " (dropped.toList.map fun d => s!"'{d}'")}" pos
      (help := "natbib reads each keyword exactly as written, so write no space after a comma")
      (subject := some ("ctrl:" ++ name))
  if punct && (src 3).trimAscii.toString == "s" then
    say .W0101 s!"'\\bibpunct' superscript citations are set on the baseline" pos
      (subject := some "ctrl:bibpunct")
  became s!"\\{name}" "natbib's citation punctuation, read at \\begin{document}" pos
  natbibDefer (#["nobibstyle"] ++ decls) pos
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
def ptMacros : List (String × Nat) :=
  [("@vpt", 5000), ("@vipt", 6000), ("@viipt", 7000), ("@viiipt", 8000),
   ("@ixpt", 9000), ("@xpt", 10000), ("@xipt", 10950), ("@xiipt", 12000),
   ("@xivpt", 14400), ("@xviipt", 17280), ("@xxpt", 20740), ("@xxvpt", 24880)]

/-- One `\@setfontsize` argument in milli-points: a kernel size macro, or
a literal number (`{14}`, `{10.95}`). -/
def ptMacroArg (r : Array Raw) : Option Nat :=
  match r.toList with
  | [.ctrl n _] => ptMacros.lookup n
  | _ =>
    (Decl.parseDecimal (rawSrc r).trimAscii.toString).bind fun (m, s) =>
      if m ≥ 0 && s > 0 then some (m.toNat * 1000 / s) else none

/-- A milli value as its shortest decimal spelling: 10000 is "10",
10950 "10.95", 913 "0.913". -/
def milliStr (m : Nat) : String :=
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
def condHeads : List String :=
  (texPrimitives.toList.filter (·.startsWith "if")) ++ ["ifdefined", "ifcsname", "iffontchar"]

/-- Definers that bind the control word standing after them, directly or
as `{\name}`. -/
private def definesNext : List String :=
  ["def", "edef", "gdef", "xdef", "let", "newcommand", "renewcommand",
   "providecommand", "DeclareRobustCommand", "DeclareMathOperator",
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
declared, not a conditional. -/
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
      else if n.startsWith "if" then return none
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
      match (v.raws.filter fun r => !(r matches .space)).toList with
      | [.word w _] => condIntLit w
      | [.ctrl m _] => condIntOf vals k m
      | _ => none
    | _ => none

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
      let v := st.binds.contains n
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
        let v := rawSrc va.raws == rawSrc vb.raws && va.long == vb.long && va.prot == vb.prot
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
content: `definesNext`, the environment definers, and xparse's command
definers. A definition's replacement text is expanded where the definition
is used, never where it is made. -/
private def condDefiners : List String :=
  definesNext ++ ["newenvironment", "renewenvironment", "NewDocumentCommand",
    "RenewDocumentCommand", "ProvideDocumentCommand", "DeclareDocumentCommand"]

/-- Is `n` the setter of a declared flag (`\Xtrue`, `\Xfalse`)? -/
private def isFlagSetter (flags : Std.HashMap String Bool) (n : String) : Bool :=
  (n.endsWith "true" && flags.contains (n.dropEnd 4).toString) ||
    (n.endsWith "false" && flags.contains (n.dropEnd 5).toString)

mutual

-- conserves: none — a predicate over a replacement text, not a walk that
-- rewrites one.
/-- Does a replacement text do something only its use can decide
(`CondVal.live`): hold a conditional, set a flag, make a definition or a
picture — itself, or through a macro it uses whose own text does? -/
private def condLiveList (flags : Std.HashMap String Bool)
    (binds : Std.HashMap String (Option CondVal)) : List Raw → Bool
  | [] => false
  | r :: rest => condLiveRaw flags binds r || condLiveList flags binds rest

private def condLiveRaw (flags : Std.HashMap String Bool)
    (binds : Std.HashMap String (Option CondVal)) : Raw → Bool
  | .ctrl n _ =>
    isCondHead flags n || n == "unless" || n == "newif" || condDefiners.contains n ||
      isFlagSetter flags n ||
      (match condValueOf binds n with
       | some (some v) => v.live
       | _ => false)
  | .group body _ => condLiveList flags binds body.toList
  | .env n body _ => pictureEnvs.contains n || condLiveList flags binds body.toList
  | .math _ body _ => condLiveList flags binds body.toList
  | .word _ _ => false
  | .space => false
  | .par _ => false
  | .sym _ _ => false
  | .verb _ _ _ => false

end

mutual

-- conserves: none — drops each conditional extent and flag setting a
-- definition's text holds, by design: they are decided at a use.
/-- A replacement text with what only a use can decide removed, at any
depth — every conditional extent the pass can match, every declared flag's
setter and `\newif` — and whether anything was: the text an expansion that
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

mutual

-- conserves: none — the scan answers a set of names, not a tree.
/-- The names the definers inside a replacement text bind, at any depth:
bound where the text is used, which the pass reads as bound from the
definition on — the flat reading, which only ever errs toward "defined". -/
private def condBindsList (acc : Array String) : List Raw → Array String
  | [] => acc
  | .ctrl d _ :: rest =>
    let acc := if definesNext.contains d then
        match (rest.dropWhile isSpaceOrStar).head?.bind boundName with
        | some m => acc.push m
        | none => acc
      else acc
    condBindsList acc rest
  | r :: rest => condBindsList (condBindsRaw acc r) rest

private def condBindsRaw (acc : Array String) : Raw → Array String
  | .group body _ => condBindsList acc body.toList
  | .env _ body _ => condBindsList acc body.toList
  | .math _ body _ => condBindsList acc body.toList
  | .word _ _ => acc
  | .space => acc
  | .par _ => acc
  | .ctrl _ _ => acc
  | .sym _ _ => acc
  | .verb _ _ _ => acc

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
private def definerShape (raws : Array Raw) (i : Nat) (d : String) : Option DefShape := Id.run do
  -- The first group at or after `k`, the parameter text or signature before it.
  let groupFrom (k : Nat) : Option Nat := Id.run do
    let mut j := k
    for _ in [k:min raws.size (k + 40)] do
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
    unless raws[j]? matches some (.ctrl _ _) do return none
    let some b := groupFrom (j + 1) | return none
    if d == "edef" || d == "xdef" then return some { stop := b, bodies := [] }
    return some { stop := b + 1, bodies := [b] }
  if d == "let" then
    let j := skipSpaces raws (i + 1)
    let k0 := skipSpaces raws (j + 1)
    let k := if raws[k0]? matches some (.word "=" _) then skipSpaces raws (k0 + 1) else k0
    unless raws[j]? matches some (.ctrl _ _) do return none
    if k < raws.size then return some { stop := k + 1, bodies := [] }
    return none
  if d == "newcommand" || d == "renewcommand" || d == "providecommand" ||
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

/-- Record a definition of `n` whose readable value is `v` (`none`: none
the pass can read), globally when `global`. The value is stamped with the
next serial and with whether its text is live, read against the state the
definition is made in — what a macro it uses means is what that macro
meant then, the elaborator's own rule. -/
private def recordValue (n : String) (v : Option CondVal) (global : Bool) : M Unit := do
  let st ← get
  let s := st.serial + 1
  let v := v.map fun c =>
    { c with live := condLiveList st.flags st.binds c.raws.toList, serial := s }
  write fun st => { st with serial := s }
  setBind n v
  if global then write fun st => { st with globals := st.globals.push (n, v) }

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

/-- The value the definer `d` at `raws[i]` gives the name it binds: the body
of a parameterless definition and the prefixes its meaning carries. LaTeX's
`\newcommand` family is `\long` exactly when it takes arguments and is not
starred, so a parameterless one is never `\long` (measured against LaTeX2e
2025-11-01: `\meaning` reads `macro:->x` for `\def` and `\newcommand` alike);
one with arguments is unread here. An `\outer` macro cannot stand where
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
  if d == "def" || d == "gdef" || d == "edef" || d == "xdef" then
    let j := skipSpaces raws (i + 1)
    match raws[j]?, raws[j + 1]? with
    | some (.ctrl _ _), some (.group body _) =>
      if d == "def" || d == "gdef" then return some { raws := body, long, prot }
      if body.all fun r => !(r matches .ctrl _ _) then
        return some { raws := body, long, prot }
      match (body.filter fun r => !(r matches .space)).toList with
      | [.ctrl m _] =>
        match condValueOf st.binds m with
        | some (some v) =>
          if v.raws.all fun r => !(r matches .ctrl _ _) then
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
    | some (.ctrl _ _), some (.ctrl m _) => return (condValueOf st.binds m).bind id
    | _, _ => return none
  if d == "newcommand" || d == "renewcommand" || d == "providecommand" then
    let j0 := skipSpaces raws (i + 1)
    let star := raws[j0]? matches some (.word "*" _)
    let j := if star then skipSpaces raws (j0 + 1) else j0
    match raws[skipSpaces raws (j + 1)]? with
    | some (.group body _) => return some { raws := body, long := false, prot := false }
    | _ => return none
  return none

/-- Does the definer `d` at `raws[i]` define globally: `\gdef`, `\xdef`, or
a `\global` prefix among the definer's prefixes? -/
private def definesGlobally (raws : Array Raw) (i : Nat) (d : String) : Bool :=
  d == "gdef" || d == "xdef" || (definerPrefixes raws i).contains "global"

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

/-- Where the definition state stood when a group or environment opened: the
save stack's height, the globals made so far, the picture's own names. -/
private structure CondMark where
  undo : Nat
  globals : Nat
  picBound : Nat

private def condMark : M CondMark := do
  let st ← get
  return { undo := st.undo.size, globals := st.globals.size, picBound := st.picBound.size }

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

/-- A brace group closes. What it bound stays bound — the flat reading of
`binds` — but no value set inside it is read past it: the group is as often
an argument (a hook) whose definitions are not in force here as a TeX group
whose definitions are gone, and in neither case is the value set inside it
the one in force after it. The save stack keeps what the group changed, so
an enclosing environment still restores it, and the close costs what the
group bound — nothing, for a group that bound nothing. -/
private def condCloseGroup (m : CondMark) : M Unit := do
  let st ← get
  let changed := st.undo.extract m.undo st.undo.size
  let made := st.globals.size
  for u in changed do
    if let .bind n _ := u then
      write fun st => { st with binds := st.binds.insert n none }
  for k in [m.globals:made] do
    write fun st => { st with globals := st.globals.modify k fun p => (p.1, none) }

/-- Unwind the save stack to `m`, latest change first: the definition state
the mark was taken in, the picture's own names included. -/
private def condUnwind (m : CondMark) : M Unit := do
  let st ← get
  let recs := st.undo.extract m.undo st.undo.size
  write fun st => { st with undo := st.undo.shrink m.undo, picBound := st.picBound.shrink m.picBound }
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

/-- An environment closes. It is a TeX group, so the definition state is the
one it opened with — the save stack is unwound to its mark, latest change
first — and only the global definitions made inside it outlive it, in the
order they were made. -/
private def condCloseEnv (m : CondMark) : M Unit := do
  let made := (← get).globals.extract m.globals (← get).globals.size
  condUnwind m
  for (n, v) in made do setBind n v

mutual

/-- Resolve the decidable conditionals at one level. `stack` holds every open
conditional, innermost first; an element is emitted only while every frame
keeps what is read now (`CondOpen.keeps`), and a bare `\else`, `\or` or
`\fi` with nothing open is not ours and passes through. `skip` counts the
raws a decided head's test consumed. The list drives the recursion; `raws`
and `i` give the heads their lookahead, exactly as `rewriteList` pairs
them. -/
private def condList (ex : String → Pos → M (Option (Array Raw))) (raws : Array Raw)
    (out : Array Raw) (stack : List CondOpen) :
    List Raw → Nat → Nat → M (Array Raw)
  | [], _, _ => pure out
  | _ :: rest, i, skip + 1 => condList ex raws out stack rest (i + 1) skip
  | .ctrl "newif" pos :: .ctrl n np :: rest, i, 0 => do
    -- `\newif\ifX` declares a decidable flag, initially false (plain TeX:
    -- `\newif` ends with `\csname …false\endcsname`): `\ifX` joins this
    -- pass, `\Xtrue`/`\Xfalse` set it. A `\newif` whose next token is not
    -- an `\if…` name passes through for the ordinary unknown warning.
    if !(stack.all CondOpen.keeps) then
      condList ex raws out stack rest (i + 2) 0
    else if n.startsWith "if" && n.length > 2 then
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
      condList ex raws out stack rest (i + 2) 0
    else
      condList ex raws ((out.push (.ctrl "newif" pos)).push (.ctrl n np)) stack rest (i + 2) 0
  | .ctrl "newif" pos :: .space :: .ctrl n np :: rest, i, 0 => do
    if !(stack.all CondOpen.keeps) then
      condList ex raws out stack rest (i + 3) 0
    else if n.startsWith "if" && n.length > 2 then
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
      condList ex raws out stack rest (i + 3) 0
    else
      condList ex raws (((out.push (.ctrl "newif" pos)).push .space).push (.ctrl n np))
        stack rest (i + 3) 0
  | .ctrl "else" pos :: rest, i, 0 => do
    match stack with
    | [] => condList ex raws (out.push (.ctrl "else" pos)) [] rest (i + 1) 0
    | .decided k :: more => condList ex raws out (.decided (!k) :: more) rest (i + 1) 0
    | .cased sel cur _ :: more => condList ex raws out (.cased sel cur true :: more) rest (i + 1) 0
    | .opaque :: more =>
      let out := if more.all CondOpen.keeps then out.push (.ctrl "else" pos) else out
      condList ex raws out stack rest (i + 1) 0
  | .ctrl "or" pos :: rest, i, 0 => do
    match stack with
    | .cased sel cur false :: more =>
      condList ex raws out (.cased sel (cur + 1) false :: more) rest (i + 1) 0
    | _ =>
      let out := if stack.all CondOpen.keeps then out.push (.ctrl "or" pos) else out
      condList ex raws out stack rest (i + 1) 0
  | .ctrl "fi" pos :: rest, i, 0 => do
    match stack with
    | [] => condList ex raws (out.push (.ctrl "fi" pos)) [] rest (i + 1) 0
    | .opaque :: more =>
      let out := if more.all CondOpen.keeps then out.push (.ctrl "fi" pos) else out
      condList ex raws out more rest (i + 1) 0
    | _ :: more => condList ex raws out more rest (i + 1) 0
  | .ctrl "endinput" pos :: rest, i, 0 => do
    -- TeX reads the rest of the line, then no more of the file (TeXbook
    -- ch. 20). Only a file's own top level is cut: elsewhere the name
    -- passes through to be named where it stands. The walk ends here, so
    -- the conditionals the line closes close with it, and what else the
    -- line holds stands as written.
    if !(stack.all CondOpen.keeps) then
      condList ex raws out stack rest (i + 1) 0
    -- premise: endInputChecks — a wrapper's top level is a file's own text,
    -- the one list TeX stops reading at a terminator
    else if (← get).fileTop then
      let line := rest.takeWhile (onLine pos.line)
      if (rest.drop line.length).any fun r => !(r matches .space | .par _) then
        became "\\endinput" s!"the end of '{(← get).file}': its later lines are not read" pos
          (subject := some "ctrl:endinput")
      return out ++ (line.filter fun r =>
        !(r matches .ctrl "fi" _ | .ctrl "else" _ | .ctrl "or" _)).toArray
    else
      condList ex raws (out.push (.ctrl "endinput" pos)) stack rest (i + 1) 0
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
        condList ex raws (out.push (.ctrl n pos)) stack rest (i + 1) 0
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
          let out := if live then (out.push (.ctrl n pos)).push (.ctrl h hp) else out
          condList ex raws out stack' rest (i + 1) 1
        | .opaque, none =>
          let out := if live then out.push (.ctrl n pos) else out
          condList ex raws out stack' rest (i + 1) 0
        | _, _ =>
          let out := match r.tail with
            | some t => if stack'.all CondOpen.keeps then out.push t else out
            | none => out
          condList ex raws out stack' rest (i + 1)
            (r.used + (if unlessHead.isSome then 1 else 0))
    else if !(stack.all CondOpen.keeps) then
      condList ex raws out stack rest (i + 1) 0
    else if n.endsWith "true" && st.flags.contains (n.dropEnd 4).toString then
      let x := (n.dropEnd 4).toString
      setFlag x true
      -- premise: settleChecks — a settled text is read, not run: what it
      -- declares or sets is undone after, so no note may say it holds
      unless st.settling.isSome do
        sayOnce ("cond:set:" ++ n) .N0114 s!"'\\{n}': '\\if{x}' is true from here on"
          (st.useSite.getD pos)
      condList ex raws out stack rest (i + 1) 0
    else if n.endsWith "false" && st.flags.contains (n.dropEnd 5).toString then
      let x := (n.dropEnd 5).toString
      setFlag x false
      -- premise: settleChecks — a settled text is read, not run: what it
      -- declares or sets is undone after, so no note may say it holds
      unless st.settling.isSome do
        sayOnce ("cond:set:" ++ n) .N0114 s!"'\\{n}': '\\if{x}' is false from here on"
          (st.useSite.getD pos)
      condList ex raws out stack rest (i + 1) 0
    else if condDefiners.contains n then
      let bound := if definesNext.contains n then
          (rest.dropWhile isSpaceOrStar).head?.bind boundName
        else none
      if let some m := bound then
        unless n == "providecommand" && st.binds.contains m do
          -- Inside a frame the pass cannot decide, the branch may not run:
          -- the name is bound (the flat reading), its value unread.
          let v := if stack.any (· matches .opaque) then none
            else definedValue st raws i n
          recordValue m v (definesGlobally raws i n)
      match definerShape raws i n with
      | none => condList ex raws (out.push (.ctrl n pos)) stack rest (i + 1) 0
      | some sh =>
        -- The texts are expanded where the definition is used, never here:
        -- nothing in them is decided, set or defined now. The names they
        -- bind are bound from here on, and what the expansion cannot decide
        -- is taken out of the definition the elaborator expands.
        let st ← get
        let liveVal := match bound.bind (condValueOf st.binds ·) with
          | some (some v) => if v.live then some v.serial else none
          | _ => none
        -- A use of a built-in the pass never expands: the elaborator reads
        -- the text, at the preamble's end, so there it is settled.
        let expands := liveVal.isSome && !(bound.any st.provideKeeps.contains)
        let settles := liveVal.isSome && !st.condInDoc
        let flags := st.flags
        let site := st.useSite
        let file := st.file
        let mut ops : Array Raw := #[]
        let mut stripped := false
        let mut inner : Array String := #[]
        let mut texts : Array Pos := #[]
        for k in [i + 1:sh.stop] do
          if let some r := raws[k]? then
            if sh.bodies.contains k then
              inner := condBindsRaw inner r
              let (r', h) := condStripRaw flags r
              ops := ops.push r'
              stripped := stripped || h
              if let .group _ gp := r then texts := texts.push gp
            else ops := ops.push r
        for m in inner do recordDefined m
        if stripped && settles then
          if let (some m, some s) := (bound, liveVal) then
            for gp in texts do
              write fun st => { st with
                pending := st.pending.push { name := m, serial := s, file := file, pos := gp } }
        if stripped && !(expands || settles) then
          -- premise: macroUseChecks — a definition whose uses the pass does not
          -- expand keeps no conditional for the elaborator to spell as text
          sayOnce ("cond:body:" ++ n ++ ":" ++ (bound.getD "")) .W0104
            (s!"'\\{n}' makes a definition whose text holds a conditional or sets a \
flag, which TeX decides where the definition is used; this engine does not expand it with \
conditionals there, so that part of the text is skipped whole")
            (site.getD pos)
            (help := "a command without parameters, defined with \\def or \\newcommand, \
is expanded where it is used, conditional and all")
        condList ex raws ((out.push (.ctrl n pos)) ++ ops) stack rest (i + 1) (sh.stop - (i + 1))
    else if condNoExpand.contains n then
      -- The next token is read as itself here, never expanded.
      match rest with
      | r :: _ => condList ex raws ((out.push (.ctrl n pos)).push r) stack rest (i + 1) 1
      | [] => condList ex raws (out.push (.ctrl n pos)) stack rest (i + 1) 0
    else
      match ← ex n pos with
      | some body => condList ex raws (out ++ body) stack rest (i + 1) 0
      | none => condList ex raws (out.push (.ctrl n pos)) stack rest (i + 1) 0
  | r :: rest, i, 0 => do
    if stack.all CondOpen.keeps then
      condList ex raws (out.push (← condOne ex r)) stack rest (i + 1) 0
    else
      condList ex raws out stack rest (i + 1) 0

/-- Descend into a group, math or an environment body. An environment and
math are TeX groups: the definition state is restored when they close
(`condCloseEnv`); a brace group is read as `condCloseGroup` says. A
picture's own bindings are known before its body is read. An `\input`
wrapper switches the file its notes name, as `rewriteRaw` does, and is no
group at all. -/
private def condOne (ex : String → Pos → M (Option (Array Raw))) : Raw → M Raw
  | .group body p => do
    let m ← condMark
    let top ← swapTop false
    let body' ← condList ex body #[] [] body.toList 0 0
    let _ ← swapTop top
    condCloseGroup m
    return .group body' p
  | .math d body p => do
    let m ← condMark
    let top ← swapTop false
    let body' ← condList ex body #[] [] body.toList 0 0
    let _ ← swapTop top
    condCloseEnv m
    return .math d body' p
  | .env n body p => do
    match Parse.inputEnvFile? n with
    | some f =>
      let saved := (← get).file
      write fun st => { st with file := f }
      let top ← swapTop true
      let body' ← condList ex body #[] [] body.toList 0 0
      let _ ← swapTop top
      write fun st => { st with file := saved }
      return .env n body' p
    | none =>
      let m ← condMark
      let inPic := (← get).inPicture
      if pictureEnvs.contains n then
        let names := condBoundLevel #[] body.toList
        write fun st => { st with picBound := st.picBound ++ names, inPicture := true }
      let top ← swapTop false
      let body' ← condList ex body #[] [] body.toList 0 0
      let _ ← swapTop top
      condCloseEnv m
      write fun st => { st with inPicture := inPic }
      return .env n body' p
  | r => pure r

end

/-- Expand the macro `n` where the conditional pass meets it in live
content, when its text does something only a use can decide
(`CondVal.live`), or when the use stands inside a picture, which reads a
macro at its own site: the text is walked where the use stands, against the
state in force there, so its conditionals are decided — and its flags set,
its definitions made — at the use, as TeX does, and the decisions are named
at the use. `bound` is the serial below which a text may expand: a use in
running text sees every definition made so far, a use inside a macro's text
only those made before that macro, the elaborator's own visibility rule, so
each nested expansion strictly lowers the bound. A live use the bound rules
out is refused by name; `none` leaves the name to the elaborator. -/
private def condExpandAt (bound : Nat) (n : String) (pos : Pos) : M (Option (Array Raw)) := do
  let st ← get
  let site := st.useSite
  let inPic := st.inPicture
  let own := st.picBound.contains n || st.provideKeeps.contains n ||
    (inPic && picWalkCtrls.contains n)
  match condValueOf st.binds n with
  | some (some v) =>
    -- premise: macroUseChecks — a use between two states of what the text reads
    if !(v.live || inPic) || own then return none
    if _h : v.serial < bound then
      write fun s => { s with useSite := some (site.getD pos) }
      let top ← swapTop false
      let out ← condList (fun m p => condExpandAt v.serial m p) v.raws #[] [] v.raws.toList 0 0
      let _ ← swapTop top
      write fun s => { s with useSite := site }
      return some out
    else if v.live then
      sayOnce ("cond:unexpanded:" ++ n) .W0104
        (s!"'\\{n}' holds a conditional or sets a flag, which TeX decides where it is \
used; here it is reached through a macro defined before it, which this engine expands \
without it, so that part of its text is skipped whole")
        (site.getD pos)
        (help := "define '\\{n}' before the macros that use it")
      return none
    else return none
  | _ => return none
termination_by bound

/-- The expander running text uses: every definition made so far is visible. -/
private def condTopExpand (n : String) (pos : Pos) : M (Option (Array Raw)) := do
  condExpandAt ((← get).serial + 1) n pos

/-- Run `act` and put the definition state back as it was: a definition's
text settled for the elaborator is read, not run, so nothing it binds, sets
or defines — globally or not — outlives the reading. -/
private def condSandbox (act : M (Array Raw)) : M (Array Raw) := do
  let m ← condMark
  let r ← act
  condUnwind m
  write fun st => { st with globals := st.globals.shrink m.globals }
  return r

/-- Settle the pending preamble definitions (`CondPending`) against the
state at the preamble's end, which is where the elaborator reads a text no
use the pass sees reaches: each one still in force is walked there, its
decisions named as the definition's, and handed back with where it stands.
The document body begins here. -/
private def condSettle : M (Array (String × Pos × Array Raw)) := do
  let pend := (← get).pending
  write fun st => { st with pending := #[], condInDoc := true }
  let mut out : Array (String × Pos × Array Raw) := #[]
  for p in pend do
    match condValueOf (← get).binds p.name with
    | some (some v) =>
      if v.serial == p.serial then
        let file := (← get).file
        write fun st => { st with file := p.file, settling := some p.name }
        let body ← condSandbox
          (condList (fun m q => condExpandAt v.serial m q) v.raws #[] [] v.raws.toList 0 0)
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

/-- The conditional pass over a document: its preamble, then the preamble's
pending definitions settled against the state at its end and put back, then
its body. A fragment with no `{document}` has no preamble's end, and is one
walk. -/
private def condDocument (raws : Array Raw) : M (Array Raw) := do
  match raws.findIdx? (· matches .env "document" _ _) with
  | none => condList condTopExpand raws #[] [] raws.toList 0 0
  | some d =>
    let pre := raws.extract 0 d
    let post := raws.extract d raws.size
    let pre' ← condList condTopExpand pre #[] [] pre.toList 0 0
    let texts ← condSettle
    let file := (← get).file
    let pre' := if texts.isEmpty then pre' else condPatchList texts file #[] pre'.toList
    let post' ← condList condTopExpand post #[] [] post.toList 0 0
    return pre' ++ post'

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

A test is answered for the moment it runs. Standing in the flow — the
preamble's, a style file's, the body's — it runs where it stands, and is read
against the loads before it. Inside a group it runs when the command holding
the group runs it: a deferred hook's body at `\begin{document}`, a definition
body where the command is used, an argument where its command sets it. Every
one of those is after the preamble but a preamble-time use, so a group's test
is read against the whole preamble's loads, on the pass's second walk, and
its note says so. The kept branch replaces the test, unbraced, as
`\@firstoftwo` leaves it, and the other goes with it; N0114 names the
choice. -/

/-- The branches a loaded test carries after its name and option list: both,
the true one only, or the false one only (latex.ltx defines the `T` and `F`
forms over the `TF` one with `\@firstofone\@gobble` and `{}`). -/
inductive LoadedBranches where
  | tf
  | t
  | f
  deriving BEq, Repr

/-- One spelling of the loaded-test family: whether it reads the class or the
packages, whether an option list follows the name, and its branches. -/
structure LoadedTest where
  ctrl : String
  cls : Bool
  withOpts : Bool
  branches : LoadedBranches
  deriving BEq, Repr

/-- The family as latex.ltx defines it: the `\@if…` internals, and the
`\If…Loaded…` interface `\let` to them or wrapped around them. -/
def loadedTests : List LoadedTest :=
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
structure LoadQuery where
  cls : Bool
  name : String
  want : Option (Array String)
  deriving BEq, Repr

/-- An option list as the kernel compares it: comma-separated, spaces zapped
(`\zap@space`), empty items skipped. -/
def optionItems (s : String) : Array String :=
  ((s.splitOn ",").map fun o => String.ofList (o.toList.filter (!·.isWhitespace)))
    |>.filter (!·.isEmpty) |>.toArray

/-- One package load: the first load of a name stands, and a later one of the
same name passes nothing new. -/
def LoadSet.addPkg (s : LoadSet) (p : String) (os : Option (Array String)) : LoadSet :=
  if s.pkgs.any (·.1 == p) then s else { s with pkgs := s.pkgs.push (p, os) }

/-- The class line: the first `\documentclass` is the class. -/
def LoadSet.setCls (s : LoadSet) (c : String) (os : Array String) : LoadSet :=
  if s.cls.isSome then s else { s with cls := some (c, os) }

/-- Option passes, onto the class half or the package half. -/
def LoadSet.pass (s : LoadSet) (toClass : Bool) (ps : Array (String × Array String)) :
    LoadSet :=
  if toClass then { s with clsPassed := s.clsPassed ++ ps }
  else { s with passed := s.passed ++ ps }

/-- The answer the loads read so far give a test: `some true` when it holds,
`some false` when it fails, `none` when what it reads is not carried — a
local style file's passed options, where only a positive answer is sound. -/
def LoadSet.answer (s : LoadSet) (q : LoadQuery) : Option Bool :=
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

/-- When a test runs, as far as its place in the flow says. -/
inductive LoadTiming where
  /-- Where it stands: the preamble's flow, a style file's, the body's. -/
  | now
  /-- Inside a group — a hook's body, a definition, an argument: when the
  command holding the group runs it, after the preamble. -/
  | after
  deriving BEq, Repr

/-- The answer a test site gets, or `none` when nothing fixes one yet:
`soFar` is what is loaded where the site stands, `final` the preamble's
whole load set, known on the second walk. -/
def loadedDecide (t : LoadTiming) (soFar : LoadSet) (final : Option LoadSet)
    (q : LoadQuery) : Option Bool :=
  match t with
  | .now => soFar.answer q
  | .after => final.bind (·.answer q)

/-- Exactly `n` brace groups after `i`, each after any spaces: a loaded
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
                want := if test.withOpts then some (optionItems (rawSrc (args.getD 1 #[])))
                  else none }

/-- Which of the groups after a resolved test are kept, unbraced, and which go
with it: the name and the option list go, and the branch the answer picks
stays. -/
def loadedPlan (test : LoadedTest) (ans : Bool) : List Bool :=
  let lead := if test.withOpts then [false, false] else [false]
  let branches := match test.branches with
    | .tf => [ans, !ans]
    | .t => [ans]
    | .f => [!ans]
  lead ++ branches

/-- The note a resolved test earns: what it read, when, and what that keeps. -/
private def loadedMsg (test : LoadedTest) (q : LoadQuery) (ans : Bool) (t : LoadTiming) :
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
  let moment := match t with
    | .now => " here"
    | .after => " by the end of the preamble"
  let kept := match test.branches, ans with
    | .tf, true => "the first branch is kept"
    | .tf, false => "only the second branch is kept"
    | .t, true | .f, false => "its branch is kept"
    | .t, false | .f, true => "its branch is dropped"
  s!"'\\{test.ctrl}': {fact}{moment}, so {kept}"

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
      else some (optionItems (opt.getD ""))
    write fun st => { st with loads :=
      (names (args.getD 0 #[])).foldl (fun s p => s.addPkg p os) st.loads }
  else if name == "documentclass" then
    let (opt, j) := takeOpt raws (i + 1)
    let (args, _) := takeGroups raws j 1
    let c := rawSrc (args.getD 0 #[])
    unless c.isEmpty do
      write fun st => { st with loads := st.loads.setCls c (optionItems (opt.getD "")) }
  else if name == "PassOptionsToPackage" || name == "PassOptionsToClass" then
    let (args, _) := takeGroups raws (i + 1) 2
    let os := optionItems (rawSrc (args.getD 0 #[]))
    let ps := (names (args.getD 1 #[])).map (·, os)
    write fun st => { st with loads := st.loads.pass (name == "PassOptionsToClass") ps }
  else if let some pre := themeAsking.lookup name then
    let (_, j) := takeOpt raws (i + 1)
    let (args, _) := takeGroups raws j 1
    let nm := rawSrc (args.getD 0 #[])
    unless nm.isEmpty do
      write fun st => { st with loads := st.loads.addPkg (pre ++ nm) (some #[]) }

mutual

/-- One level of the loaded-test pass. The list drives the recursion and the
array gives the lookahead, as `condList` pairs them; `plan` is what the
groups after a resolved test become, one entry per group, and the spaces
between them go too. -/
private def loadList (final : Option LoadSet) (raws : Array Raw) (t : LoadTiming)
    (out : Array Raw) (plan : List Bool) : List Raw → Nat → M (Array Raw)
  | [], _ => pure out
  | .space :: rest, i =>
    loadList final raws t (if plan.isEmpty then out.push .space else out) plan rest (i + 1)
  | .ctrl name pos :: rest, i => do
    match (loadedTests.find? (·.ctrl == name)).bind fun test =>
        (loadedAt raws (i + 1) test).map (test, ·) with
    | some (test, q) =>
      -- premise: none — a package another package loads is invisible here and
      -- reads as not loaded, and a group's test is read as run after the preamble
      match loadedDecide t (← get).loads final q with
      | some ans =>
        let msg := loadedMsg test q ans t
        sayOnce ("ifloaded:" ++ msg) .N0114 msg pos
        loadList final raws t out (loadedPlan test ans) rest (i + 1)
      | none => loadList final raws t (out.push (.ctrl name pos)) [] rest (i + 1)
    | none =>
      if t == .now then recordLoad raws name i
      loadList final raws t (out.push (.ctrl name pos)) [] rest (i + 1)
  | r :: rest, i => do
    -- A group is tested, not matched, so `r` stays the list's own element.
    if r matches .group _ _ then
      match plan with
      | keep :: more =>
        let out ← if keep then loadOne final t out true r else pure out
        loadList final raws t out more rest (i + 1)
      | [] =>
        let out ← loadOne final .after out false r
        loadList final raws t out [] rest (i + 1)
    else
      let out ← loadOne final t out false r
      loadList final raws t out [] rest (i + 1)
termination_by structural l _ => l

/-- One element under the pass. A kept branch is walked into the level it
stands in, unbraced; the first walk leaves every other group whole, since the
loads a group's tests are read against are not all known yet. A local style
file is a load where it is spliced: `\ver@X.sty` is defined as the file starts
to be read, so the file's own tests already see it. -/
private def loadOne (final : Option LoadSet) (t : LoadTiming) (out : Array Raw)
    (unbrace : Bool) : Raw → M (Array Raw)
  | .group body p => do
    if unbrace then loadList final body t out [] body.toList 0
    else if final.isNone then pure (out.push (.group body p))
    else
      let inner ← loadList final body t #[] [] body.toList 0
      pure (out.push (.group inner p))
  | .env n body p => do
    match Parse.inputEnvFile? n with
    | some f =>
      if t == .now && f.endsWith ".sty" then
        let pkg := (f.dropEnd ".sty".length).toString
        write fun st => { st with loads := st.loads.addPkg pkg none }
      let saved := (← get).file
      write fun st => { st with file := f }
      let inner ← loadList final body t #[] [] body.toList 0
      write fun st => { st with file := saved }
      pure (out.push (.env n inner p))
    | none =>
      let inner ← loadList final body t #[] [] body.toList 0
      pure (out.push (.env n inner p))
  | r => pure (out.push r)
termination_by structural r => r

end

/-- The loaded-test pass: a first walk reads the preamble's loads and answers
every test standing in the flow, and a second answers every test inside a
group against the whole preamble. A site is answered by exactly one walk, so
each choice is named once. -/
private def resolveLoaded (raws : Array Raw) : M (Array Raw) := do
  let raws ← loadList none raws .now #[] [] raws.toList 0
  let final := (← get).loads
  write fun st => { st with loads := {} }
  loadList (some final) raws .now #[] [] raws.toList 0

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

mutual

/-- The one deferral pass: a hook named in `deferredHooks` is removed from
the stream and its body stored with the point it replays at. The body is
stored VERBATIM and is never walked here — that is the rule that makes the
mechanism terminate by construction rather than by a fuel parameter: a
replay cannot re-collect. Collection finishes before any replay happens, so
a `\\AtBeginDocument` written inside a hook body is not a second deferral;
it meets the dispatcher at the replay point, where the document is already
at the hook's own moment, and its group is read where it stands
(`rewriteCtrl`'s arm says so with W0340).

The `document` environment is not descended into: a hook is a preamble
declaration (LaTeX's own `\\@onlypreamble`), so a hook standing in the body
is at its replay point already and takes the same arm. -/
private def collectDeferList (out : Array Raw) : List Raw → M (Array Raw)
  | [] => pure out
  | .ctrl name pos :: .group body p :: rest => do
    if let some pt := deferredHooks.lookup name then
      deferOne name pt body pos
      collectDeferList out rest
    else
      let g ← collectDeferOne (.group body p)
      collectDeferList ((out.push (.ctrl name pos)).push g) rest
  | .ctrl name pos :: .space :: .group body p :: rest => do
    if let some pt := deferredHooks.lookup name then
      deferOne name pt body pos
      collectDeferList out rest
    else
      let g ← collectDeferOne (.group body p)
      collectDeferList (((out.push (.ctrl name pos)).push .space).push g) rest
  | r :: rest => do
    collectDeferList (out.push (← collectDeferOne r)) rest

/-- Descend into a group or environment body; an `\\input` wrapper switches
the file its note names, as `condOne` and `rewriteRaw` do. The document
environment is left whole: see `collectDeferList`. -/
private def collectDeferOne : Raw → M Raw
  | .group body p => do
    return .group (← collectDeferList #[] body.toList) p
  | .env "document" body p => pure (.env "document" body p)
  | .env n body p => do
    match Parse.inputEnvFile? n with
    | some f =>
      let saved := (← get).file
      write fun st => { st with file := f }
      let body' ← collectDeferList #[] body.toList
      write fun st => { st with file := saved }
      return .env n body' p
    | none =>
      return .env n (← collectDeferList #[] body.toList) p
  | r => pure r

end

/-- A TeX length in the native spelling: `0.5\rhythm` is `0.5 * rhythm`,
`\relax` vanishes. Each control word goes through `ref`, told whether an
argument group follows it; `none` from `ref` makes the whole value
unreadable. `\dimexpr … \relax` is its parenthesized expression. -/
private def lengthSrcBy (ref : String → Bool → Option String) (raws : Array Raw) :
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
private def kernelSkip : String → Option String
  | "smallskipamount" => some "3pt plus 1pt minus 1pt"
  | "medskipamount" => some "6pt plus 2pt minus 2pt"
  | "bigskipamount" => some "12pt plus 4pt minus 4pt"
  | _ => none

/-- A length value as the door reads it where it stands: a kernel parameter
the document set is the value it holds (TeX copies a register's value; the
parameter's own token may not exist, or carry an engine name), a kernel
skip amount is its fixed value, and any other name is a token of the
document's, read where the declaration reads it. `none` for what the door
cannot evaluate: a kernel parameter whose value it was never told (the
class sets it), a box's dimension, and a command that computes a length
(`\stretch`, calc's `\widthof`). In a definition's body (`deferred`) the
assignment runs where the command is used, so a kernel parameter is read
there, by its name. -/
private def lenValue (lens : Array (String × String)) (raws : Array Raw)
    (deferred : Bool := false) : Option String :=
  let kernel (n : String) : Bool := !deferred && (paramSites.lookup n).isSome
  let held (n : String) : Option String :=
    (if kernel n then (lens.find? (·.1 == n)).map (·.2) else none).orElse
      fun _ => kernelSkip n
  let unknown (n : String) : Bool := kernel n || n == "ht" || n == "wd" || n == "dp"
  let ref (n : String) (arg : Bool) : Option String :=
    if arg then none
    else match held n with
      | some v => some s!"({v})"
      | none => if unknown n then none else some n
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
  match (paramSites.lookup n).getD (.token n), st.inDef with
  | .page key, _ => emit s!"\\page\{ {key} = {src} }"
  | .token t, _ => emit s!"\\tokens\{ {t} = {src} }"
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
    else if st.inList then
      -- premise: unreadableLengthChecks — the setting builds inside its list,
      -- named once, and the list keeps its level's spacing
      nameParam n "spaces this one list; a list here is spaced per level, in the preamble" pos
      return #[]
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

/-- A length assignment from its value's raws (`\setlength`, TeX's own
`\parskip 6pt`): read at the door and landed by `setLength`, or named and
skipped (`unreadableLength`). -/
private def assignLength (n : String) (value : Array Raw) (what : String) (pos : Pos) :
    M (Array Raw) := do
  let st ← get
  if let some src := lenValue st.lens value st.inDef then
    if readsAsLength src then return ← setLength n src what pos
  unreadableLength n (rawSrc value).trimAscii.toString pos

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

/-- The raw standing before index `i`, spaces skipped. -/
private def rawBefore (raws : Array Raw) (i : Nat) : Option Raw := Id.run do
  let mut k := i
  for _ in [0:i] do
    k := k - 1
    match raws[k]? with
    | some .space => pure ()
    | r => return r
  return none

/-- TeX's own assignment to a kernel parameter, when the control word
`name`, read up to `start`, opens one (TeXbook ch. 24:
⟨variable⟩[=]⟨value⟩, as `\parskip 6pt plus 1pt`, `\parskip=0pt` and
`\parindent\z@` spell it): the value's raws and where it ends. The value
starts with `=`, a number or a register; a parameter read as an operand —
after `\hskip`, or before words — opens none. -/
private def plainAssign? (name : String) (raws : Array Raw) (start : Nat) :
    Option (Array Raw × Nat) :=
  if (paramSites.lookup name).isNone then none
  else if (match rawBefore raws (start - 1) with
      | some (.ctrl c _) => ["hskip", "vskip", "kern", "the", "showthe", "advance",
          "multiply", "divide"].contains c
      | _ => false) then none
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
def listLevelOf : String → Option Nat
  | "@listi" => some 1
  | "@listii" => some 2
  | "@listiii" => some 3
  | "@listiv" => some 4
  | "@listv" => some 5
  | "@listvi" => some 6
  | _ => none

/-- The list parameters a level's style carries: `\leftmargin` its indent,
`\topsep` its opening space, `\itemsep` and `\parsep` its gap between items. -/
private def listCarried : List String := ["leftmargin", "topsep", "itemsep", "parsep"]

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
  let preamble (n : String) : Option String := if st.lens.any (·.1 == n) then some n else none
  let mut run : List (String × Option String) := listCarried.map fun n => (n, preamble n)
  let mut out : Array Raw := #[]
  for level in [1:5] do
    match defOf level with
    | none => run := listCarried.map fun n => (n, none)
    | some (pos, assigns) =>
      for a in assigns do
        if listCarried.contains a.name then
          let v := if a.add then none else listOperand run st.lens a.value
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

/-- `\pagecolor[model]{colour}` sets the page background from here on
(xcolor manual §2.6); the engine's page background is the palette's `bg`
role, the one resolving site both backends read, so the contrast contracts
judge text against the colour the page actually paints. -/
private def pageColor (value : String) (pos : Pos) : M (Array Raw) := do
  let native := s!"\\palette\{ bg = {value} }"
  became "\\pagecolor" native pos
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
    (have hb : sizeOf body = 1 + sizeOf body.toList := rfl; omega)

/-- environ's `\BODY` placed once at the top level of a definition's code:
the code before it and the code after it, an environment's begin and end
code with the body standing between them. `none` when `\BODY` is absent,
stands inside a group, or stands twice. -/
def bodySlot? (code : Array Raw) : Option (Array Raw × Array Raw) :=
  (code.findIdx? (· matches .ctrl "BODY" _)).bind fun i =>
    let before := code.extract 0 i
    let after := code.extract (i + 1) code.size
    if mentionsBody before.toList || mentionsBody after.toList then none
    else some (before, after)

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
    let entries := decls.map fun (r, v) =>
      let tok := if r == "abovecaptionskip" then "captionsep" else "belowcaptionskip"
      s!"{kind.captionScope}{tok} = {lengthSrc v}"
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
   ("onehalfspacing", "\\page{ leading = 1.25 }"),
   ("doublespacing", "\\page{ leading = 1.667 }")]

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

/-- `\alert{body}` without an overlay spec: the plain rewrite, byte for
byte what it was before the spec form existed — themed, `\textcolor{alert}`
around bold; unthemed, `\textbf` with the body left in the stream. -/
private def alertPlain (pos : Pos) (raws : Array Raw) (start : Nat) :
    M (Option (Array Raw × Nat)) := do
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

/-- The later half of `rewriteCtrl`'s dispatch, split out so neither
half's `match` exhausts the LCNF compiler's heartbeat budget — one
logical dispatcher, two compilation units. `rewriteCtrl`'s own match
falls through to here for every name it does not claim. -/
private def rewriteCtrlLater (name : String) (pos : Pos) (raws : Array Raw)
    (start : Nat) : M (Option (Array Raw × Nat)) := do
  match name with
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
  | "setcitestyle" | "bibpunct" => natbibStyleArm name pos raws start
  | "bibliographystyle" =>
    -- LaTeX reads the style anywhere before the `.aux` is written, and
    -- natbib reads it back at `\begin{document}`. The preamble elaborator
    -- does not take it, so a preamble declaration replays there, where the
    -- body arm carries it to the `\bibliography` marker.
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
      -- A class's list-level macro read as the parameters it assigns.
      if found && !expanding && ps.isEmpty && (← docPreamble) then
        if let (some level, some (.group body _)) := (listLevelOf cmd, raws[k]?) then
          if ← listLevelDef level s!"\\{name}\{\\{cmd}}" body pos then
            return some (#[], k + 1)
      if found && !expanding && undelimited then
        let n := ps.size / 2
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
    -- environment's body into `\BODY` and runs the code, the end code runs
    -- the final code. With `\BODY` once at the code's top level that is the
    -- kernel's `\newenvironment` with the body standing there, so it takes
    -- the native definer's spelling, the code group announced as a macro
    -- body, and the elaborator splits it at `\BODY` (`bodySlot?`), a
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
      let final := raws[skipSpaces raws (b + 1)]? matches some (.sym '[' _)
      if (bodySlot? code).isSome then
        became s!"\\{name}\{{envName}}" (native ++ " {code before \\BODY} {code after it}") pos
        write fun st => { st with bodyNext := 1 }
        write fun st => { st with discardEnvs := st.discardEnvs.filter (·.1 != envName.trimAscii.toString) }
        return some (← synthAt native pos, j)
      else if !mentionsBody code.toList && !final then
        -- A code that never places `\BODY` runs where the environment
        -- stands and the collected body goes nowhere, as environ.sty
        -- leaves it: the kernel's definer with an empty begin code and the
        -- code as the end code, the body discarded at each use (the
        -- `.env` arm of `rewriteRaw`, which keeps only the arguments).
        became s!"\\{name}\{{envName}}" (native ++ " {} {code}, its body discarded") pos
        write fun st => { st with bodyNext := 1 }
        write fun st => { st with discardEnvs := st.discardEnvs.push (envName.trimAscii.toString, spec) }
        return some ((← synthAt native pos).push (.group #[] pos), j)
      else
        let (_, k) := takeOpt raws (b + 1)
        let why := if mentionsBody code.toList then "places \\BODY inside a group or more than once"
          else "gives a final code to a body its code never places"
        sayOnce ("ctrl:" ++ name) .W0104
          s!"'\\{name}\{{envName}}' {why}; an environment's body stands between its begin \
and its end code here, so the definition is skipped" pos
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
    -- Themed, alert is the theme's colour AND bold (`alertStyled` says
    -- why). With an overlay spec the command is beamer's own
    -- `\alt<spec>{styled}{body}`: styled on the spec's steps, plain on
    -- every other, nothing covered — the spec used to fall through, and
    -- `\textcolor{alert}` then read `<2>` as its content and failed E0304
    -- (unthemed, `\textbf` set the spec as text), and the `\uncover`
    -- stopgap that replaced it carried the alert style on every step.
    -- Without a spec the plain rewrite stands untouched.
    let j := skipSpaces raws start
    match raws[j]? with
    | some (spec@(.word w _)) =>
      if w.startsWith "<" && w.endsWith ">" then
        let (args, k) := takeGroups raws (j + 1) 1
        match args[0]? with
        | some body =>
          became s!"\\alert{w}" s!"\\alt{w}\{...}\{...}" pos
          return some (alertOverlay (← get).themed spec body pos, k)
        | none => alertPlain pos raws (j + 1)
      else alertPlain pos raws start
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
    else if element == "title page" then
      let (_, j) := takeOpt raws j
      -- A template of the overlay shape — one picture on the page, a fill
      -- over it, nodes pinned to its points — is a spelling of the engine's
      -- own title page, and is read as one: the ground and one slot per
      -- node (`TitleTemplate.read`, `.native`). What the reader meets and
      -- does not model is one named loss, never a fallback.
      let (bodyArgs, k) := takeGroups raws j 1
      match TitleTemplate.read (← get).beamerFonts.toList (bodyArgs.getD 0 #[]) with
      | some { mixed := some datum, .. } =>
        -- A datum beside literal text has no slot to stand in, and a
        -- datum is never dropped: the template is not read, the built-in
        -- title page sets every datum, and that is the one named loss.
        let (sfx, msg, help) := TitleTemplate.mixedLoss datum
        sayOnce ("beamer:setbeamertemplate:title page:" ++ sfx) .W0363 msg pos (help := help)
        return some (#[], k)
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
        for (data, several) in rd.unplaced do
          let (sfx, msg, help) := TitleTemplate.unplacedLoss data several
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
    -- The translation the help text has been naming all along: a beamer
    -- colour element the engine has a role for *is* a `\palette` entry
    -- (`beamerColorRoles` carries the mapping and its source). The value
    -- side rides verbatim into `\palette`, where names and `!` mixes
    -- evaluate at the one resolving site (`Ir.Palette.resolve`).
    --
    -- What is not translated is named, and named *specifically*: an
    -- element with no role names that element, a key whose side has no
    -- role names the element and the key, and beamer's inheritance
    -- (`parent=`/`use=`) names itself — the engine has no palette
    -- inheritance, so an inherited value is a value nobody declared. A
    -- blanket "the engine does not have this construct" over thirteen
    -- distinct elements told the author nothing about which it dropped.
    let j := skipStar raws start
    let (args, k) := takeGroups raws j 2
    if h : args.size = 2 then
      let element := (rawSrc args[0]).trimAscii.toString
      match beamerColorRoles.lookup element with
      | none =>
        sayOnce ("beamer:setbeamercolor:" ++ element) .W0104
          s!"'\\setbeamercolor\{{element}}' names a beamer colour element the \
engine has no role for; skipped" pos
          (help := beamerNative.lookup "setbeamercolor")
        return some (#[], k)
      | some (fgRole, bgRole) =>
        let mut entries : Array String := #[]
        for e in (rawSrc args[1]).splitOn "," do
          match (e.splitOn "=").map (·.trimAscii.toString) with
          | [key, v] =>
            if key == "parent" || key == "use" then
              sayOnce ("beamer:setbeamercolor:" ++ element ++ ":" ++ key) .W0104
                s!"'\\setbeamercolor\{{element}}' inherits with '{key}'; the engine \
has no palette inheritance, so only declared values are taken" pos
                (help := beamerNative.lookup "setbeamercolor")
            else
              let role := if key == "fg" then fgRole
                else if key == "bg" then bgRole else ""
              if role.isEmpty then
                sayOnce ("beamer:setbeamercolor:" ++ element ++ ":" ++ key) .W0104
                  s!"'\\setbeamercolor\{{element}}' key '{key}' has no engine role; \
its value is skipped" pos
                  (help := beamerNative.lookup "setbeamercolor")
              else
                entries := entries.push s!"{role} = {v}"
          | _ => pure ()
        if entries.isEmpty then
          return some (#[], k)
        else
          let native := s!"\\palette\{ {String.intercalate ", " entries.toList} }"
          became s!"\\setbeamercolor\{{element}}" native pos
          return some (← synthAt native pos, k)
    else return none
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
    -- The other half of the same finding: the W0104 help named
    -- `\style{element}{ font = {...} }` and then dropped the declaration.
    -- beamer's font keys are TeX font commands already
    -- (`beamerFontKeys`), so the value side needs no vocabulary of its
    -- own — the commands compose in the order the author wrote them, and
    -- the engine invents no canonical order. `beamerFontElements` carries
    -- the element mapping and its source.
    let j := skipStar raws start
    let (args, k) := takeGroups raws j 2
    if h : args.size = 2 then
      let element := (rawSrc args[0]).trimAscii.toString
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
          -- A theme's own element is the font a template selects by name
          -- (`\usebeamerfont{<element>}`, beamerbasefont.sty), so it is
          -- also recorded for the one template reader the engine has: a
          -- read template that selects it withdraws this skip by its
          -- subject, and what the record could not take joins that
          -- template's own named loss. `size*`'s size rides apart, as the
          -- slot's own size.
          let mut font : TitleTemplate.Font := {}
          for e in (rawSrc args[1]).splitOn "," do
            match (e.splitOn "=").map (·.trimAscii.toString) with
            | [key, v] =>
              if beamerFontKeys.contains key then font := { font with cmds := font.cmds ++ v }
              else if key == "size*" then
                let gs := braceGroups v
                font := { font with size := gs[0]? }
                if gs.size > 1 then
                  let note := s!"the baselineskip of '{element}'"
                  font := { font with unread := font.unread.push note }
              else
                let note := s!"'{key}' of '{element}'"
                font := { font with unread := font.unread.push note }
            | _ => pure ()
          write fun st => { st with beamerFonts :=
            (st.beamerFonts.filter (·.1 != element)).push (element, font) }
        return some (#[], k)
      | some (target, styleKey) =>
        let mut cmds : String := ""
        for e in (rawSrc args[1]).splitOn "," do
          match (e.splitOn "=").map (·.trimAscii.toString) with
          | [key, v] =>
            if key == "parent" then
              sayOnce ("beamer:setbeamerfont:" ++ element ++ ":" ++ key) .W0104
                s!"'\\setbeamerfont\{{element}}' inherits with '{key}'; the engine has \
no font inheritance, so only declared commands are taken" pos
                (help := beamerNative.lookup "setbeamerfont")
            else if beamerFontKeys.contains key then
              cmds := cmds ++ v
            else
              -- Never pasted into the template: an unknown key's value
              -- would set as prose beside the element it was meant to size.
              sayOnce ("beamer:setbeamerfont:" ++ element ++ ":" ++ key) .W0104
                s!"'\\setbeamerfont\{{element}}' key '{key}' is not a beamer font key; \
its value is skipped" pos
                (help := beamerNative.lookup "setbeamerfont")
          | _ => pure ()
        if cmds.isEmpty then
          return some (#[], k)
        else
          let native := s!"\\style\{{target}}\{ {styleKey} = \{{cmds}} }"
          became s!"\\setbeamerfont\{{element}}" native pos
          return some (← synthAt native pos, k)
    else return none
  | "parbox" =>
    -- `\parbox{w}{t}` and `{minipage}{w}` are the same box: latex.ltx builds
    -- both through `\@iiiparbox`, and the manual's own difference is what a
    -- body may contain, not what the box measures. So the width is honoured
    -- rather than dropped — the environment carries it to `Ir.BoxWidth`
    -- through the one width reader — and `[pos]` options are noted where the
    -- environment notes its own (N0102), since a block-level box has no text
    -- baseline to sit against.
    let (declared, j) := takeOpts raws start 3
    let (args, k) := takeGroups raws j 2
    if declared then
      sayOnce "ctrl:parbox:pos" .N0102
        "'\\parbox' [pos] options are ignored: the box stands as a block, top-aligned"
        pos
    became "\\parbox" "\\begin{minipage}{<width>}...\\end{minipage}" pos
    -- The environment node directly, not synthesised source: the width group
    -- and the body are already parsed raws, and a `\begin` spelled as text
    -- would have to be re-parsed against its own `\end` to become an
    -- environment at all.
    let widthGroup : Array Raw := #[.group (args[0]?.getD #[]) pos]
    return some (#[.env "minipage" (widthGroup ++ (args[1]?.getD #[])) pos], k)
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
    let (_, j) := takeOpt raws start
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
  | "multicolumn" =>
    -- `\multicolumn{n}{align}{text}`: spans are not modelled, so the text
    -- fills one cell and cell alignment is its column's. Only the count and
    -- the alignment are consumed: `text` stays where it stands, so the walk
    -- rewrites it like any group — a `#1` inside a definition body is the
    -- definition's parameter, which a kept-but-unwalked group lost. What is
    -- dropped is named under the construct's own key, one per shape of
    -- loss, so a counted line is true of every site it counts: a count of 1
    -- loses only the alignment; a wider one loses the alignment too, and
    -- any cells after it in the row move left (none at a row's end, LaTeX's
    -- commonest span, where the table then pads the short row); a count
    -- that is not a numeral says no more than the one cell.
    let (gs, k) := takeGroups raws start 2
    let j := skipSpaces raws k
    match gs, raws[j]? with
    | #[n, _], some (.group _ _) =>
      match (rawSrc n).trimAscii.toString.toNat? with
      | some 1 =>
        sayOnce "ctrl:multicolumn:1" .W0337
          "'\\multicolumn{1}' alignment is not set: the cell takes its column's alignment" pos
      | some (_ + 2) =>
        sayOnce "ctrl:multicolumn" .W0337
          "'\\multicolumn' spans are not set: its text fills one cell in its column's \
alignment, and any later cells move left" pos
      | _ =>
        sayOnce "ctrl:multicolumn:unread" .W0337
          "'\\multicolumn' span is not a numeral the engine reads: its text fills one cell \
in its column's alignment" pos
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
      sayOnce ("ctrl:" ++ name) .W0104 msg pos (help := help)
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
      if let some why := note then
        discard s!"\\{name}" why name pos
      return some (#[], k)
    | none => return none

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
      diags := s0.diags.push (Diag.of .W0387
        s!"'\\{name}' was read and had no effect" (some ⟨st.file, pos⟩)
        (help := "\\allow{W0387} accepts the skip")
        (subject := some ("ctrl:" ++ name))) })

/-- Rewrite the control sequence `name` given what follows it. Returns the
replacement and how many following elements it consumed, or `none` to leave
the command alone. An empty replacement passes the silence guard
(`account`): the arms need not hand-account their no-ops, and a silent
drop is unrepresentable (`rewriteCtrl_accounts`). State-explicit so the
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
  if let some tok := literalReplace.lookup name then
    return some (#[tok pos], start)
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
          -- authoryear's round brackets and semicolons are natbib's own load
          -- values; the style's square-bracket row stays out.
          if s == "plainnat" then natbibDefer #["nobibstyle"] pos
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
    return some (out, k)
  | "documentclass" =>
    let (opt, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    let cls := rawSrc (args.getD 0 #[])
    if presentationClasses.contains cls then
      write fun st => { st with deck := true }
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
        -- `UprightFont = *-Medium` under `{Inter}` names "Inter-Medium".
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
  | "pagecolor" =>
    let (opt, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    if h : args.size = 1 then
      let value ← match opt with
        | some model => color model (rawSrc args[0]) pos
        | none => pure (some (rawSrc args[0]))
      match value with
      | some v => return some (← pageColor v pos, k)
      | none => return some (#[], k)
    else return none
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
        | some (some v) => some v.raws
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
      | some "belowcaptionskip" =>
        -- The caption's text side: in this engine that is the float
        -- separation (`floatsep`), not a caption property; the LaTeX
        -- default here is 0pt for the same reason.
        say .N0102 "'\\belowcaptionskip' is not a knob here: the caption's \
text side is the float separation ('\\tokens{ floatsep = ... }')" pos
        return some (#[], k)
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
    -- so they are its tokens; the short skips are never selected here
    -- (`Ir.displaySkipDefault`), so only the long ones are taken.
    if !xparse && cmd == "normalsize" then
      if let some (.group sbody _) := raws[js]? then
        let b := skipSpaces sbody 0
        if let some (.ctrl "@setfontsize" _) := sbody[b]? then
          let (fsArgs, afterFs) := takeGroups sbody (b + 1) 3
          if h : fsArgs.size ≥ 3 then
            if let (some sz, some ld) := (ptMacroArg fsArgs[1], ptMacroArg fsArgs[2]) then
              if sz > 0 && ld > 0 then
                let factor := (ld * 1000000 + sz * 600) / (sz * 1200)
                let skips := (readAssigns sbody afterFs).1.filterMap fun a =>
                  if !a.add && (paramSites.lookup a.name) matches some (.sizeReset (.token _))
                  then some s!"{a.name} = {lengthSrc a.value}" else none
                let native := s!"\\page\{ fontsize = {milliStr sz}pt, \
leading = {milliStr factor} }" ++
                  (if skips.isEmpty then "" else s!"\\tokens\{ {String.intercalate ", " skips.toList} }")
                write fun st => { st with listiKept := !resetsListi sbody }
                became "\\renewcommand{\\normalsize}" native pos
                return some (← synthAt native pos, js + 1)
    if name == "providecommand" && (← get).bound.contains cmd then
      let (_, k) := takeGroups raws j 1
      discard s!"\\providecommand\{\\{cmd}}"
        s!"'\\{cmd}' is already defined and the existing definition is kept"
        s!"providecommand:{cmd}" pos
      return some (#[], k)
    -- `\providecommand` of a name the engine itself defines: the command
    -- exists, so LaTeX's provide keeps it (usrguide, "Defining commands").
    -- Without this the venue shim `\providecommand{\section}{}` reached the
    -- definition gate as an empty redefinition and earned a W0361 for a
    -- construct LaTeX defines to be a no-op.
    if name == "providecommand" && (← get).provideKeeps.contains cmd then
      let (_, k) := takeGroups raws j 1
      discard s!"\\providecommand\{\\{cmd}}"
        s!"'\\{cmd}' is built in and the built-in stands" s!"providecommand:{cmd}" pos
      return some (#[], k)
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

/-- Silence is fidelity, the surface layer: a control word the dispatcher
consumed with an empty replacement is paid for — the diagnostics grew or a
state write happened — for *every* name, position, and state. Proved by
unfolding the dispatcher's tail and the guard (`account`) alone; the arms
(`rewriteCtrlAt` and everything under it) stay opaque, so no future arm
can break the statement. `_accounts` is the registered shape (AGENTS.md,
the suffix registry): an empty result is paid for by a diagnostic or a
write. -/
theorem rewriteCtrl_accounts (name : String) (pos : Pos) (raws : Array Raw)
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

/-- The group primitives, opener to closer: `\begingroup … \endgroup`
scopes exactly what a brace pair scopes (TeXbook ch. 24, "\begingroup"),
and `\bgroup … \egroup` is the brace pair itself (latex.ltx `\let\bgroup={`). -/
def groupPrimitives : List (String × String) :=
  [("begingroup", "endgroup"), ("bgroup", "egroup")]

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

/-- The delimited definitions the rewrite refuses (W0357), by name, with
their parameter texts: gathered whole tree, since a definition's uses
follow it and the refusal leaves the name undefined. -/
private def delimDefsLevel (xs : Array Raw)
    (out : Array (String × (Array DelimAtom × Array (Array DelimAtom)))) :
    Array (String × (Array DelimAtom × Array (Array DelimAtom))) := Id.run do
  let mut out := out
  for h : i in [0:xs.size] do
    if let .ctrl d _ := xs[i] then
      if d == "def" || d == "gdef" then
        if let some (.ctrl n _) := xs[i + 1]? then
          let params := ((xs.extract (i + 2) xs.size).toList.takeWhile
            fun r => !(r matches .group _ _)).toArray
          if let some sh := delimShape params then out := out.push (n, sh)
  return out

mutual

private def delimDefsRaw (out : Array (String × (Array DelimAtom × Array (Array DelimAtom)))) :
    Raw → Array (String × (Array DelimAtom × Array (Array DelimAtom)))
  | .group body _ => delimDefsList (delimDefsLevel body out) body.toList
  | .env _ body _ => delimDefsList (delimDefsLevel body out) body.toList
  | .math _ _ _ => out
  | .word _ _ => out
  | .space => out
  | .par _ => out
  | .ctrl _ _ => out
  | .sym _ _ => out
  | .verb _ _ _ => out

private def delimDefsList (out : Array (String × (Array DelimAtom × Array (Array DelimAtom)))) :
    List Raw → Array (String × (Array DelimAtom × Array (Array DelimAtom)))
  | [] => out
  | r :: rest => delimDefsList (delimDefsRaw out r) rest

end

/-- Every refused delimited definition in a tree (`delimDefsLevel`). -/
private def delimitedDefs (raws : Array Raw) :
    Array (String × (Array DelimAtom × Array (Array DelimAtom))) :=
  delimDefsList (delimDefsLevel raws #[]) raws.toList

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

/-- The signatures in force after the definer at `i`: its name's delimited
parameter text when it is a delimited `\def` or `\gdef`, and none otherwise. -/
private def sigsAfter (sigs : Array (String × (Array DelimAtom × Array (Array DelimAtom))))
    (xs : Array Raw) (i : Nat) (d n : String) :
    Array (String × (Array DelimAtom × Array (Array DelimAtom))) :=
  let kept := sigs.filter (·.1 != n)
  if d == "def" || d == "gdef" then
    let params := ((xs.extract (i + 2) xs.size).toList.takeWhile
      fun r => !(r matches .group _ _)).toArray
    match delimShape params with
    | some sh => kept.push (n, sh)
    | none => kept
  else kept

mutual

/-- Every use of a refused delimited definition spelled as its braced call
(`delimCall`), whole tree, in document order, before the rewrite walk: the
delimiter is the call's syntax, consumed as TeX consumes it, never ink. A
use reads the signature in force where it stands — the last definition of
its name met so far — so a later redefinition ends it. The definition's own
head is not a use. -/
-- conserves: none — a use's delimiters are syntax, not text.
private def delimCallsRaw (sigs : Array (String × (Array DelimAtom × Array (Array DelimAtom)))) :
    Raw → Raw × Array (String × (Array DelimAtom × Array (Array DelimAtom)))
  | .group body p =>
    let (b, sigs) := delimCallsList sigs body #[] body.toList 0 0
    (.group b p, sigs)
  | .env n body p =>
    let (b, sigs) := delimCallsList sigs body #[] body.toList 0 0
    (.env n b p, sigs)
  | .math d body p => (.math d body p, sigs)
  | .word s p => (.word s p, sigs)
  | .space => (.space, sigs)
  | .par p => (.par p, sigs)
  | .ctrl n p => (.ctrl n p, sigs)
  | .sym c p => (.sym c p, sigs)
  | .verb env s p => (.verb env s p, sigs)

private def delimCallsList (sigs : Array (String × (Array DelimAtom × Array (Array DelimAtom))))
    (xs : Array Raw) (out : Array Raw) : List Raw → Nat → Nat →
    Array Raw × Array (String × (Array DelimAtom × Array (Array DelimAtom)))
  | [], _, _ => (out, sigs)
  | _ :: rest, i, skip + 1 => delimCallsList sigs xs out rest (i + 1) skip
  | .ctrl d p :: rest, i, 0 =>
    match (if redefiners.contains d then definedCmd xs i else none) with
    | some n =>
      let sigs := sigsAfter sigs xs i d n
      match xs[i + 1]? with
      | some (.ctrl m q) =>
        delimCallsList sigs xs ((out.push (.ctrl d p)).push (.ctrl m q)) rest (i + 1) 1
      | _ => delimCallsList sigs xs (out.push (.ctrl d p)) rest (i + 1) 0
    | none =>
      match (sigs.find? (·.1 == d)).bind fun (_, sh) => delimCall xs i d p sh with
      | some (call, stop) => delimCallsList sigs xs (out ++ call) rest (i + 1) (stop - (i + 1))
      | none => delimCallsList sigs xs (out.push (.ctrl d p)) rest (i + 1) 0
  | r :: rest, i, 0 =>
    let (r', sigs) := delimCallsRaw sigs r
    delimCallsList sigs xs (out.push r') rest (i + 1) 0

end

/-- Glue a row of boxes can hold between two boxes: a space, or the fill
that takes what the boxes leave of the measure (`\hfill`, `\hfil`). A
paragraph break is not among them — it ends the line the boxes stand on. -/
private def rowGlue : Raw → Bool
  | .space => true
  | .ctrl "hfill" _ => true
  | .ctrl "hfil" _ => true
  | _ => false

/-- A minipage's width group and its content past it, and whether a
`[pos]`-family option stood before the width (classes.dtx §minipage:
`[pos][height][inner-pos]{width}`). `none` without a width group. -/
private def boxParts (body : Array Raw) : Option (Raw × Array Raw × Bool) :=
  let (opts, k) := takeOpts body 0 3
  let k := skipSpaces body k
  match body[k]? with
  | some (.group g gp) => some (.group g gp, body.extract (k + 1) body.size, opts)
  | _ => none

/-- Each run of minipages at one level whose separators are row glue holding
a fill becomes one `{columns}` row of `{column}`s of the widths the boxes
declare: LaTeX sets such boxes on one line with the fill between them
(`\hfill` is `\hskip 0pt plus 1fill`, TeXbook chapter 12), which is the
columns model's own leftover rule — the measure the declared widths leave
goes into equal gutters between the boxes. A box standing alone, a pair a
paragraph break or other content separates, and a pair only a space
separates are left as they stand. Returns the level and, for each row,
where it opened and whether a box carried `[pos]` options. -/
private def boxRows (rs : Array Raw) : Array Raw × Array (Pos × Bool) := Id.run do
  let mut out : Array Raw := #[]
  let mut rows : Array (Pos × Bool) := #[]
  let mut i := 0
  for _ in [0:rs.size + 1] do
    match (rs[i]? : Option Raw) with
    | none => break
    | some (.env "minipage" b p) =>
      match boxParts b with
      | none =>
        out := out.push (.env "minipage" b p)
        i := i + 1
      | some (w0, c0, o0) =>
        let mut cols : Array (Raw × Array Raw × Pos) := #[(w0, c0, p)]
        let mut opts := o0
        let mut j := i + 1
        for _ in [i + 1:rs.size + 1] do
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
          match rs[k]? with
          | some (.env "minipage" b2 p2) =>
            match boxParts b2 with
            | some (w, c, o) =>
              if fill then
                cols := cols.push (w, c, p2)
                opts := opts || o
                j := k + 1
              else break
            | none => break
          | _ => break
        if cols.size ≥ 2 then
          out := out.push (.env "columns"
            (cols.map fun (w, c, cp) => Raw.env "column" (#[w] ++ c) cp) p)
          rows := rows.push (p, opts)
          i := j
        else
          out := out.push (.env "minipage" b p)
          i := i + 1
    | some r =>
      out := out.push r
      i := i + 1
  return (out, rows)

/-- One level of rows, formed and named: each row is a translation onto the
columns model (N0100), and a `[pos]` option inside one is noted where the
row opens, since a row's boxes stand top-aligned. -/
private def boxRowEmit (rs : Array Raw) : M (Array Raw) := do
  let (out, rows) := boxRows rs
  for (p, opts) in rows do
    became "\\begin{minipage}…\\end{minipage}\\hfill\\begin{minipage}…"
      "one row of boxes, the fill between them" p (subject := some "env:minipage-row")
    if opts then
      sayOnce "env:minipage-row-options" .N0102
        "'minipage' [pos] options are ignored in a row of boxes: the boxes stand top-aligned" p
  return out

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
    let kids ← boxRowList #[] body.toList
    return .env n (← boxRowEmit kids) p
  | .math d body p => pure (.math d body p)
  | .word s p => pure (.word s p)
  | .space => pure .space
  | .par p => pure (.par p)
  | .ctrl n p => pure (.ctrl n p)
  | .sym c p => pure (.sym c p)
  | .verb env s p => pure (.verb env s p)

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
def presentationModes : List String := ["presentation", "beamer", "all"]

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
def modeSilencesPresentation (w : String) : Bool :=
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
theorem overprintAlt_exact (p : Pos) (tail : Array Raw) (sp : Raw) (content : Array Raw)
    (rest : List (Raw × Array Raw)) :
    overprintAlt p tail ((sp, content) :: rest) =
      #[.ctrl "alt" p, sp, .group content p, .group (overprintAlt p tail rest) p] := rfl

/-- The item is carried whole as the alternation's first alternative: what
the steps its own spec names show, and the only copy of it. -/
theorem overprintAlt_item_exact (p : Pos) (tail : Array Raw) (sp : Raw) (content : Array Raw)
    (rest : List (Raw × Array Raw)) :
    (overprintAlt p tail ((sp, content) :: rest))[2]? = some (.group content p) := rfl

/-- The spec reaches the elaborator as written, at the index its `\alt` arm
reads: a spec the step model cannot number is judged there, never here. -/
theorem overprintAlt_spec_id (p : Pos) (tail : Array Raw) (sp : Raw) (content : Array Raw)
    (rest : List (Raw × Array Raw)) :
    (overprintAlt p tail ((sp, content) :: rest))[1]? = some sp := rfl

/-- The last item's other alternative is the tail and nothing else: the
overlay no item names shows what stands last, never a second item beside the
first. With no tail — `#[]`, the shape a body of numbered items alone
plans — it shows nothing. -/
theorem overprintAlt_last_exact (p : Pos) (tail : Array Raw) (sp : Raw)
    (content : Array Raw) :
    (overprintAlt p tail [(sp, content)])[3]? = some (.group tail p) := rfl

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
theorem overprintNumbered_mem (items : Array (Raw × Array Raw))
    (it : Raw × Array Raw) (h : it ∈ overprintNumbered items) : it ∈ items :=
  (Array.mem_filter.mp h).1

/-- `_mem`: the last-resort item is one the body wrote too. -/
theorem overprintLoose_mem (items : Array (Raw × Array Raw))
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
theorem overprintPlan_accounts (body : Array Raw) (p : Pos) (repl : Array Raw)
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
private def overprintList : List Raw → Array Raw → M (Array Raw)
  | [], out => pure out
  | r :: rest, out => do
    let rs ← overprintRaw r
    overprintList rest (out ++ rs)

/-- Descend into a group or environment, so an overprint nested anywhere is
found. Split from the list walk so the recursion is structural on `Raw`, as
the idiom rewrite's own pair is. -/
private def overprintRaw : Raw → M (Array Raw)
  | .group body p => do return #[.group (← overprintList body.toList #[]) p]
  | .env "overprint" body p => do
    let body' ← overprintList body.toList #[]
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
  | .env n body p => do return #[.env n (← overprintList body.toList #[]) p]
  | r => pure #[r]

end

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
    write fun st => { st with bodyNext := 1 }
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
    let savedDef := (← get).inDef
    let savedGroup := (← get).inGroup
    let savedLens := (← get).lens
    write fun st => { st with bodyNext := 0, inDef := st.inDef || saved > 0, inGroup := true }
    let body' ← rewriteList (inBody || saved > 0) body #[] body.toList 0 0
    -- A group's assignments end with it (TeXbook ch. 24: an assignment is
    -- local to the group it stands in).
    write fun st => { st with bodyNext := saved - 1, inDef := savedDef, inGroup := savedGroup,
                              lens := savedLens }
    return .group body' p
  | .env n body p => do
    -- An `\input` wrapper switches the file its diagnostics name.
    match Parse.inputEnvFile? n with
    | some f =>
      let saved := (← get).file
      write fun st => { st with file := f }
      let body' ← rewriteList inBody body #[] body.toList 0 0
      write fun st => { st with file := saved }
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
        -- `\begin{document}` runs `\normalsize`, which sets the size's
        -- lengths again (size10.clo), so the preamble's values of them end.
        write fun st => { st with inDoc := true,
                                  lens := st.lens.filter fun e => !sizeReset e.1 }
        let body' ← rewriteList inBody body #[] body.toList 0 0
        write fun st => { st with inDoc := false }
        return .env n body' p
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
        write fun st => { st with inList := st.inList || listEnvs.contains n }
        let body' ← rewriteList inBody body #[] body.toList 0 0
        write fun st => { st with lens := st0.lens, inList := st0.inList }
        return .env n body' p
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

/-- Split the raws of a replayed hook body across the seam
`\begin{document}` is: the native declarations the preamble reads
(`hookPreambleSide`, with their optional argument and one group) to the
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
      let (_, k) := takeGroups raws j 1
      seamSplit raws rest (i + 1) (k - (i + 1))
        (pre ++ raws.extract i k, body)
    else
      seamSplit raws rest (i + 1) 0 (pre, body.push (.ctrl name pos))
  | r :: rest, i, 0, (pre, body) =>
    seamSplit raws rest (i + 1) 0 (pre, body.push r)

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
(`Elab.runRawsSpanned`), never as ambient state. -/
def rewrite (file : String) (raws : Array Raw) (provideKeeps : List String := [])
    (warned : Array String := #[]) :
    Array Raw × Array Diag × Array String :=
  let go : M (Array Raw) := do
    let raws ← condDocument raws
    -- After the conditionals: only a live pair is a group.
    let raws := pairGroupsList true #[] raws.toList
    let raws := if (delimitedDefs raws).isEmpty then raws
      else (delimCallsList #[] raws #[] raws.toList 0 0).1
    let raws ← resolveLoaded raws
    -- After the conditionals: only live hook bodies are collected.
    let raws ← collectDeferList #[] raws.toList
    let raws := (splitColumnsList raws.toList).toArray
    let raws ← overprintList raws.toList #[]
    let out ← rewriteList false raws #[] raws.toList 0 0
    -- After the idiom rewrite, so a `\parbox` is the box it became.
    let out ← boxRowList #[] out.toList
    let out ← boxRowEmit out
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
    write fun st => { st with inDoc := saved, file := savedFile, seam := false }
    let counters := (← get).preCounters
    let isBody : Raw → Bool
      | .env "document" _ _ => true
      | _ => false
    return match out.findIdx? isBody with
      | some i =>
        let tail := match out[i]? with
          | some (.env n dbody p) => #[Raw.env n (counters ++ bodySide ++ dbody) p]
          | some r => #[r]
          | none => #[]
        out.extract 0 i ++ running ++ preSide ++ tail ++ out.extract (i + 1) out.size
      | none => out ++ running ++ preSide ++ bodySide
  let st0 : St :=
    { file := file, provideKeeps := provideKeeps, warned := warned,
      boundaryOpen := !boundaryRefused raws,
      wholeDoc := raws.any (· matches .env "document" _ _), docFile := file }
  let (out, st) := go.run st0
  (out, st.diags, st.warned)

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

/-- **The name-refusal registry: every code that refuses a declaration by
name, with the file prefix that would have defined it.** The invariant behind
it is that a refusal asks the input path first, and the registry is what lets
that be *quantified* rather than restated per code — a refusal outside the
list is a refusal nobody checked.

Closed against the code list rather than kept by hand: a refusal carries the
name it refuses on `Diag.refused`, and every code owes a firing witness, so
the codes that refuse names are discoverable from the registry of codes
itself. `nameRefusalRegistryChecks` runs that closure in both directions — a
row whose code never carries a name is a stale row, and a code that carries
one without a row is the hole `\usetheme` fell through, refusable without
being enumerable.

The prefix is this module's because the candidate scan is: a package `foo`
would be defined by `foo.sty` and a theme `X` by `beamerthemeX.sty`. -/
def nameRefusalAsk : List (DiagCode × String) :=
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

/-- **The invariant this engine owes every declaration it can refuse by
name: it asks the input path first.** `\usetheme` was refusable — W0319,
"unknown theme", the document left with no palette at all — and offered no
candidate, so a theme file sitting beside the document was never opened and
one unloaded theme cost the document its whole colour design.

Two halves. The *structural* half holds by construction and needs no
theorem: `themeAsking` is one list, read by the candidate scan and by the
splice, so a slot cannot be asked for and then not spliced, or spliced under
a prefix the scan never offered. The *behavioural* half — every slot asks
for exactly its prefixed file, and no refusable-by-name declaration exists
outside the registry — is two statements: the first is proved below
(`themeAsking_candidates`, read through the argument layer rather than by
kernel reduction, which does not reach through these readers), the second
still owed (`Obligations.nameRefusals_asked`, which wants a declared
name-refusal channel on the diagnostic). `themeAskingChecks` keeps the
quantification running over the registry itself as a floor. -/
def localStyCandidates (raws : Array Raw) : Array String :=
  styCandList raws #[] raws.toList 0 0

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
    simp [takeOpt, hs, Id.run]
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
theorem themeAsking_candidates (nm : String) (pos : Pos) (hne : nm.trimAscii.toString = nm)
    (hnz : nm ≠ "") :
    ∀ p ∈ themeAsking,
      localStyCandidates #[.ctrl p.1 pos, .group #[.word nm pos] pos]
        = #[p.2 ++ nm] := by
  intro p hp
  simp only [themeAsking, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  all_goals exact localSty_theme _ _ nm pos rfl hne hnz (by decide) (by decide)


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
      -- A theme file named as a package floors on its shipped bundle, as
      -- the slot spelling does: the two spellings are one ask.
      if let some (_, pre, nm) := themeSlotOfPackage? p then
        splice := splice ++ bundleFloor pre nm pos
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
    let passed := ((opt.getD "").splitOn ",").map (·.trimAscii.toString)
    let floor := bundleFloor pre nm pos
    return some (floor.push
      (.env (Parse.inputEnv (p ++ ".sty")) (resolveStyOptions passed sraws) pos),
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
def applyLocalSty (raws : Array Raw) (stys : Array (String × Array Raw)) :
    Array Raw × Array (String × Option String × Pos) :=
  applyStyList stys raws #[] #[] raws.toList 0 0

private theorem spliceUse_empty (raws : Array Raw) (cn : String) (pos : Pos) (i : Nat) :
    spliceUse #[] raws cn pos i = none := rfl

private theorem spliceTheme_empty (raws : Array Raw) (pre : String) (pos : Pos) (i : Nat) :
    spliceTheme #[] raws pre pos i = none := rfl

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
theorem applyLocalSty_id (raws : Array Raw) : applyLocalSty raws #[] = (raws, #[]) := by
  rw [applyLocalSty, applyStyList_empty]
  simp

/-- What a spliced `.sty` yielded, counted after elaboration: a construct
was honoured when its translation note (N0100) carries the file, named
when a warning does, and a TeX internal refused when a demoted refusal
does — a note that kept its W0301/W0357/W0391 code is the demotion's
signature, and at this point in the run nothing else makes one (`\allow`
acceptance resolves later, in the driver). -/
def styCounts (sty : String) (diags : Array Diag) : Nat × Nat × Nat :=
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
def styRead (docFile sty : String) (pos : Pos) (diags : Array Diag) : Diag :=
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
def siUnits : List (String × String) :=
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
def siPrefixes : List (String × String) :=
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
  /-- Names the document defines; a defined `\num` is the document's. -/
  defined : Array String := #[]

/-- `\lstset`'s standing entries spliced ahead of a listing's option
head: the environment's own entries stand last, so they win at
elaboration — listings' own precedence. -/
private def injectLstOpts (st : TextSt) (s : String) : String :=
  if st.lstOpts.isEmpty then s else
  let joined := String.intercalate "," st.lstOpts.toList
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
-- text and consumes `\lstset` into the next listing's option head.
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
    else if n == "lstset" && !st.defined.contains n then
      let (args, k) := takeGroups raws (i + 1) 1
      let entries := (Decl.splitEntries (rawSrc (args.getD 0 #[]))).filterMap
        fun e => let e := e.trimAscii.toString
          if e.isEmpty then none else some e
      let st := { st with lstOpts := st.lstOpts ++ entries.toArray }
      textList loc st raws out rest (i + 1) (k - (i + 1))
    else if siCtrls.contains n && !st.defined.contains n then
      let (repl, k) ← siCtrl loc n pos raws (i + 1)
      textList loc st raws (out ++ repl) rest (i + 1) (k - (i + 1))
    else
      textList loc st raws (out.push (.ctrl n pos)) rest (i + 1) 0
  | .verb env s vpos :: rest, i, 0 =>
    let s := if env == "lstlisting" then injectLstOpts st s else s
    textList loc st raws (out.push (.verb env s vpos)) rest (i + 1) 0
  | r :: rest, i, 0 => do
    let (r, st) ← textRaw loc st r
    textList loc st raws (out.push r) rest (i + 1) 0

/-- Descend into groups and environments: `\lstset` in the preamble of an
`\input`ed file, or `\num` inside a cell, reads exactly as at top level.
The state threads through in flow order and out again. -/
private def textRaw (loc : Locale) (st : TextSt) : Raw → M (Raw × TextSt)
  | .group body p => do
    let (body, st) ← textList loc st body #[] body.toList 0 0
    return (.group body p, st)
  | .env n body p => do
    let (body, st) ← textList loc st body #[] body.toList 0 0
    return (.env n body p, st)
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

/-- Whether the pass has anything to do: a `\lstset` or a siunitx command
anywhere. A read-only scan, so the common document — which has neither —
never pays for the rebuilding walk (`scripts/bench.lean` is the check). -/
private def textNeededList : List Raw → Bool
  | [] => false
  | .ctrl n _ :: rest =>
    n == "lstset" || siCtrls.contains n || textNeededList rest
  | r :: rest => textNeededOne r || textNeededList rest

private def textNeededOne : Raw → Bool
  | .group b _ => textNeededList b.toList
  | .env _ b _ => textNeededList b.toList
  | _ => false

end

/-- The listings/siunitx pass, run right after `rewrite`: `\lstset` folds
into the listings that follow it, and the siunitx commands become their
spelled text under the document's own locale. Third in the document's
warn-once chain (`rewrite`'s docstring carries why the set travels): the
keys it receives are the ones `rewrite` fired, the keys it returns go on to
the elaborator. -/
def rewriteText (file : String) (raws : Array Raw) (warned : Array String := #[]) :
    Array Raw × Array Diag × Array String :=
  if !textNeededList raws.toList then (raws, #[], warned) else
  let loc := ((declaredTagList raws.toList).bind Locale.forTag).getD Locale.en
  let go : M (Array Raw) := do
    let (out, _) ← textList loc {} raws #[] raws.toList 0 0
    return out
  let (out, st) := go.run { file := file, warned := warned }
  (out, st.diags, st.warned)

end LeanTex.Core.Compat
