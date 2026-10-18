module

public import LeanTex.Core.Lex
public import LeanTex.Core.Parse
import LeanTex.Core.Marker
public import LeanTex.Core.Native
public import LeanTex.Core.PackageImports
import LeanTex.Core.Theme
import LeanTex.Core.Decl
import LeanTex.Core.KeyVal
import LeanTex.Core.Entries
import LeanTex.Core.PdfDate
public import LeanTex.Core.Ir
import LeanTex.Core.BeamerColor
public import LeanTex.Core.TitleTemplate
public import LeanTex.Core.BlockTemplate
public import LeanTex.Core.Tcolorbox
import LeanTex.Core.LoopProgress
import LeanTex.Core.EncodingOption
import LeanTex.Core.PdfObj
public import LeanTex.Core.TikzCommands
import LeanTex.Core.UnusedSetting
public import LeanTex.Core.Definer

namespace LeanTex.Core.Compat

open LeanTex.Core LeanTex.Core.Parse

/-! # LaTeX idioms, spelled natively

Each LaTeX idiom is rewritten into its native declaration before elaboration. -/

/-- Package interfaces the engine handles natively: loading
one draws a note, never a warning. -/
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
   "cleveref", "listings", "minted", "siunitx", "leantex",
   "algorithm2e", "algorithmicx", "algpseudocode", "algorithm", "lineno", "environ", "amsthm",
   "cancel", "animate", "markdown", "ulem", "tikz-cd", "colorspace", "blueprint"]

/-- An option item as one spelling, `key` or `key=value`, its braces and spaces removed. -/
public def optionSpelling (item : String) : String :=
  match KeyVal.entry item with
  | (k, some v) => s!"{k}={v}"
  | (k, none) => k

/-- The encodings that, as `fontenc`'s main one, set Latin input in another script's glyphs. -/
public def glyphEncodings : List String := ["OT2", "T3", "LGR", "OML", "OMS", "OMX"]

/-- The font encodings LaTeX's `fontenc` loads, Unicode's included. -/
public def fontencEncodings : List String :=
  ["TU", "T1", "OT1", "OT2", "OT3", "OT4", "OT6", "LY1", "TS1", "TS3", "T2A", "T2B", "T2C", "X2",
   "T3", "T4", "T5", "T7", "LGR", "OML", "OMS", "OMX", "U", "L7x", "IL2", "QX", "LCY"]

/-- Options of a native package without an option reader of its own that configure machinery the
engine runs as they ask, each with why; every other such option is a setting nothing reads. -/
public def packageOptionsInert : List (String × List (String × String)) :=
  let drivers (why : String) : List (String × String) :=
    ["dvips", "dvipdfm", "dvipdfmx", "dvisvgm", "pdftex", "luatex", "xetex"].map (·, why)
  [("inputenc", ["utf8", "utf8x", "ascii"].map (·, "the input is read as UTF-8")),
   ("fontenc", fontencEncodings.map (·, "text is set from Unicode faces, whatever encoding is named")),
   ("csquotes", [("autostyle", "quotes follow the language in force, as the option asks"),
     ("autostyle=true", "quotes follow the language in force, as the option asks"),
     ("autostyle=try", "quotes follow the language in force, as the option asks"),
     ("german=quotes", "German quotes are set as „…“, the style the option names"),
     ("english=american", "English quotes take their American form, as without the option")]),
   ("babel", [("shorthands=off", "the engine reads no shorthand characters, as the option asks")]),
   ("parskip", [("indent=0pt", "paragraphs are set flush, as without the option")]),
   ("graphicx", ("final", "images are drawn, as without the option") ::
     drivers "the engine writes its own output"),
   ("xcolor", [("natural", "colours ship in the model they are declared in"),
     ("hyperref", "link colours are read from hyperref's own keys"),
     ("usenames", "the option has had no effect since xcolor 2.11")] ++
     drivers "the engine writes its own output"),
   ("color", ("usenames", "the option has no effect") :: drivers "the engine writes its own output"),
   ("amsmath", [("reqno", "equation numbers stand on the right, as without the option"),
     ("sumlimits", "a sum's limits stand above and below it, as without the option"),
     ("namelimits", "an operator name's limits stand below it, as without the option"),
     ("nointlimits", "an integral's limits stand beside it, as without the option"),
     ("centertags", "a split equation's number is centred on it, as without the option")]),
   ("amssymb", [("psamsfonts", "the symbols are set from the math face")]),
   ("amsfonts", [("psamsfonts", "the symbols are set from the math face")]),
   ("url", [("hyphens", "a URL breaks after its hyphens here")]),
   ("xurl", [("hyphens", "a URL breaks after its hyphens here")]),
   ("fontspec", [("quiet", "the engine writes no TeX log"),
     ("no-math", "the math faces stand as declared, as the option asks")]),
   ("cleveref", [("english", "references are named in English, as without the option")]),
   ("siunitx", [("output-decimal-marker=.", "the decimal marker is a point, as without the option"),
     ("output-decimal-marker={.}", "the decimal marker is a point, as without the option")]),
   ("microtype", [("final", "the document is set in final mode, as without the option"),
     ("draft", "the features stay on: only 'disable=ifdraft' reads the flag"),
     ("disable=ifdraft", "the features stay on: the flag disables them only beside 'draft'"),
     ("disable=false", "the features stay on, as without the option"),
     ("activate", "the features stay on, as without the option"),
     ("activate=true", "the features stay on, as without the option"),
     ("activate=true,nocompatibility", "the features stay on, as without the option"),
     ("tracking=false", "no letterspacing is set, as without the option"),
     ("kerning=false", "no extra kerning is set, as without the option"),
     ("spacing=false", "interword spaces stay as the face sets them, as without the option"),
     ("verbose", "the engine writes no TeX log")]),
   ("listings", [("final", "listings are set, as without the option")]),
   ("minted", [("newfloat", "a listing float is set as without the option"),
     ("cache=false", "the engine keeps no minted cache"),
     ("finalizecache", "the engine keeps no minted cache"),
     ("frozencache", "the engine keeps no minted cache"),
     ("outputdir=*", "the engine writes no minted temporaries")]),
   ("nicefrac", [("nice", "the fraction is set as without the option")]),
   ("algorithm2e", [("english", "the keywords are English, as without the option")])]

/-- Beamer's colour elements, each mapped onto the palette roles its `fg=` and
`bg=` declare; an empty role is a side the engine names rather than drops. -/
private def beamerColorRoles : List (String × Option Ir.Role × Option Ir.Role) :=
  BeamerColor.roles

/-- Beamer's font elements, each mapped onto the styleable element and the
`\style` key that carries its font. -/
public def beamerFontElements : List (String × String × String) :=
  [("frametitle", "frametitle", "font"),
   ("standout", "standout", "font"),
   ("section title", "sectionpage", "font"),
   ("title", "titlepage", "font"),
   ("author", "titlepage", "author-font"),
   ("abstract title", "abstract", "font"),
   ("block title", "block", "font"),
   ("block title alerted", "alertblock", "font"),
   ("block title example", "exampleblock", "font")]

/-- The block-title fonts a shipped theme declares, which a document's
`\setbeamerfont` merges into. -/
private def themeBlockFont (theme element : String) (pos : Pos) : List (String × Array Raw) :=
  if theme == "moloch" && (element == "block title" || element == "block title alerted") then
    [(Ir.FontAxis.series.key, #[.ctrl "bfseries" pos]), (Ir.FontAxis.size.key, #[.ctrl "normalsize" pos])]
  else []

/-- Beamer's font axes in the order `\usebeamerfont` selects them. -/
private def beamerFontKeys : List String := Ir.FontAxis.all.map (·.key)

/-- Classes that are an `article` with different defaults. -/
private def articleClasses : List String := ["report", "book", "memoir", "letter"]

/-- Whether written class options ask for title pages, `notitlepage` winning as the classes declare
it last. -/
private def asksTitlePage (opts : List String) : Bool :=
  !opts.contains "notitlepage" && opts.contains "titlepage"

/-- The article-like classes whose default is a title page. -/
private def titlepageClasses : List String := ["report", "book"]

/-- Résumé classes, mapped onto the native `resume` class. -/
private def resumeClasses : List String :=
  ["moderncv", "res"]

/-- A class option's `\normalsize` `\baselineskip`, its size file's decimal points as TeX scans
them. -/
private def classNormalSkip (pt : Nat) : Int :=
  let milli := (Ir.sizeFileLeading (Dim.pt pt) 1000 "normalsize" * 1000 + 32768) / 65536
  (milli * 65536 + 500) / 1000

/-- The point size a standard class's options set `\normalsize` at: its one size option of 10, 11
or 12pt, else its record's size or 10pt; none past a size option of any other size. -/
public def classNormalPt (cls : String) (opts : List String) : Option Nat :=
  let sized (v : String) : Bool :=
    2 < v.length && v.endsWith "pt" && (v.dropEnd 2).toString.toList.all fun c => c.isDigit || c == '.'
  let sizes : List (Option Nat) := opts.filterMap fun o => match KeyVal.entry o with
    | (v, none) | ("fontsize", some v) =>
      if v == "10pt" then some (some 10) else if v == "11pt" then some (some 11)
      else if v == "12pt" then some (some 12) else if sized v then some none else none
    | _ => none
  let native := Ir.DocClass.ofString? cls
  if cls != "article" && !articleClasses.contains cls && native != some .koma then none
  else match sizes with
    | [some n] => some n
    | [] => some (((native.bind (·.record.fontSize)).map fun s => (s / Dim.pt 1).toNat).getD 10)
    | _ => none

/-- Font-selection packages whose whole documented effect is
naming families for the generic slots. -/
private def fontPackages : List (String × Array (String × String)) :=
  [("times", #[("body", "TeX Gyre Termes"), ("sans", "TeX Gyre Heros"), ("mono", "TeX Gyre Cursor")]),
   ("mathptmx", #[("body", "TeX Gyre Termes"), ("math", "TeX Gyre Termes Math")]),
   ("palatino", #[("body", "TeX Gyre Pagella"), ("sans", "TeX Gyre Heros"), ("mono", "TeX Gyre Cursor")]),
   ("mathpazo", #[("body", "TeX Gyre Pagella"), ("math", "TeX Gyre Pagella Math")]),
   ("helvet", #[("sans", "TeX Gyre Heros")]),
   ("courier", #[("mono", "TeX Gyre Cursor")]),
   ("libertine", #[("body", "Linux Libertine O"), ("sans", "Linux Biolinum O"),
     ("mono", "Linux Libertine Mono O")]),
   ("carlito", #[("sans", "Carlito")])]

/-- Where a LaTeX length parameter's value goes. -/
public inductive ParamSite where
  /-- A page property: `\page{ key = ... }`. -/
  | page (key : Native.PageKey)
  /-- A token an engine site reads under this name. -/
  | token (name : String)
  /-- `\leftmargin` at list depth `level`, which the class's
  `\@list` reads at every list. -/
  | listIndent (level : Nat)
  /-- Set again by `\normalsize` at `\begin{document}`, so a preamble value
  never reaches the body, whose site is `body`. -/
  | sizeReset (body : ParamSite)
  /-- Set again at every list by `\list` or the class's `\@listi`: a value from
  outside a list reaches no list. -/
  | listReset
  /-- LaTeX reads it where `what` says; no engine site does. -/
  | unmodelled (what : String)
  deriving Repr, BEq

private def listEnvs : List String := ["itemize", "enumerate", "description"]

/-- Environments whose bodies the elaborator reads as table cells. -/
public def tableEnvs : List String := ["tabular", "tabular*", "tabularx"]

/-- Math-mode entry environments, whose bodies belong to the math parser. -/
private def mathEnvs : List String :=
  ["equation", "equation*", "displaymath", "align", "align*", "gather", "gather*"]

/-- The tokens the page reads once, from the preamble's value. -/
private def pageTokens : List String := ["footins", "topskip", "partopsep"]

/-- The kernel and booktabs length parameters, each with its site; any other
name is a length of the document's own. -/
public def paramSites : List (String × ParamSite) :=
  [("parskip", .page .parskip),
   ("textwidth", .page .textwidth),
   ("textheight", .unmodelled "sets the text block's height under its top margin; the page here \
keeps its top and bottom margins equal"),
   ("headsep", .page .headsep),
   ("footskip", .page .footskip),
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

/-- The native spelling of a skipped beamer construct, named
in its warning's help. -/
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

public def presentationClasses : List String := ["beamer", "slides"]

/-- The packages a class loads itself: beamer loads both AMS packages unless its
options hold the `noamsthm` key. -/
public def classPackages (cls : String) (options : List String) : List String :=
  let disabled := options.any fun option =>
    String.ofList ((KeyVal.entry option).1.toList.filter (!·.isWhitespace)) == "noamsthm"
  if cls == "beamer" && !disabled then ["amsmath", "amsthm"] else []

public theorem classPackages_ams_agree (cls : String) (options : List String) :
    ("amsmath" ∈ classPackages cls options) ↔
      ("amsthm" ∈ classPackages cls options) := by
  dsimp only [classPackages]
  split <;> simp

/-- beamer's theme-loading commands, each with the file
prefix it asks the input path for. -/
@[expose] public def themeAsking : List (String × String) :=
  [("usetheme", "beamertheme"),
   ("usecolortheme", "beamercolortheme"),
   ("usefonttheme", "beamerfonttheme"),
   ("useinnertheme", "beamerinnertheme"),
   ("useoutertheme", "beameroutertheme")]

/-- `moloch` for its lineage's other names, `metropolis` and
`m`; any other name as written. -/
private def themeAlias (nm : String) : String :=
  if nm == "metropolis" || nm == "m" then "moloch" else nm

/-- A theme-family file name resolved to its slot, the
slot's prefix and the theme name. -/
public def themeSlotOfPackage? (p : String) : Option (String × String × String) :=
  themeAsking.findSome? fun (slot, pre) =>
    if p.startsWith pre && p.length > pre.length then
      some (slot, pre, (p.drop pre.length).toString)
    else none

/-- Where a deferred declaration replays: the end of the preamble or the opening
of `\begin{document}`. -/
private inductive DeferPoint where
  | endPreamble
  | beginDocument
deriving BEq, Repr

/-- The deferral table, one row per hook. -/
private def deferredHooks : List (String × DeferPoint) :=
  [("AtBeginDocument", .beginDocument), ("AtEndPreamble", .endPreamble)]

/-- The native declarations the preamble reads and the body refuses, where a
hook body's declaration half goes. -/
public def hookPreambleSide : List String := Decl.blockDeclarations ++ Decl.runningDeclarations

/-- The native declarations a compatibility help text may name. -/
public def nativeDeclarations : List String := hookPreambleSide ++ ["framefoot"]

/-- Constructs whose help text names an engine declaration the engine does not
translate, each with the reason it cannot. -/
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

/-- A definition the conditional pass can read: its
replacement text, its `\long` and `\protected` prefixes, and
an optional command's default and inner definition. -/
private structure CondVal where
  raws : Array Raw
  long : Bool
  prot : Bool
  arity : Nat := 0
  optional : Option (String × Array Raw) := none
  live : Bool := false
  serial : Nat := 0
  textSerial : Nat := 0
  /-- The line ends at the replacement text's braces, which
  TeX reads as spaces of the text. -/
  edges : Bool × Bool := (false, false)

/-- One change the conditional pass made to its definition
state, with what it replaced. -/
private inductive CondUndo where
  | bind (n : String) (prev : Option (Option CondVal))
  | flag (n : String) (prev : Option Bool)
  | len (n : String) (prev : Option Rat)

/-- Where the definition state stood when a group or environment opened. -/
private structure CondMark where
  undo : Nat
  globals : Nat
  lens : Nat
  picBound : Nat
  primitives : Nat

/-- A preamble definition whose text went out without what
only a use decides. -/
private structure CondPending where
  name : String
  serial : Nat
  file : String
  pos : Pos

/-- Package and class declarations read by `condList`, with
the bodies the loader admitted. -/
private structure LoadSet where
  pkgs : Array (String × Option (Array String)) := #[]
  passed : Array (String × Array String) := #[]
  /-- Bodies already admitted, including local files still executing. -/
  imports : PackageImports.Loads := []
  /-- Option passes replayed at their execution point, so a late pass cannot
  alter an earlier native load. -/
  rewritePassed : Array (String × Array (String × Array Raw)) := #[]
  /-- Class option passes, replayed at their execution point. -/
  rewriteClassPassed : Array (String × Array String) := #[]
  cls : Option (String × Array String) := none
  clsPassed : Array (String × Array String) := #[]
  deriving Repr, BEq, Inhabited

/-- One TeX parameter assignment as TeX scans it: the parameter, whether the
value adds to it, and the value's raws. -/
private structure TexAssign where
  name : String
  add : Bool
  value : Array Raw
  deriving Repr

/-- hyperref's link colouring as its options and each
`\hypersetup` accumulate. -/
private structure LinkSetup where
  colorlinks : Bool := false
  link : String := "red"
  url : String := "magenta"
  cite : String := "green"
  deriving Repr

/-- hyperref's link keys, each with how it reads its value into the setup. -/
private def linkKeys : List (String × (LinkSetup → String → LinkSetup)) :=
  [("colorlinks", fun l v => { l with colorlinks := v != "false" }),
   ("hidelinks", fun l _ => { l with colorlinks := false }),
   ("linkcolor", fun l v => { l with link := v }),
   ("urlcolor", fun l v => { l with url := v }),
   ("citecolor", fun l v => { l with cite := v }),
   ("allcolors", fun l v => { l with link := v, url := v, cite := v })]

/-- The hyperref link keys the setup reads. -/
public def hyperrefLinkKeys : List String := linkKeys.map (·.1)

/-- One hyperref key read into the setup; `none` for a key
that sets no link colour. -/
private def LinkSetup.read (l : LinkSetup) (k v : String) : Option LinkSetup :=
  (linkKeys.lookup k).map (· l v)

/-- The setup as native settings: each link kind's colour style under `colorlinks`, none otherwise. -/
private def LinkSetup.native (l : LinkSetup) : Array Native.Setting :=
  if l.colorlinks then
    #[.style "link" #[("color", l.link)], .style "url" #[("color", l.url)],
      .style "cite" #[("color", l.cite)]]
  else #[]

/-- Written tokens indexed before execution; generated commands inherit the
written call's coordinates and spelling. -/
public abbrev SourceTriggers := Std.HashMap (String × Nat × Nat) String

/-- The written token at an original source coordinate; `none` where the
coordinate is not source-mapped. -/
@[expose] public def SourceTriggers.writtenAt (sources : SourceTriggers) (file : String)
    (pos : Pos) : Option String :=
  if pos.sourceMapped then sources[(file, pos.line, pos.col)]? else none

/-- A downstream diagnostic with its written trigger restored from lexical
evidence; a loss about a place takes none. -/
@[expose] public def SourceTriggers.attribute (sources : SourceTriggers) (d : Diag) : Diag :=
  { d with trigger := if d.kind.namesPlace then d.trigger else
      ((d.span.bind fun s =>
        sources.writtenAt s.file s.pos).bind Diag.Spelling.ofWritten?).orElse (fun _ => d.trigger) }

public theorem SourceTriggers.attribute_record_exact (sources : SourceTriggers) (d : Diag) :
    { sources.attribute d with trigger := d.trigger } = d := by rfl

public theorem SourceTriggers.attribute_fixed_point (sources : SourceTriggers) (d : Diag) :
    sources.attribute (sources.attribute d) = sources.attribute d := by
  unfold SourceTriggers.attribute
  by_cases hp : d.kind.namesPlace = true
  · simp [hp]
  · cases (d.span.bind (fun s => sources.writtenAt s.file s.pos)).bind
      Diag.Spelling.ofWritten? <;> simp [hp]

public theorem SourceTriggers.attribute_unmapped_id (sources : SourceTriggers) (d : Diag)
    (h : ∀ s, d.span = some s → s.pos.sourceMapped = false) :
    sources.attribute d = d := by
  have absent : (d.span.bind fun s => sources.writtenAt s.file s.pos) = none := by
    cases hs : d.span with
    | none => simp
    | some s => simp [SourceTriggers.writtenAt, h s hs]
  unfold SourceTriggers.attribute
  rw [absent]
  simp

mutual

/-- Lexical evidence captured before compatibility consumes
or synthesizes commands. -/
-- conserves: none — an index of the parsed surface
private def sourceTriggers (file : String) (acc : SourceTriggers) :
    List Raw → SourceTriggers
  | [] => acc
  | r :: rest => sourceTriggers file (sourceTrigger file acc r) rest

private def sourceTrigger (file : String) (acc : SourceTriggers) : Raw → SourceTriggers
  | .ctrl _ p | .verb _ _ p | .sym _ p =>
    match p.command with
    | some command =>
      if Diag.constructSpelling command then acc.insertIfNew (file, p.line, p.col) command
      else acc
    | none => acc
  | .word _ _ => acc
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

/-- A file read reached by the bounded macro evaluator. -/
public structure InputRequest where
  command : String
  file : String
  pos : Pos
  /-- The call token's position, distinct from a macro's attributed use site. -/
  callPos : Pos
  /-- The executed operand slice that filename, options and the style-file
  candidate scan all read. -/
  operands : Array Raw
  deriving Repr, BEq

/-- An actual reader call and whether it supplied parsed input. -/
public structure InputAttempt where
  request : InputRequest
  answered : Bool
  deriving Repr, BEq

/-- The walk's place relative to an environment definition's `[default]`. -/
private inductive DefaultAt where
  | none
  | awaiting
  /-- Inside the default, its text replacement text as a body's is; `outerDef` the walk's own. -/
  | inside (outerDef : Bool)
  deriving Repr, BEq, Inhabited

/-- A listing default the document declares: its command, its lexer's layer, its site and file,
and whether a listing after it has read it. -/
private structure ListingDefault where
  reader : String
  lang : Option String
  pos : Pos
  file : String
  read : Bool := false

/-- A beamer template the preamble installs, read typed: a block kind's shape on the element it
styles, its rules painted by the palette entries it names, or the title page; each with its site. -/
public inductive TemplateDecl where
  | block (element : String) (read : BlockTemplate.Read) (colors : Array String) (file : String)
      (pos : Pos)
  | titlePage (read : TitleTemplate.Read) (file : String) (pos : Pos)

private structure St where
  file : String
  diags : Array Diag := #[]
  sourceTriggers : SourceTriggers := {}
  inputAttempts : Array InputAttempt := #[]
  /-- Running-content slots gathered across `\ihead`/`\chead`/`\ohead`: 0 inner,
  1 centre, 2 outer, a repeat replacing. -/
  head : Array (Nat × Array Raw) := #[]
  foot : Array (Nat × Array Raw) := #[]
  runPos : Pos := { line := 1, col := 1 }
  runFrom : Nat := 1
  /-- Whether the counter resets after the title page:
  article.cls does so only in oneside mode. -/
  titlepageReset : Bool := true
  /-- Upcoming groups that are macro bodies, where `#k` names a parameter. -/
  bodyNext : Nat := 0
  /-- environ's environments whose code never places
  `\BODY`, with their argument signatures. -/
  discardEnvs : Array (String × String) := #[]
  /-- Where the walk stands with an environment definition's default, whose groups are no body of
  the definition. -/
  defaultAt : DefaultAt := .none
  /-- The environments a body definition left unapplied: the signature their uses' arguments
  follow, and whether the definition discards the body. -/
  refusedEnvs : Array (String × String × Bool) := #[]
  /-- The environments the preamble's definitions lowered here define. -/
  definedEnvs : Array String := #[]
  /-- The first of paracol's two column shares, in per mille. -/
  paracolRatio : Nat := 500
  /-- Inside a paracol flow, whose close splits its switching commands. -/
  inParacol : Bool := false
  /-- A `\usetheme` was seen, so `\alert` maps to the theme's alert colour. -/
  themed : Bool := false
  /-- The shipped theme the deck names, whose font
  declarations `themeBlockFont` reads. -/
  beamerTheme : String := ""
  /-- A theme was named, in any spelling, so the slides
  class's default bundle steps aside. -/
  themeNamed : Bool := false
  /-- The declared class produces a presentation, which a beamer mode
  specification is read against. -/
  deck : Bool := false
  /-- The class options the class leaves to the packages that take them, as LaTeX offers global
  options. -/
  globalOffered : Array String := #[]
  /-- The font slots a fontspec or babel declaration has
  named so far, in preamble order. -/
  facesDeclared : Array String := #[]
  /-- The main language's BCP 47 tag from babel's options, which `\enquote`
  reads its quotes through. -/
  mainLang : String := "en"
  /-- The option the first `inputenc` load names, the
  encoding every file reads in. -/
  inputenc : Option String := none
  /-- babel's main language as its options spell it, which biblatex's
  `language=autodetect` reads. -/
  babelMain : Option String := none
  /-- biblatex is loaded, so a later babel load hands it the main language. -/
  biblatexLoaded : Bool := false
  /-- Inside the document environment, where a preamble declaration is a
  placement defect (W0340). -/
  inDoc : Bool := false
  /-- Inside a definition body, where a construct's meaning
  is decided at its use. -/
  inDef : Bool := false
  /-- Inside an environment's begin or end code, which the elaborator expands at each use. -/
  envCode : Bool := false
  /-- Upcoming groups that are an environment's begin or end code. -/
  envNext : Nat := 0
  /-- Replaying a `\begin{document}` hook body, whose
  content goes to the body side. -/
  seam : Bool := false
  /-- Inside a brace group of the walk, where a declaration
  ends with the group. -/
  inGroup : Bool := false
  /-- Inside a list environment's body, where a list
  parameter spaces that one list. -/
  inList : Bool := false
  /-- The rewrite is of a whole document rather than of a
  value's text read on its own. -/
  wholeDoc : Bool := false
  /-- The file the rewrite was asked for; a site in any
  other stands in an included file. -/
  docFile : String := ""
  /-- Counter commands at the preamble's top level, moved to
  where the body starts. -/
  preCounters : Array Raw := #[]
  /-- The list levels whose parameter macro the preamble redefined as
  assignments, with each definition's site. -/
  listDefs : Array (Nat × Pos × Array TexAssign) := #[]
  /-- The document's `\normalsize` leaves `\@listi` as the preamble set it. -/
  listiKept : Bool := false
  /-- The preamble's assignments to a parameter a list level sets again, with
  spelling, file and site. -/
  listResets : Array (String × String × String × Pos) := #[]
  /-- At the top level of a `tabular` body, where the elaborator sets a
  `\multicolumn` as a span. -/
  tableTop : Bool := false
  /-- At the top level of a definition body, where a `\multicolumn` opens the
  cell its use stands in. -/
  defTop : Bool := false
  /-- The lengths as the preamble left them, taken where the
  document environment opens. -/
  preLens : Option (Array (String × String)) := none
  /-- The text block's measure is one the elaborator can
  read in the preamble. -/
  measureKnown : Bool := false
  /-- The declared class's page model is the flow model,
  whose text block is the engine's. -/
  flowPage : Bool := true
  /-- Constructs already warned about. -/
  warned : Array String := #[]
  /-- Every control word the conditional pass has seen bound, with its
  parameterless value when readable. -/
  binds : Std.HashMap String (Option CondVal) := {}
  /-- `\newif` flags by base name, with the value the last
  `\Xtrue`/`\Xfalse` gave. -/
  flags : Std.HashMap String Bool := {}
  /-- The save stack: each change to `binds`, `flags` and `exactLens` with what it replaced,
  undone when its group closes. -/
  undo : Array CondUndo := #[]
  /-- Every global definition, in the order made. -/
  globals : Array (String × Option CondVal) := #[]
  /-- Every global length assignment, in the order made. -/
  lenGlobals : Array (String × Option Rat) := #[]
  /-- Live primitive group pairs, whose save marks cross
  macro and input boundaries. -/
  primitiveScopes : Array (String × CondMark) := #[]
  /-- The names the picture being walked binds for itself,
  which the picture evaluates. -/
  picBound : Array String := #[]
  /-- The count of definitions the conditional pass has recorded, the clock
  `CondVal.serial` reads. -/
  serial : Nat := 0
  macroClock : Nat := 0
  /-- Where the macro being expanded is used, the site its
  decisions are named at. -/
  useSite : Option Pos := none
  /-- The conditional pass is inside a picture, which reads
  a document macro at its own site. -/
  inPicture : Bool := false
  /-- A prepared title becomes inline content, so readable definitions execute
  without emitting their syntax. -/
  materializeTitle : Bool := false
  /-- The document body has begun, so a definition is read where it is made. -/
  condInDoc : Bool := false
  /-- Collection has ended, so a hook met during replay is read in place. -/
  condReplaying : Bool := false
  /-- The opening `\ignorespaces` scan of `\document`: expand readable commands
  and discard spaces until a nonexpandable token. -/
  ignoreSpaces : Bool := false
  /-- Preamble definitions whose live texts the elaborator reads itself, settled
  at the preamble's end. -/
  pending : Array CondPending := #[]
  /-- The macro whose definition is being settled, whose
  decisions are named as the definition's. -/
  settling : Option String := none
  /-- A preamble block template's own macros, which the template reader runs
  where the template stands. -/
  templateCode : Array String := #[]
  /-- The definitions and flags in force where the body begins, which a block's
  templates run against. -/
  templateBinds : Std.HashMap String (Option CondVal) := {}
  templateFlags : Std.HashMap String Bool := {}
  /-- The control words the block templates reach. -/
  templateNames : Array String := #[]
  /-- Template names whose meaning or flag changed after the body began. -/
  templateDrift : Array String := #[]
  /-- The next definition body is a block template's own
  macro's: translated, naming nothing. -/
  quietNext : Bool := false
  /-- The conditional pass reads a spliced file's own top level, where a live
  `\endinput` ends the file. -/
  fileTop : Bool := false
  /-- The value source each length holds as the rewrite last set it. -/
  lens : Array (String × String) := #[]
  /-- Each allocated length's exact value in inches where the conditional pass stands, scoped as
  TeX scopes it, and absent where the pass cannot follow its last assignment. -/
  exactLens : Std.HashMap String Rat := {}
  /-- The length registers the document allocates with `\newlength`, the only ones the conditional
  pass follows. -/
  newLengths : Std.HashSet String := {}
  /-- The controls each document environment's code assigns, which run where it opens. -/
  envAssigns : Std.HashMap String (Array String) := {}
  /-- The dimen registers the document allocates with `\newdimen`. -/
  allocated : Array String := #[]
  /-- The page boxes the page-attribute assignments leave, by native key. -/
  pageBoxes : Array (Native.PageKey × String) := #[]
  /-- Their native declaration, which goes out once at the preamble's end. -/
  pageAttr : Array Raw := #[]
  /-- Token sites assigned directly in this scope. -/
  localLengths : Array String := #[]
  /-- Command names the rewrite walk has bound so far, in document order. -/
  bound : Array String := #[]
  /-- Whether the document defines `\only` and `\alt` itself. -/
  userOverlays : Bool × Bool := (false, false)
  /-- The counter names the document's counter commands read, its included files' too. -/
  countersRead : Std.HashSet String := {}
  /-- Whether an article's author asked for a title page, which its title and abstract lack. -/
  titlePageAsked : Bool := false
  /-- biblatex's declared resources (`\addbibresource`). -/
  bibResources : Array String := #[]
  /-- The record name biblatex's style option mapped to, emitted beside the
  synthesized `\bibliography`. -/
  bibStyle : Option String := none
  /-- hyperref's link colouring as declared so far. -/
  links : LinkSetup := {}
  /-- The ICC profile `\DocumentMetadata`'s `colorprofiles` names for the PDF/X output intent. -/
  intentProfile : Option String := none
  /-- Names the caller declares the engine renders or reserves, which the
  provision definers keep. -/
  provideKeeps : List String := []
  /-- Built-in names whose every definition the engine ignores whole: commands by name,
  environments as `Tcolorbox.bindingName`. -/
  ignoredDefs : List String := []
  /-- The `\baselineskip` the class set the strut box at, while nothing the preamble has run since
  may have set it again. -/
  strutSkip : Option Int := none
  /-- State mutations performed through `write`, which with `diags.size` the
  dispatcher's silence guard reads. -/
  writes : Nat := 0
  /-- The boundary door is open unless a
  `\pictures{ tool = none }` refusal stands. -/
  boundaryOpen : Bool := true
  /-- Hook bodies collected by the deferral pass, in declaration order, with
  replay point and declaring file. -/
  deferred : Array (DeferPoint × String × Pos × Array Raw) := #[]
  /-- The loads the shared conditional walk has read so far. -/
  loads : LoadSet := {}
  /-- Native spacers appended to the ordinary block-begin
  template in the preamble. -/
  beamerBlockBegin : Array Raw := #[]
  /-- Local field definitions shared by native element
  styles and template font selection. -/
  beamerFonts : Array (String × List (String × Array Raw)) := #[]
  /-- A global numbered footer, read at the document seam
  after its font declarations. -/
  beamerFootline : Option (String × Pos × Array Raw) := none
  /-- The font and footer fields saved at each preamble group primitive. -/
  beamerScopes : List (String × Array (String × List (String × Array Raw)) ×
    Option (String × Pos × Array Raw)) := []
  /-- Successful captures, which alone justify removing an
  otherwise empty preamble group. -/
  beamerCaptures : Nat := 0
  /-- beamer's block templates the preamble installs, by element, read as pairs
  where the preamble ends. -/
  beamerTemplates : Array (String × String × Pos × Array Raw) := #[]
  /-- The templates read, handed to the elaborator typed. -/
  templates : Array TemplateDecl := #[]
  /-- Named block templates a `\setbeamertemplate{element}[name]` installs. -/
  beamerTemplateDefs : Array ((String × String) × Array Raw) := #[]
  /-- The families declared beside the three slots, in the
  order the elaborator assigns them. -/
  fontFamilies : Array String := #[]
  /-- enumitem's stored settings by scope (kind, level) as native style entries. -/
  setlists : Array ((Option String × Option Nat) × Array (String × Native.StyleValue)) := #[]
  /-- enumitem's stored vertical keys by scope, as native spacing entries (`Ir.listSetKeys`). -/
  listSpacings : Array ((Option String × Option Nat) × Array (String × String)) := #[]
  /-- The listing defaults the document declares, in the order the text pass meets them. -/
  listingDefaults : Array ListingDefault := #[]
  /-- The source of each value a construct the walk refused carried, which still names what it
  names. -/
  mentions : Array String := #[]
  /-- The raws the walk leaves alone, each returning at its place after the rewrite. -/
  kept : Array (Array Raw) := #[]

private abbrev M := StateM St

/-- The markdown package's options the engine reads, `citations` and `hybrid` as LaTeX's package
reads them, and every other option as written. -/
public structure MarkdownOptions where
  citations : Option Bool := none
  hybrid : Option Bool := none
  others : Array String := #[]

/-- Option text as the markdown package reads its keys, a key alone true. -/
public def MarkdownOptions.read (opts : String) : MarkdownOptions :=
  (KeyVal.items opts).foldl (init := {}) fun acc item =>
    let item := item.trimAscii.toString
    if item.isEmpty then acc else
    let (k, v) := KeyVal.entry item
    let flag : Option Bool := match v.map (·.trimAscii.toString) with
      | none | some "true" => some true
      | some "false" => some false
      | some _ => none
    match k.trimAscii.toString, flag with
    | "citations", some b => { acc with citations := some b }
    | "hybrid", some b => { acc with hybrid := some b }
    | _, _ => { acc with others := acc.others.push item }

/-- The commands whose execution asks the driver's reader, in source order, for a file. -/
public def inputCommands : List String :=
  ["input", "include", "markdownInput", "inputminted", "inputlean"]

/-- The actual call offered to the driver's candidate and splice readers. -/
@[expose] public def InputRequest.call (request : InputRequest) : Array Raw :=
  #[.ctrl request.command request.callPos] ++ request.operands

/-- The execution state at a file read, which only
`resumeInput` can run a fragment against. -/
public structure InputContext where
  private state : St

/-- Completed reads, including reads made while an answer was resumed. -/
public def InputContext.inputAttempts (context : InputContext) : Array InputAttempt :=
  context.state.inputAttempts

/-- An answer the walk leaves alone: its place, at `pos`, and the context keeping its raws. -/
public def InputContext.keep (context : InputContext) (raws : Array Raw) (pos : Pos) :
    Array Raw × InputContext :=
  (#[Parse.keptRaw context.state.kept.size { pos with origins := [] }],
    { state := { context.state with kept := context.state.kept.push raws } })

/-- A file reader whose parsed answer runs in the requesting context; `none`
leaves the original call. -/
public abbrev InputReader (m : Type → Type) :=
  InputRequest → InputContext → m (Option (Array Raw) × InputContext)

/-- The reader's answer accepted unchanged, with a receipt of the exact call. -/
public def finishInput (request : InputRequest)
    (response : Option (Array Raw) × InputContext) :
    Option (Array Raw) × InputContext :=
  (response.1, { state := { response.2.state with
    inputAttempts := response.2.inputAttempts.push ⟨request, response.1.isSome⟩ } })

/-- The evaluator's file-effect door, making every receipt
from the request and the answer returned. -/
public def dispatchInput [Monad m] (reader : InputReader m) (request : InputRequest)
    (context : InputContext) : m (Option (Array Raw) × InputContext) := do
  return finishInput request (← reader request context)

public theorem finishInput_attempts_exact (request : InputRequest)
    (response : Option (Array Raw) × InputContext) :
    (finishInput request response).2.inputAttempts =
      response.2.inputAttempts.push ⟨request, response.1.isSome⟩ := by rfl

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

/-- The one door for a state mutation: `f`, then the `writes` bump. -/
private def write (f : St → St) : M Unit :=
  modify fun st => { f st with writes := st.writes + 1 }

/-- Records the first `inputenc` load's option as the encoding in force. -/
private def recordInputenc (options : String) : M Unit := do
  if (← get).inputenc.isNone then
    write fun st => { st with inputenc := some ((Encoding.lastOption? options).getD "utf8") }

private theorem write_eq (f : St → St) :
    write f = fun st => ((), { f st with writes := st.writes + 1 }) := by rfl

/-- Restores the definitions a group or environment scopes at its close: beamer's fonts and
templates, and the environments defined, discarding their bodies or left unapplied. -/
private def closeScope (saved : St) (result : α × St) : α × St :=
  (result.1, (write fun st => { st with
    beamerFonts := saved.beamerFonts
    beamerFootline := saved.beamerFootline
    beamerScopes := saved.beamerScopes
    beamerTemplates := saved.beamerTemplates
    beamerTemplateDefs := saved.beamerTemplateDefs
    discardEnvs := saved.discardEnvs
    refusedEnvs := saved.refusedEnvs
    definedEnvs := saved.definedEnvs
    defaultAt := saved.defaultAt }) result.2 |>.2)

private def withScope (act : M α) : M α := fun st =>
  closeScope st (act st)

/-- Restores at an argument's close what every group's close restores but the environment
definitions, which an argument's braces do not scope. -/
private def closeArgScope (saved : St) (result : α × St) : α × St :=
  (result.1, (write fun st => { st with
    beamerFonts := saved.beamerFonts
    beamerFootline := saved.beamerFootline
    beamerScopes := saved.beamerScopes
    beamerTemplates := saved.beamerTemplates
    beamerTemplateDefs := saved.beamerTemplateDefs
    defaultAt := saved.defaultAt }) result.2 |>.2)

/-- A group's walk, told whether the group stands inside a definition's default, whose groups are
no body of the definition, and the bodies the walk still awaits; an argument's group scopes no
environment definition. -/
private def withGroupScope (arg : Bool) (act : Bool → Nat → M α) : M α := fun st =>
  (if arg then closeArgScope else closeScope) st
    (act (st.defaultAt matches .inside _) st.bodyNext { st with defaultAt := .none })

/-- Whether a group the walk reaches after `out` may be an argument, whose braces TeX does not
scope: past blanks and at most nine groups, an optional argument or a control word, neither `\:`,
a marker taking none, nor one of TeX's grouping primitives. -/
private def argGroupAt (out : Array Raw) : Bool := Id.run do
  let mut k := out.size
  for _ in [0:20] do
    if k == 0 then return false
    match out[k - 1]? with
    | some .space | some (.group _ _) => k := k - 1
    | some (.ctrl n _) =>
      return n != ":" && (Marker.readingOf? n).all (·.takesGroup) &&
        !["begingroup", "endgroup", "bgroup", "egroup", "relax"].contains n
    | some (.sym ']' _) => return true
    | _ => return false
  return false

/-- Enters the document body: `\normalsize` resets the size-owned lengths. -/
private def openDocumentBody : M Unit :=
  write fun st =>
    let lens := st.lens.filter fun e => !sizeReset e.1
    { st with inDoc := true, lens := lens, preLens := st.preLens.orElse fun _ => some lens }

private def closeDocumentBody (pos : Pos) (result : Array Raw × St) : Raw × St :=
  (.env "document" result.1 pos,
    (write fun st => { st with inDoc := false }) result.2 |>.2)

/-- The document environment's body call and return. -/
private def rewriteDocumentBody (body : M (Array Raw)) (pos : Pos) : M Raw := fun st =>
  closeDocumentBody pos (body (openDocumentBody st).2)

/-- The TeX82 primitive control words. -/
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

/-- Whether a control word is a TeX internal: an `@`-name, an engine marker or a TeX primitive. -/
public def texInternal (name : String) : Bool :=
  name.contains '@' || (Marker.read? name).isSome || texPrimitives.contains name

/-- Whether a control word is a LaTeX internal or an engine marker, whose `{...}` arguments are
code. -/
public def codeInternal (name : String) : Bool :=
  name.contains '@' || (Marker.read? name).isSome

/-- Whether a site in `file` is package code rather than the
document's own text. -/
public def packageFile (file : String) : Bool :=
  file.endsWith ".sty" || file.endsWith ".cls"

/-- A refusal of `name` at a site in `file` demotes exactly when the site is
package code and the name a TeX internal. -/
public def styInternal (file name : String) : Bool :=
  packageFile file && texInternal name

mutual

-- conserves: none — the result is the files the walk enters
private def packageInputsList (owned : Bool) (acc : Array String) : List Raw → Array String
  | [] => acc
  | r :: rest => packageInputsList owned (packageInputsOne owned acc r) rest

private def packageInputsOne (owned : Bool) (acc : Array String) : Raw → Array String
  | .env n body _ =>
    match Parse.inputEnvFile? n with
    | some f =>
      packageInputsList (owned || packageFile f)
        (if owned && !acc.contains f then acc.push f else acc) body.toList
    | none => packageInputsList owned acc body.toList
  | .group body _ => packageInputsList owned acc body.toList
  | .math _ body _ => packageInputsList owned acc body.toList
  | .ctrl _ _ | .verb _ _ _ | .sym _ _ | .word _ _ | .space | .par _ => acc

end

/-- The files a package or class file inputs, directly or through another file it inputs, whose
declarations are the package's. -/
public def packageInputs (file : String) (raws : Array Raw) : Array String :=
  packageInputsList (packageFile file) #[] raws.toList

/-- A diagnostic attributed by its source site, keeping an explicit trigger; a
loss about a place takes none. -/
public def SourceTriggers.atSource (sources : SourceTriggers) (file : String)
    (pos : Pos) (d : Diag) : Diag :=
  { d with trigger := if d.kind.namesPlace then d.trigger else d.trigger.orElse fun _ =>
      (sources.writtenAt file pos).bind Diag.Spelling.ofWritten? }

public theorem SourceTriggers.atSource_unmapped_id (sources : SourceTriggers) (file : String)
    (pos : Pos) (d : Diag) (h : pos.sourceMapped = false) :
    sources.atSource file pos d = d := by
  simp [SourceTriggers.atSource, SourceTriggers.writtenAt, h]

private def atSource (st : St) (pos : Pos) (d : Diag) : Diag :=
  st.sourceTriggers.atSource st.file pos d

public theorem atSource_record_exact (sources : SourceTriggers) (file : String)
    (pos : Pos) (d : Diag) :
    { sources.atSource file pos d with trigger := d.trigger } = d := by rfl

/-- The one door a diagnostic lands through here: a push, keyed by `subject`,
the loss's census key. -/
private def say (code : DiagCode) (msg : String) (pos : Pos) (help : Option String := none)
    (demote : Bool := false) (subject : Option String := none)
    (refused : Option String := none) (output : Option Diag.Output := none)
    (detail : Option String := none) : M Unit :=
  modify fun st => { st with
    diags := st.diags.push (
      let d := atSource st pos
        (Diag.of code msg (some ⟨st.file, pos⟩) help subject refused (output := output)
          (detail := detail))
      if demote then d.demote else d) }

/-- A diagnostic said once per namespaced key (`ctrl:`, `spec:`, `beamer:`); a
repeat is accounted as a write. -/
private def sayOnce (key : String) (code : DiagCode) (msg : String) (pos : Pos)
    (help : Option String := none) (demote : Bool := false) (detail : Option String := none) :
    M Unit := do
  let first := !(← get).warned.contains key
  if first then
    write fun st => { st with warned := st.warned.push key }
  else
    write id
  say code msg pos (if first then help else none) (demote || !first) (subject := some key)
    (detail := detail)

/-- The one line a `\multicolumn` that does not open a tabular cell prints. -/
public def multicolumnMisplaced : String :=
  "'\\multicolumn' opens no tabular cell here: its text stays in place, without its \
span or alignment"

public def multicolumnMisplacedHelp : String :=
  "write \\multicolumn first in a tabular cell"

/-- The translation note, one shape for every translation. -/
private def became (what native : String) (pos : Pos)
    (subject : Option String := none) : M Unit :=
  say .N0100 s!"'{what}' → {native}" pos (subject := subject)

/-- A construct that reads to nothing: the translation note keyed
`ctrl:nothing:<key>`, naming the reason. -/
private def discard (what why key : String) (pos : Pos) : M Unit :=
  became what s!"nothing: {why}" pos (subject := some ("ctrl:nothing:" ++ key))

/-- The census subject of a declared setting: its reader and its name. -/
public def paramSubject (reader name : String) : String := s!"param:{reader}:{name}"

/-- A declared setting no engine site reads, named once where it is set. -/
private def unreadParam (reader name what : String) (pos : Pos)
    (help : String := "\\allow{W0104} accepts the skip") : M Unit :=
  sayOnce ("param:" ++ reader ++ ":" ++ name) .W0104 (Diag.notHonoured what) pos
    (help := help)

/-- minted's keys that configure a display alone, read for no inline code. -/
public def mintedDisplayKeys : List String :=
  ["linenos", "numbers", "firstnumber", "stepnumber", "numbersep", "numberblanklines",
   "numberfirstline", "frame", "framerule", "framesep", "rulecolor", "label",
   "labelposition", "xleftmargin", "xrightmargin", "resetmargins", "samepage", "vspace",
   "listparameters", "firstline", "lastline", "highlightlines", "highlightcolor"]

/-- A `\\setlist` scope as enumitem reads its optional argument: names are list kinds and numbers
levels, none of either standing for every kind or level. -/
private def setlistScope (scope : String) : List String × List Nat :=
  let parts := (scope.splitOn ",").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
  (parts.filter (·.toNat?.isNone), parts.filterMap (·.toNat?))

/-- The list kinds a `\\setlist` scope styles through an element. -/
private def setlistKinds : List String := ["itemize", "enumerate"]

/-- enumitem's length keys a `\\setlist` reads into a kind's style, each with the native style key
it sets; its vertical keys are a list's spacing (`listSpacingEntries`). -/
public def setlistLengthKeys : List (String × String) := [("leftmargin", "indent")]

/-- The native entries one list level takes from enumitem's stored scopes, applied as enumitem
applies them: every list, the level, the kind, then the kind at the level, a later key winning. -/
private def setlistRecord
    (stored : Array ((Option String × Option Nat) × Array (String × Native.StyleValue)))
    (kind : String) (level : Option Nat) : Array (String × Native.StyleValue) :=
  let scopes : List (Option String × Option Nat) := match level with
    | none => [(none, none), (some kind, none)]
    | some l => [(none, none), (none, some l), (some kind, none), (some kind, some l)]
  scopes.foldl (fun acc sc =>
    match stored.find? (·.1 == sc) with
    | some (_, entries) => entries.foldl (fun a e => Ir.redeclare a e.1 e.2) acc
    | none => acc) #[]

/-- The style element of a list kind at a level, the kind's own standing for its first level and
every level no deeper element takes. -/
private def setlistElement (kind : String) : Option Nat → String
  | some l => s!"{kind}{l}"
  | none => kind

/-- An optional argument as written, brackets and all, or nothing. -/
private def bracketed (s : String) : String := if s.isEmpty then "" else s!"[{s}]"

/-- A declared setting the engine's own machinery already answers, named in its note. -/
private def inertParam (reader name what why : String) (pos : Pos) : M Unit :=
  became what s!"nothing: {why}" pos (subject := some (paramSubject reader name))

/-- The preamble proper: outside the document environment, a `\begin{document}`
hook's replay, and every brace group of the walk. -/
private def preambleProper : M Bool := do
  let st ← get
  return !st.inDoc && !st.inDef && !st.seam && !st.inGroup

/-- The preamble proper of a whole document; a value's text
read on its own has none. -/
private def docPreamble : M Bool := do
  return (← get).wholeDoc && (← preambleProper)

/-- The top-level brace groups of a feature value; text
outside any group is dropped. -/
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
  if key == "size*" then Ir.FontAxis.size.key else key

/-- The stored font fields updated by a declaration's key
list; an empty value clears its field. -/
private def beamerFontUpdate (old : List (String × Array Raw)) (src : Array Raw) :
    List (String × Array Raw) := Id.run do
  let mut fields := old
  for e in Entries.read .keyval src do
    -- `size*`'s two groups are read as written, a single one included.
    if let some value := if e.key == "size*" then e.written else e.value then
      fields := (e.key, value) :: fields.filter (fun f => beamerFontAxis f.1 != beamerFontAxis e.key)
  return fields

/-- A value's top-level groups; what stands outside them is dropped. -/
private def rawGroups (v : Array Raw) : Array (Array Raw) :=
  v.filterMap fun r => match r with
    | .group b _ => some b
    | _ => none

/-- Native font commands selecting the stored fields in beamer's order. -/
private def beamerFontCommands (fields : List (String × Array Raw)) (pos : Pos) : Array Raw :=
  beamerFontKeys.foldl (init := #[]) fun out axis =>
    match fields.find? (fun e => beamerFontAxis e.1 == axis) with
    | some ("size*", value) =>
      match (rawGroups value).toList with
      | [size, skip] =>
        out ++ #[.ctrl "fontsize" pos, .group size pos, .group skip pos, .ctrl "selectfont" pos]
      | _ => out
    | some (_, value) => out ++ value
    | none => out

/-- A theme's own block title fields over those declared before it loads. -/
private def themeOver (stored seed : List (String × Array Raw)) : List (String × Array Raw) :=
  seed.foldl (fun fields (key, value) =>
    (key, value) :: fields.filter (fun e => beamerFontAxis e.1 != beamerFontAxis key)) stored

/-- The fields the plain block title is set in: its own, with the regular series
where they name none. -/
private def blockTitleFields (element : String) (fields : List (String × Array Raw)) (pos : Pos) :
    List (String × Array Raw) :=
  if element == "block title" &&
      !fields.any (fun e => e.1 == Ir.FontAxis.series.key && !(rawSrc e.2).isEmpty) then
    (Ir.FontAxis.series.key, #[.ctrl "mdseries" pos]) :: fields.filter (·.1 != Ir.FontAxis.series.key)
  else fields

/-- The commands a template sets its font with, its measured size apart: a size beamer does not
measure before the other fields. -/
private def templateFontCommands (fields : List (String × Array Raw)) (pos : Pos) : Array Raw :=
  let rest := beamerFontCommands (fields.filter fun e => beamerFontAxis e.1 != Ir.FontAxis.size.key) pos
  match fields.find? (fun e => beamerFontAxis e.1 == Ir.FontAxis.size.key) with
  | some ("size*", _) | none => rest
  | some (_, value) =>
    let src := rawSrc value
    let name := if src.startsWith "\\" then (src.drop 1).toString else src
    if (TitleTemplate.beamerSizes.lookup name).isSome then rest else value ++ rest

/-- The title template's font, its measured size and leading
carried separately. -/
private def beamerTemplateFont (element : String) (fields : List (String × Array Raw)) (pos : Pos) :
    TitleTemplate.Font := Id.run do
  let mut font : TitleTemplate.Font := { cmds := rawSrc (templateFontCommands fields pos) }
  match fields.find? (fun e => beamerFontAxis e.1 == Ir.FontAxis.size.key) with
  | some ("size*", value) =>
    let gs := (rawGroups value).map rawSrc
    font := { font with size := gs[0]?, leading := gs[1]? }
    if gs.size < 2 then
      font := { font with unread := font.unread.push s!"'size*' of '{element}'" }
    if gs.size > 2 then
      font := { font with unread := font.unread.push s!"extra size fields of '{element}'" }
  | some (_, value) =>
    let src := rawSrc value
    let name := if src.startsWith "\\" then (src.drop 1).toString else src
    if let some (size, leading) := TitleTemplate.beamerSizes.lookup name then
      font := { font with size := some size, leading := some leading }
  | none => pure ()
  for (key, _) in fields do
    unless beamerFontKeys.contains (beamerFontAxis key) do
      font := { font with unread := font.unread.push s!"'{key}' of '{element}'" }
  return font

/-- One `FontFace = {series}{shape}{font}` entry as the native slot part it
becomes, or `none` after a warning naming what could not be honoured. -/
private def fontFacePart (family slot v : String) (pos : Pos) :
    M (Option (String × String)) := do
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
      return some (s!"{slot}.{w.series}{ext}", Decl.quote f)
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

mutual

/-- Token sites relocated without changing their spelling; an input wrapper owns
another file's sites. -/
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

private theorem endsCtrlSpace_rebase (mapPos : Pos → Pos) (groups : Bool) (rs : List Raw) :
    endsCtrlSpace (rebaseList mapPos groups rs) = endsCtrlSpace rs := by
  induction rs with
  | nil => rfl
  | cons r rest ih =>
    have hall : ∀ l : List Raw, (rebaseList mapPos groups l).all isBlankRaw = l.all isBlankRaw := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ihx => cases x <;> simp [rebaseList, rebase, isBlankRaw, ihx]
    have hr : isCtrlSpace (rebase mapPos groups r) = isCtrlSpace r := by cases r <;> rfl
    simp only [rebaseList, endsCtrlSpace, hall, hr, ih]

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

private theorem rebase_source (mapPos : Pos → Pos) (groups : Bool) (r : Raw) :
    rawSrcOne (rebase mapPos groups r) = rawSrcOne r := by
  cases r with
  | env n body p =>
    simp only [rebase]
    split <;> simp only [rawSrcOne, rebaseArray_source, endsCtrlSpace_rebase]
  | _ => simp only [rebase, rawSrcOne, rebaseArray_source, endsCtrlSpace_rebase]

end

public theorem rebase_source_exact (mapPos : Pos → Pos) (groups : Bool) (r : Raw) :
    rawSrcOne (rebase mapPos groups r) = rawSrcOne r :=
  rebase_source mapPos groups r

/-- Each entry a carrier cannot read back whole, named dropped. -/
private def dropUnfit (dropped : List (String × String)) (opening : String) (pos : Pos) : M Unit := do
  -- premise: nativeCarrierChecks — a value no entry carries whole would read as other entries
  for (k, v) in dropped do
    say .W0101 "a value that stands as no single native entry was dropped" pos
      (detail := some s!"'{k} = {v}' in '{opening}'")
      (help := "write the value so it stands as one entry: its commas, quotes and brackets inside braces")

/-- A native setting's carrier where it stands, each entry its block cannot carry whole named and
dropped, so the elaborator reads the rest exactly (`Native.render_parse_exact`). -/
private def carry (s : Native.Setting) (pos : Pos) : M (Array Raw) := do
  dropUnfit s.dropped s.opening pos
  return if s.kept.pairs.isEmpty then #[] else s.raws pos

/-- A native setting where it stands, named as `what`'s translation where it keeps an entry. -/
private def setting (what : String) (s : Native.Setting) (pos : Pos)
    (subject : Option String := none) : M (Array Raw) := do
  if let some n := s.note? then became what n pos (subject := subject)
  carry s pos

/-- A style holding TeX where it stands, named as `what`'s translation where it keeps an entry, each
text entry its carrier cannot read back whole named and dropped. -/
private def texSetting (what element : String) (entries : Array (String × Native.StyleValue))
    (pos : Pos) : M (Array Raw) := do
  let unfit (kv : String × Native.StyleValue) : Option (String × String) := match kv.2 with
    | .text w => if Native.Setting.carried (kv.1, w) then none else some (kv.1, w)
    | .tex _ => none
  let kept := entries.filter (unfit · |>.isNone)
  unless kept.isEmpty do became what (Native.texStyleRender element kept) pos
  dropUnfit (entries.toList.filterMap unfit) s!"\\style\{{element}}" pos
  return if kept.isEmpty then #[] else Native.texStyle element kept pos

/-- Raws without the blanks at both ends, as their source trimmed reads. -/
private def trimBlank (rs : Array Raw) : Array Raw :=
  ((rs.toList.dropWhile isBlankRaw).reverse.dropWhile isBlankRaw).reverse.toArray

mutual

-- conserves: none — a surface token comparison key
/-- Replacement-token identity for `\ifx`: positions and word boundaries
ignored, spaces and groups kept as tokens. -/
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

/-- One optional `[...]` argument, its tokens kept inert; groups are opaque and
an ungrouped `[` does not nest. -/
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

/-- A delimited argument with the one enclosing group
removed when that group is the whole argument. -/
private def ungroupArg (raws : Array Raw) : Array Raw :=
  match raws.toList with
  | [.group body _] => body
  | _ => raws

/-- Up to `n` optional `[...]` runs, and whether any of them was there. -/
private def takeOpts (raws : Array Raw) (i n : Nat) : Bool × Nat := Id.run do
  let mut j := i
  let mut any := false
  for _ in [0:n] do
    let (o, j') := takeOpt raws j
    if o.isSome then any := true
    j := j'
  return (any, j)

/-- Consecutive arguments in the raw source, whitespace
skipped only before an argument. -/
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

private def takeGroupsStep (raws : Array Raw) (s : Array (Array Raw) × Nat) :
    Id (ForInStep (Array (Array Raw) × Nat)) :=
  let k := skipSpaces raws s.2
  match raws[k]? with
  | some (.group body _) => pure (.yield (s.1.push body, k + 1))
  | some (r@(.ctrl _ _)) => pure (.yield (s.1.push #[r], k + 1))
  | _ => pure (.done s)

/-- Up to `n` brace groups or bare control words; any other
raw stops the reader unconsumed. -/
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

/-- The filename, read from the executed call the local-style reader sees. -/
@[expose] public def InputRequest.name (request : InputRequest) : String :=
  rawSrc ((takeGroups request.call (takeOpt request.call 1).2 1).1.getD 0 #[])

/-- A request's second group, the file of minted's `\inputminted{lang}{file}`. -/
@[expose] public def InputRequest.second (request : InputRequest) : String :=
  rawSrc ((takeGroups request.call (takeOpt request.call 1).2 2).1.getD 1 #[])

/-- The options, read from the executed call the filename is read from. -/
@[expose] public def InputRequest.options (request : InputRequest) : String :=
  ((takeOpt request.call 1).1.getD "").trimAscii.toString

/-- The scalar loading calls in one executed request, in
source order, duplicates retained. -/
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

public theorem takeGroups_prefix_exact {raws : Array Raw} {i args stop}
    (h : GroupPrefix raws i args stop) :
    takeGroups raws i args.length = (args.toArray, stop) := by
  rw [takeGroups_loop_exact, Std.Legacy.Range.forIn_eq_forIn_range']
  simpa using Loop.forIn_yields_exact (h.yields #[])
    (List.range' 0 args.length) (by simp)

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

/-- Undelimited TeX arguments, a group or one token each, with the unconsumed
tail of a lexer word. -/
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

/-- etoolbox's `\apptocmd`'s four arguments. -/
private def takeHookArgs (raws : Array Raw) (i : Nat) :
    Array (Array Raw) × Nat × Array Raw :=
  takeRawArgs raws i 4

/-- The arity of canonical undelimited parameter text `#1`
through `#9`; `none` for any other. -/
private def undelimitedArity (params : Array Raw) : Option Nat :=
  read params.toList 0
where
  read : List Raw → Nat → Option Nat
    | [], n => some n
    | .sym '#' _ :: .word w _ :: rest, n =>
      if n < 9 && w == toString (n + 1) then read rest (n + 1) else none
    | _, _ => none

/-- A captured minted command's text with each parameter replaced by its
argument's source; `##` is one `#`. -/
private def bindMintedParams (args : Array (Array Raw)) (s : String) : String := Id.run do
  if !s.contains '#' then return s
  let cs := s.toList.toArray
  let mut out := ""
  let mut i := 0
  for _ in [0:cs.size] do
    let some c := cs[i]? | break
    let next := cs[i + 1]?
    if c == '#' && next == some '#' then
      out := out.push '#'
      i := i + 2
    else if c == '#' && next.any (fun d => '1' ≤ d && d ≤ '9') then
      let k := ((next.map fun d => d.toNat - '1'.toNat)).getD 0
      match args[k]? with
      | some arg =>
        out := out ++ rawSrc arg
        i := i + 2
      | none =>
        out := out.push c
        i := i + 1
    else
      out := out.push c
      i := i + 1
  return out

mutual

-- conserves: none — substitutes arguments for parameter tokens
/-- Replacement text with its parameters bound: `#10` is argument one followed
by `0`, and `##` quotes one parameter token. -/
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
  | .verb e s p =>
    if e == "mintinline" || e == "mint" then .verb e (bindMintedParams args s) p else .verb e s p

end

/-- `\tikz`'s one-command form from `i`: the raws through the first top-level
`;`, with the rest of that word handed back. -/
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

/-- The reserved control name a saved native meaning carries
through macro execution. -/
public def overlayName (name : String) : String :=
  if name.startsWith "overlay native " then (name.drop "overlay native ".length).toString
  else name

private def overlayNativeName (name : String) : String :=
  let native := overlayName name
  "overlay native " ++ native

private def overlayTitled (name : String) : Bool :=
  ["block", "alertblock", "exampleblock"].contains name

/-- The numbered-selector shape of an overlay-aware command: ordinary arguments
before the last selector slot, and whether it is prefix-only. -/
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

/-- A closed selector: the raws it consumes through `stop`, with its last word's
suffix left in `tail`. -/
private structure OverlaySelector where
  word : Raw
  stop : Nat
  tail : Array Raw := #[]

/-- A `<...>` overlay selector read across lexer and
substituted-argument fragments. -/
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

/-- The canonical selector word `overlaySelector?` produced,
refused selectors included. -/
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

/-- The window after a selector: only `\newcommand<>` keeps looking, until its
ordinary arguments end. -/
private def OverlayWindow.afterSelector (w : OverlayWindow) : Option OverlayWindow :=
  if w.middle && w.left > 0 then some { w with selected := true } else none


/-- The window after a raw, with item labels' second
selector slot after the bracketed label. -/
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

/-- Beamer's starred and plus `\onslide` variants routed to
`\only` and `\visible`. -/
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

/-- Advertised selector slots normalized after macro execution, an accepted
final selector moved to the head. -/
-- conserves: none — a surface boundary walk
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

/-- The shared selector boundary, run after macro execution and before
compatibility routing. -/
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

/-- The selector cursor of the emitted prefix. -/
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

/-- The alert style around a body, one spelling for both `\alert` forms: the
theme's alert colour, or bold when unthemed. -/
public def alertStyled (themed : Bool) (body : Array Raw) (pos : Pos) : Array Raw :=
  if themed then
    #[.ctrl "textcolor" pos, .group #[.word "alert" pos] pos, .group body pos]
  else #[.group (#[.ctrl "bfseries" pos] ++ body) pos]

/-- The command name marking a conditional alert style, unforgeable because a
control word holds no space. -/
public def alertMark (themed : Bool) : String :=
  if themed then "alert themed" else "alert plain"

/-- The boundary's set-line vocabulary, collected as written into the standalone
while the boundary is open. -/
public def boundaryCtrls : List String :=
  ["usetikzlibrary", "tikzset", "tikzcdset", "gtrset", "pgfplotsset", "graphicspath"]

/-- The set lines the engine reads itself. -/
public def nativeSetCtrls : List String := ["tikzset"]

/-- The picture-family lines the engine reads itself and
never names as unknown. -/
public def nativeReadCtrls : List String := nativeSetCtrls ++ ["usetikzlibrary", "graphicspath"]

/-- Picture packages, whose loads go to the boundary standalone's preamble while
the boundary is open. -/
public def boundaryPkgs : List String :=
  ["genealogytree", "pgfplots", "circuitikz"]

/-- Native packages whose loads also go to the boundary standalone, which sets
picture labels and diagram cells. -/
public def boundaryMathPkgs : List String := ["amsmath", "amssymb", "amsfonts", "tikz-cd"]

/-- Whether the document refused the boundary with a
`\pictures{ tool = none }` block. -/
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

/-- The picture environments whose bodies go to the boundary verbatim. -/
public def pictureEnvs : List String := ["tikzpicture", "external"]

/-- Whether a package is a theme of the document's class,
from beamer's theme family. -/
public def themePackage (p : String) : Bool := (themeSlotOfPackage? p).isSome

/-- Whether a package belongs to the presentation class's own family: a theme,
one of beamer's modules, or an add-on named for it. -/
public def classPackage (p : String) : Bool :=
  themePackage p || ((p.splitOn "beamer").length > 1 && p != "beamerarticle") || p == "pdfpc"

/-- Whether a boundary standalone carries the package's load. -/
public def boundaryRides (p : String) : Bool :=
  !p.isEmpty && (!nativePackages.contains p || boundaryMathPkgs.contains p) && !classPackage p

/-- The directories a `\graphicspath` argument names, one
per group, as written. -/
public def graphicsDirs (arg : Array Raw) : Array String :=
  arg.filterMap fun r => match r with
    | .group body _ => some (rawSrc body).trimAscii.toString
    | _ => none

/-- What one tree walk collects for a document's picture renderers. -/
public structure BoundaryScan where
  pre : String := ""
  sets : Array (Span × Array Raw) := #[]
  /-- The last `\graphicspath` line's directories, as written. -/
  graphics : Array String := #[]

mutual

-- conserves: none — the result is the standalone's preamble text
private def boundaryLevel (file : String) (raws : Array Raw) (out : BoundaryScan) :
    List Raw → Nat → Nat → BoundaryScan
  | [], _, _ => out
  | _ :: rest, i, skip + 1 => boundaryLevel file raws out rest (i + 1) skip
  | .ctrl name p :: rest, i, 0 =>
    if name == "usepackage" || name == "RequirePackage" then
      let (opt, j) := takeOpt raws (i + 1)
      let (args, k) := takeGroups raws j 1
      let pkgs := (KeyVal.items (rawSrc (args.getD 0 #[]))).toList.filter boundaryRides
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
        else if name == "graphicspath" then
          { out with graphics := graphicsDirs (args.getD 0 #[]) }
        else out
      boundaryLevel file raws out rest (i + 1) (k - (i + 1))
    else boundaryLevel file raws out rest (i + 1) 0
  | r :: rest, i, 0 => boundaryLevel file raws (boundaryRaw file out r) rest (i + 1) 0

/-- One raw of the boundary-declaration walk, descending into groups,
environments and input wrappers. -/
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

/-- What one walk of the tree collects for a picture's renderers. -/
public def boundaryScan (file : String) (raws : Array Raw) : BoundaryScan :=
  boundaryLevel file raws {} raws.toList 0 0

/-- The preamble declarations a boundary standalone needs,
collected from the unrewritten tree. -/
public def boundaryDecls (file : String) (raws : Array Raw) : String :=
  (boundaryScan file raws).pre

/-- The key lists the engine reads itself, in source order, each with the span
of the `\tikzset` that wrote it. -/
public def tikzsetKeys (file : String) (raws : Array Raw) : Array (Span × Array Raw) :=
  (boundaryScan file raws).sets

/-- The directories the document's last `\graphicspath` names. -/
public def graphicsPath (file : String) (raws : Array Raw) : Array String :=
  (boundaryScan file raws).graphics

public theorem boundaryDecls_covers (file : String) (raws : Array Raw) (p : Pos) :
    boundaryDecls file #[.env "document" raws p] = boundaryDecls file raws := by
  simp [boundaryDecls, boundaryScan, boundaryLevel, boundaryRaw, pictureEnvs,
    Parse.inputEnvFile?, String.startsWith_string_iff]

public theorem tikzsetKeys_covers (file : String) (raws : Array Raw) (p : Pos) :
    tikzsetKeys file #[.env "document" raws p] = tikzsetKeys file raws := by
  simp [tikzsetKeys, boundaryScan, boundaryLevel, boundaryRaw, pictureEnvs,
    Parse.inputEnvFile?, String.startsWith_string_iff]

public theorem tikzsetKeys_input_exact (caller file name : String) (body : Array Raw)
    (pos : Pos) (h : Parse.inputEnvFile? name = some file) :
    tikzsetKeys caller #[.env name body pos] = tikzsetKeys file body := by
  have hp : name ∉ pictureEnvs := by
    intro hm
    simp only [pictureEnvs, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp [Parse.inputEnvFile?, String.startsWith_string_iff] at h
  simp [tikzsetKeys, boundaryScan, boundaryLevel, boundaryRaw, hp, h]

/-- The index after the `*` of a starred LaTeX form, if one stands there. -/
private def skipStar (raws : Array Raw) (i : Nat) : Nat :=
  match raws[i]? with
  | some (.word "*" _) => i + 1
  | _ => i

/-- The end of a predefined beamer template's arguments: its further options and a brace group
standing right after them, never a control word on the next line. -/
private def predefinedEnd (raws : Array Raw) (i : Nat) : Nat :=
  let (_, j) := takeOpts raws i 2
  match raws[j]? with
  | some (.group _ _) => j + 1
  | _ => j

/-- Whether a template body prints only its element's own text, beamer's `\\insert` command of that
name, which the engine draws in its own element. -/
private def insertsOwn (element body : String) : Bool :=
  let kept := body.toList.filter fun c => !c.isWhitespace && c != '{' && c != '}'
  String.ofList kept == "\\insert" ++ String.ofList (element.toList.filter (· != ' '))

/-- The templates an empty body leaves as the engine draws them: no navigation symbols, and beamer's
empty headline and background. -/
public def emptyTemplates : List String := ["navigation symbols", "headline", "background"]

/-- The templates whose predefined `default` form lualatex measured drawing as an unthemed deck
draws them already. -/
public def defaultTemplates : List String :=
  ["itemize items", "enumerate items", "blocks", "footline", "title page"]

/-- lineno's options naming the numbering the engine sets once `\linenumbers` turns it on. -/
public def linenoInert : List String := ["left", "running", "displaymath", "mathlines"]

/-- lineno's options read as one native declaration each. -/
public def linenoNatives : List (String × Native.Setting) := [("modulo", .page #[(.modulo, "5")])]

/-- `\usepackage[...]{lineno}`'s options, natively the declared page keys. -/
private def linenoLoad (opt : String) (pos : Pos) : M (Array Raw) := do
  let mut out : Array Raw := #[]
  for o in KeyVal.items opt do
    if linenoInert.contains o then
      inertParam "usepackage:lineno" o s!"\\usepackage[{o}]\{lineno}"
        "where line numbers are on, every galley line, display math's too, is numbered in the left margin, running on" pos
    else if let some native := linenoNatives.lookup o then
      out := out ++ (← setting s!"\\usepackage[{o}]\{lineno}" native pos
        (subject := some (paramSubject "usepackage:lineno" o)))
    else
      sayOnce ("param:usepackage:lineno:" ++ o) .W0104 s!"lineno option '{o}' selects a numbering mode \
the engine does not have; continuous numbers in the left margin stand" pos
  discard "\\usepackage{lineno}" "\\page{ linenumbers = on } turns line numbers on"
    "usepackage:lineno" pos
  return out

/-- unicode-math's option-driven legacy alphabets, carried into the typed font
specification; other options are named. -/
private def unicodeMathOptions (what opt : String) (pos : Pos) : M (Array Raw) := do
  let mut sources : Array (String × String) := #[]
  let mut dropped : Array String := #[]
  for entry in KeyVal.items opt do
    match KeyVal.entry entry with
    | (key, some value) =>
      match Math.MathAlphabet.sourceKey? key, Math.MathAlphabetSource.ofName? value with
      | some _, some source => sources := sources.push (key, source.name)
      | _, _ => dropped := dropped.push entry
    | (_, none) => dropped := dropped.push entry
  for e in dropped do
    unreadParam "usepackage:unicode-math" (KeyVal.entry e).1 s!"unicode-math option '{e}'" pos
      (help := "the math alphabets' source keys (mathrm=sym, ...) carry over")
  if sources.isEmpty then
    discard what "the engine keeps its existing math-source policy"
      "usepackage:unicode-math" pos
    return #[]
  setting what (.fonts sources) pos

/-- A citation setup carried to the document, replayed at `\begin{document}`. -/
private def natbibDefer (decls : Array CiteDecl) (pos : Pos) : M Unit :=
  write fun st => { st with deferred := st.deferred.push (.beginDocument, st.file, pos,
    Parse.citeSetupRaws decls pos) }

/-- biblatex's punctuation and format macros, which a document redefines to
restyle the list and its citations. -/
private def biblatexMacros : List String :=
  ["nameyeardelim", "multicitedelim", "postnotedelim", "prenotedelim", "multinamedelim",
   "finalnamedelim", "revsdnamepunct", "andothersdelim", "multilistdelim", "finallistdelim",
   "andmoredelim", "nametitledelim", "namelabeldelim", "nonameyeardelim", "extradatedelim",
   "textcitedelim", "finaltextcitedelim", "compcitedelim", "labelnamepunct", "subtitlepunct",
   "intitlepunct", "bibpagespunct", "bibpagerefpunct", "newunitpunct", "finentrypunct",
   "entrysetpunct", "bibnamedash", "bibfont", "citesetup", "bibsetup", "bibnamedelima",
   "bibnamedelimb", "bibnamedelimc", "bibnamedelimd", "bibnamedelimi", "bibinitperiod",
   "bibinitdelim", "bibinithyphendelim", "mkbibnamefamily", "mkbibnamegiven",
   "mkbibnameprefix", "mkbibnamesuffix", "mkbibdatelong", "mkbibdateshort"]

/-- A delimiter's definition as the text it prints, when it is only biblatex's
punctuation commands and text. -/
private def punctText (body : Array Raw) : Option String :=
  body.foldl (init := some "") fun acc r => acc.bind fun out =>
    match r with
    | .ctrl "addcomma" _ => some (out ++ ",")
    | .ctrl "addsemicolon" _ => some (out ++ ";")
    | .ctrl "addcolon" _ => some (out ++ ":")
    | .ctrl "addperiod" _ | .ctrl "adddot" _ => some (out ++ ".")
    | .ctrl "space" _ | .ctrl "addspace" _ | .ctrl "addnbspace" _ | .ctrl "nobreakspace" _
    | .ctrl " " _ | .space => some (out ++ " ")
    | .word w _ => some (out ++ (if w == "~" then " " else w))
    | .sym c _ => some (out.push c)
    | _ => none

/-- A redefinition of one of biblatex's macros. -/
private def biblatexMacroDef (definer cmd : String) (body : Array Raw) (pos : Pos) : M (Array Raw) := do
  let authoryear := (← get).bibStyle == some "plainnat"
  let slot : Option CiteDecl.Key := match cmd with
    | "nameyeardelim" => some .aysep
    | "multicitedelim" => some .citesep
    | "postnotedelim" => some .notesep
    | _ => none
  let value := (punctText body).bind fun t =>
    if slot == some .notesep then (if t.isEmpty then none else some t)
    else if t.endsWith " " && !(t.dropEnd 1).toString.endsWith " " then some (t.dropEnd 1).toString
    else none
  match slot, value with
  | some key, some v =>
    if authoryear then
      natbibDefer #[.set key v] pos
      became s!"\\{definer}\{\\{cmd}}" s!"the author-year citations' '{v}'" pos
      return #[]
    else pure ()
  | _, _ => pure ()
  say .W0104 s!"biblatex's '\\{cmd}' is redefined; the engine's reference list and \
citations keep biblatex's default in its place" pos
    (help := "under author-year citations, redefine '\\nameyeardelim', '\\multicitedelim' or \
'\\postnotedelim' as punctuation and a space, such as '\\addcomma\\space'")
    (subject := some s!"biblatexmacro:{cmd}")
  return #[]

/-- `\usepackage[...]{natbib}`: the load, its options as
declarations in natbib's order. -/
private def natbibLoad (name opt : String) (pos : Pos) : M (Array Raw) := do
  let given := (KeyVal.items opt).toList
  let (decls, dropped) := CiteDecl.natbibLoad given
  for o in dropped do
    unreadParam "usepackage:natbib" (KeyVal.entry o).1 (CiteDecl.natbibOption o) pos
  became (if given.isEmpty then s!"\\{name}\{natbib}" else s!"\\{name}[{opt}]\{natbib}")
    "natbib's citation punctuation, read at \\begin{document}" pos
  natbibDefer decls pos
  return #[]

/-- biblatex's options the reference list and citations read; `babel` is `autolang`'s former name
(biblatex manual §3.1.2.1). -/
public def biblatexRead : List String :=
  ["style", "bibstyle", "citestyle", "sorting", "babel"] ++ CiteDecl.Key.carriedNames.map (·.1)

/-- biblatex's options that change nothing the engine sets. -/
public def biblatexInert : List String :=
  ["backend", "hyperref", "natbib", "bibencoding", "texencoding", "safeinputenc",
   "bibwarn", "bibtexcaseprotection", "noerroretextools"]

/-- The style family a biblatex style name belongs to. -/
private def biblatexFamily (style : String) : Option String :=
  if style.startsWith "numeric" then some "numeric"
  else if style.startsWith "authoryear" then some "authoryear"
  else none

/-- `\usepackage[...]{biblatex}`: the reference list of biblatex's standard
styles, read through biber. -/
private def biblatexLoad (name opt : String) (pos : Pos) : M Unit := do
  let pairs := (KeyVal.items opt).toList.map fun o =>
    let (k, v) := KeyVal.entry o
    (k, v.getD "true")
  let pick (key dflt : String) : String := pairs.foldl (init := dflt) fun acc (k, v) =>
    if k == key then v else acc
  let bbx := pick "bibstyle" (pick "style" "numeric")
  let cbx := pick "citestyle" (pick "style" "numeric")
  let dropped := pairs.filter fun (k, _) => !biblatexRead.contains k && !biblatexInert.contains k
  for (k, v) in pairs do
    if k == "hyperref" && v != "false" then
      unreadParam "usepackage:biblatex" k s!"'biblatex' option '{k}={v}', linking each citation \
to its entry," pos
    else if biblatexInert.contains k then
      inertParam "usepackage:biblatex" k s!"\\{name}[{k}={v}]\{biblatex}"
        "the engine reads the bibliography and sets its citations itself" pos
  for (k, v) in dropped do
    unreadParam "usepackage:biblatex" k
      s!"'biblatex' option '{if v == "true" then k else s!"{k}={v}"}'" pos
  let what := match biblatexFamily bbx, biblatexFamily cbx with
    | none, none => some (if bbx == cbx then s!"style '{bbx}'" else s!"styles '{bbx}' and '{cbx}'",
        "its reference list and its citations are set as biblatex's numeric ones")
    | none, some _ => some (s!"bibliography style '{bbx}'",
        "its reference list is set as biblatex's numeric one")
    | some _, none => some (s!"citation style '{cbx}'",
        "its citations are set as biblatex's numeric ones")
    | some _, some _ => none
  if let some (name, loss) := what then
    say .W0353 s!"biblatex {name} is not one the engine knows; {loss}" pos
      (help := "styles known: numeric, authoryear and their -comp variants")
  let listFamily := (biblatexFamily bbx).getD "numeric"
  let citeFamily := (biblatexFamily cbx).getD "numeric"
  if (biblatexFamily cbx).isSome && cbx != citeFamily then
    say .W0101 s!"'biblatex' style '{cbx}' is read as '{citeFamily}': its citations' own \
compaction and repetition rules are dropped" pos (subject := some "usepackage:biblatex")
  let defaultSorting := if listFamily == "authoryear" then "nyt" else "nty"
  let declaredSorting := pick "sorting" defaultSorting
  let sorting ← if CiteDecl.sortingSchemes.contains declaredSorting then
      pure declaredSorting
    else do
      say .W0101 s!"'biblatex' option 'sorting={declaredSorting}' is not a scheme the engine \
sorts by; the list is sorted '{defaultSorting}'" pos (subject := some "usepackage:biblatex")
        (help := s!"the schemes sorted: {", ".intercalate CiteDecl.sortingSchemes}")
      pure defaultSorting
  let record :=
    if citeFamily == "authoryear" then "plainnat" else if sorting == "none" then "unsrt" else "plain"
  became (if opt.isEmpty then s!"\\{name}\{biblatex}" else s!"\\{name}[{opt}]\{biblatex}")
    s!"biblatex's {listFamily} reference list and {citeFamily} citations" pos
  write fun st => { st with bibStyle := some record }
  let mut carried : Array CiteDecl := #[]
  for (k, v) in pairs do
    let some key := (CiteDecl.Key.carriedNames.lookup (if k == "babel" then "autolang" else k))
      | continue
    if k == "uniquename" && ["mininit", "minfull", "minyearinit", "minyearfull"].contains v then
      say .W0101 s!"'biblatex' option 'uniquename={v}' is read as 'uniquename={if v.endsWith "init" then "init" else "full"}': \
a shared family is told apart wherever it appears, not only where whole lists coincide" pos
        (subject := some "usepackage:biblatex")
      carried := carried.push (.set key (if v.endsWith "init" then "init" else "full"))
    else if k == "uniquelist" && v == "minyear" then
      say .W0101 s!"'biblatex' option 'uniquelist=minyear' is read as 'uniquelist=true': lists \
are told apart whatever their year" pos (subject := some "usepackage:biblatex")
      carried := carried.push (.set key "true")
    else carried := carried.push (.set key v)
  let mainLang := (← get).babelMain
  write fun st => { st with biblatexLoaded := true }
  natbibDefer ((if record == "plainnat" then #[.word .nobibstyle, .set .aysep "", .word .biblatex]
    else #[.word .biblatex]) ++
    #[.set .bbx listFamily, .set .cbx citeFamily, .set .sorting sorting] ++ carried ++
    (mainLang.map (.set .mainlang ·)).toArray) pos

/-- `\setcitestyle{…}` and `\bibpunct`: natbib's
declarations in the preamble. -/
private def natbibStyle (name : String) (notes : Option (Array Raw)) (args : Array (Array Raw))
    (pos : Pos) : M (Array Raw) := do
  let punct := name == "bibpunct"
  -- natbib's values are token lists, so groups are read one deep as written.
  let verbatim (body : Array Raw) : String := body.foldl (init := "") fun s r =>
    let t := match r with
      | .group g _ => "{" ++ rawSrcList g.toList ++ "}"
      | r => rawSrcOne r
    s ++ t
  let src (i : Nat) : String := verbatim (args.getD i #[])
  let notesep := match notes with
    | some n => verbatim n
    | none => ", "
  let (decls, dropped) : Array CiteDecl × Array String :=
    if punct then
      (#[.punct .open (src 0), .punct .close (src 1), .punct .citesep (src 2),
        .word (if ["n", "s"].contains (src 3).trimAscii.toString then .numbers else .authoryear),
        .punct .aysep (src 4), .punct .yysep (src 5), .punct .notesep notesep], #[])
    else if name == "citestyle" then (#[.set .citestyle (src 0).trimAscii.toString], #[])
    else
      let items := (KeyVal.split (src 0)).filter (!·.isEmpty)
      (items.filterMap CiteDecl.ofItem?, items.filter (CiteDecl.ofItem? · |>.isNone))
  unless dropped.isEmpty do
    say .W0101 s!"'\\{name}' keywords without a native equivalent were dropped: \
{String.intercalate ", " (dropped.toList.map fun d => s!"'{d}'")}" pos
      (help := "natbib reads each keyword exactly as written, so write no space after a comma")
      (subject := some ("ctrl:" ++ name))
  if punct && (src 3).trimAscii.toString == "s" then
    say .W0101 s!"'\\bibpunct' superscript citations are set on the baseline" pos
      (subject := some "ctrl:bibpunct")
  became s!"\\{name}" "natbib's citation punctuation, read at \\begin{document}" pos
  natbibDefer (#[.word .nobibstyle] ++ decls) pos
  return #[]

/-- lineno's switch and modulo commands, natively the declared page keys. -/
private def lineNumbers (name : String) (opt : Option String) (pos : Pos) : M (Array Raw) := do
  if name == "modulolinenumbers" then
    let n := (opt.bind (fun o => o.trimAscii.toString.toNat?)).getD 5
    return (← setting "\\modulolinenumbers" (.page #[(.modulo, toString (max 1 n))]) pos)
  let on := name != "nolinenumbers"
  if on then
    if let some n := opt then
      unless n.trimAscii.toString == "1" do
        say .W0101 s!"'\\{name}[{n}]' asks to start numbering at {n}; \
line numbers here always run from 1" pos
  setting s!"\\{name}" (.page #[(.linenumbers, if on then "on" else "off")]) pos

/-- The kernel's point-size macros in milli-points, at the values the size files
and ltplain give them. -/
private def ptMacros : List (String × Nat) :=
  [("@vpt", 5000), ("@vipt", 6000), ("@viipt", 7000), ("@viiipt", 8000),
   ("@ixpt", 9000), ("@xpt", 10000), ("@xipt", 10950), ("@xiipt", 12000),
   ("@xivpt", 14400), ("@xviipt", 17280), ("@xxpt", 20740), ("@xxvpt", 24880)]

/-- One `\@setfontsize` argument in milli-points: a kernel
size macro or a literal number. -/
public def ptMacroArg (r : Array Raw) : Option Nat :=
  match r.toList with
  | [.ctrl n _] => ptMacros.lookup n
  | _ =>
    (Decl.parseDecimal (rawSrc r).trimAscii.toString).bind fun (m, s) =>
      if m ≥ 0 && s > 0 then some (m.toNat * 1000 / s) else none

/-- A milli value as its shortest decimal spelling. -/
public def milliStr (m : Nat) : String :=
  let i := m / 1000
  let f := m % 1000
  if f == 0 then toString i else
  let digits := ((toString (1000 + f)).drop 1).toString
  let digits := if digits.endsWith "00" then (digits.dropEnd 2).toString
    else if digits.endsWith "0" then (digits.dropEnd 1).toString
    else digits
  s!"{i}.{digits}"

/-- The conditional heads TeX defines: TeX82's `\if…`
primitives and e-TeX's three. -/
private def condHeads : List String :=
  (texPrimitives.toList.filter (·.startsWith "if")) ++ ["ifdefined", "ifcsname", "iffontchar"]

/-- Bind `n` to `v`, recording what it replaced on the save stack. -/
private def setBind (n : String) (v : Option CondVal) : M Unit :=
  write fun st =>
    let prev := st.binds[n]?
    { st with undo := st.undo.push (.bind n prev), binds := st.binds.insert n v }

/-- Set length `n`'s exact value, or forget it, recording what it replaced on the save stack, and
in the global log when `global`. -/
private def setExactLen (n : String) (v : Option Rat) (global : Bool) : M Unit := do
  write fun st =>
    let prev := st.exactLens[n]?
    { st with undo := st.undo.push (.len n prev),
              exactLens := match v with
                | some x => st.exactLens.insert n x
                | none => st.exactLens.erase n }
  if global then write fun st => { st with lenGlobals := st.lenGlobals.push (n, v) }

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

/-- The value of the `\newif` flag the control word tests, when recorded. -/
private def flagTested (flags : Std.HashMap String Bool) (n : String) : Option Bool :=
  if n.startsWith "if" && n.length > 2 then flags[(n.drop 2).toString]? else none

/-- Whether the pass can match a conditional headed `n`: one TeX defines, or a
declared flag's `\ifX`. -/
private def isCondHead (flags : Std.HashMap String Bool) (n : String) : Bool :=
  condHeads.contains n || (flagTested flags n).isSome

/-- The index of the `\fi` closing the conditional heading `raws[i]`, when every
`\if…` inside is a tracked head. -/
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

/-- The value a name holds: `none` when unbound, `some none`
when bound but unreadable. -/
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
holding an integer in turn. -/
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

/-- The expansion of textual, parameterless selector
fragments in this use's state. -/
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

/-- One element a test is read from: a character of a word,
a space, or a control word. -/
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

/-- The atoms of a test starting at `raws[j]`, never past a
group, a paragraph or math. -/
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

/-- A TeX ⟨number⟩ from atom `p0` on: signs and spaces, then digits or a macro
holding an integer, then one optional space. -/
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

/-- How many raws a test ending at atom `p` consumed, and the unread end of the
word it stopped inside. -/
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

/-- One open conditional: decided, an `\ifcase` with its
selected and current case, or opaque. -/
private inductive CondOpen where
  | decided (keep : Bool)
  | cased (sel : Int) (cur : Nat) (inElse : Bool)
  | opaque

/-- Whether the frame keeps what is read now; an opaque
frame keeps both branches. -/
private def CondOpen.keeps : CondOpen → Bool
  | .decided k => k
  | .cased sel cur inElse => if inElse then sel < 0 || sel > (cur : Int) else sel == (cur : Int)
  | .opaque => true

/-- What the pass reads a head as: the frame it opens, the raws its test
consumed, the unread word end, and the keyed note. -/
private structure CondRead where
  frame : CondOpen
  used : Nat := 0
  tail : Option Raw := none
  note : Option (String × String) := none

/-- Which branch a two-way decision keeps, in words. -/
private def keptWords (keep : Bool) : String :=
  if keep then "the branch before '\\else' is kept" else "only the '\\else' branch is kept"

/-- Whether the inner theme defines `standout`, which it does even when a native
theme replaces its implementation. -/
private def nativeStandoutDefined (st : St) : Bool :=
  st.loads.pkgs.any fun (name, _) =>
    ["beamerthememoloch", "beamerthememetropolis", "beamerthemem",
     "beamerinnerthememoloch", "beamerinnerthememetropolis"].contains name

/-- Whether a theme's own setter is defined, which it is
once the theme loads. -/
private def nativeSetterDefined (st : St) (n : String) : Bool :=
  n == "molochset" && st.loads.pkgs.any (·.1 == "beamerthememoloch")

/-- The head `h` at `raws[i]` read against the state in force there; `neg` marks
a preceding `\unless`. -/
private def readHead (st : St) (raws : Array Raw) (i : Nat) (h : String) (neg : Bool) :
    CondRead := Id.run do
  let undecided : CondRead := { frame := .opaque }
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
      -- premise: standoutPaletteChecks — each hook branch ships its colours
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

/-- Primitives that read the next token as itself, so a
macro after one is not a use. -/
private def condNoExpand : List String :=
  ["noexpand", "string", "meaning", "show", "expandafter", "futurelet"]

/-- Is `n` the setter of a declared flag (`\Xtrue`, `\Xfalse`)? -/
private def isFlagSetter (flags : Std.HashMap String Bool) (n : String) : Bool :=
  (n.endsWith "true" && flags.contains (n.dropEnd 4).toString) ||
    (n.endsWith "false" && flags.contains (n.dropEnd 5).toString)

/-- The branches a loaded test carries after its name and option list: both, the
true one only, or the false one only. -/
private inductive LoadedBranches where
  | tf
  | t
  | f
  deriving BEq, Repr

/-- One spelling of the loaded-test family: class or packages, whether an option
list follows, and its branches. -/
private structure LoadedTest where
  ctrl : String
  cls : Bool
  withOpts : Bool
  branches : LoadedBranches
  deriving BEq, Repr

/-- The family as latex.ltx defines it. -/
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

/-- What one test asks: the class or the packages, the name,
and the options it wants. -/
private structure LoadQuery where
  cls : Bool
  name : String
  want : Option (Array String)
  deriving BEq, Repr

/-- An option list as the kernel compares it:
comma-separated, spaces removed, empty items skipped. -/
private def optionItems (s : String) : Array String :=
  ((s.splitOn ",").map fun o => String.ofList (o.toList.filter (!·.isWhitespace)))
    |>.filter (!·.isEmpty) |>.toArray

/-- The one execution gate for native packages and local
styles; a repeat keeps the first execution. -/
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

private theorem admitPackage_compatible_exact (name : String)
    (options passed first : List String) (pos : Pos) (st : St)
    (loaded : st.loads.imports.lookup name = some first)
    (compatible : ∀ o ∈ options, o ∈ first ++ passed) :
    admitPackage name options passed pos st = (none, { st with writes := st.writes + 1 }) := by
  simp only [admitPackage, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure]
  rw [PackageImports.admit_compatible_exact _ _ _ _ _ loaded compatible]
  rfl

/-- A local file admitted tentatively; the driver commits the context only when
the file exists or the load repeats. -/
public def InputContext.admitLocalPackage (context : InputContext)
    (name options : String) (pos : Pos) : Option (List String) × InputContext :=
  let passed := (context.state.loads.passed.filter (·.1 == name)).toList.flatMap (·.2.toList)
  let (options, state) :=
    admitPackage name (PackageImports.literalOptions options) passed pos context.state
  (options, { state })

/-- Whether a package that loads pgf's loop and arithmetic has been loaded. -/
private def LoadSet.pgf (s : LoadSet) : Bool :=
  s.pkgs.any fun (p, _) => ["tikz", "pgf", "pgfplots", "pgffor", "pgfmath", "tikz-cd"].contains p

/-- One package load: the first load of a name stands. -/
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

/-- The answer the loads read so far give a test, `none`
when what it reads is not carried. -/
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

/-- Exactly `n` brace groups after `i`, each after any spaces. -/
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

/-- Whether a name argument holds only letters and
punctuation, which the pass can read unexpanded. -/
private def plainName (body : Array Raw) : Bool :=
  body.all fun
    | .word .. | .space | .sym .. => true
    | .par .. | .ctrl .. | .group .. | .math .. | .env .. | .verb .. => false

/-- The question a loaded test at `i` asks; `none` when its
shape is not the family's. -/
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

/-- A detokenized control word, with the delimiter space a control word carries
and a control symbol does not. -/
private def stringTestControl (n : String) : String :=
  "\\" ++ n ++ if !n.isEmpty && n.toList.all Lex.nameChar then " " else ""

mutual

-- conserves: none — a comparison key over surface tokens
private def stringTestTokens (out : String) : List Raw → Option String
  | [] => some out
  | r :: rest => (stringTestToken r).bind fun s => stringTestTokens (out ++ s) rest

/-- Literal token spelling for etoolbox's `\ifstrequal`. -/
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

/-- etoolbox's `\ifstrequal` answer, read from all four groups before any part
of the call executes. -/
private def stringTestAt (raws : Array Raw) (i : Nat) : Option Bool := do
  let args ← argGroupsAt raws i 4
  let left ← stringTestTokens "" (args.getD 0 #[]).toList
  let right ← stringTestTokens "" (args.getD 1 #[]).toList
  pure (left == right)

/-- Which groups after a resolved test are kept: the branch
the answer picks stays. -/
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

/-- A load the flow performs where it stands: a package line, the class line, an
option pass, or a theme slot. -/
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

/-- One collected hook: the note naming its replay point,
and the body stored against that point. -/
private def deferOne (name : String) (pt : DeferPoint) (body : Array Raw)
    (pos : Pos) : M Unit := do
  became s!"\\{name}\{...}" (match pt with
    | .beginDocument => "its body, replayed at '\\begin{document}'"
    | .endPreamble => "its body, replayed at the end of the preamble") pos
  let file := (← get).file
  write fun st => { st with deferred := st.deferred.push (pt, file, pos, body) }

/-- The group primitives, opener to closer. -/
public def groupPrimitives : List (String × String) :=
  [("begingroup", "endgroup"), ("bgroup", "egroup")]

/-- Whether a flat preamble scope closes before the document starts. -/
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

-- conserves: none — a predicate over a replacement text
/-- Whether a replacement text does something only its use can decide, itself or
through a macro it uses. -/
private def condLiveList (flags : Std.HashMap String Bool)
    (binds : Std.HashMap String (Option CondVal)) : List Raw → Bool
  | [] => false
  | r :: rest => condLiveRaw flags binds r || condLiveList flags binds rest

private def condLiveRaw (flags : Std.HashMap String Bool)
    (binds : Std.HashMap String (Option CondVal)) : Raw → Bool
  | .ctrl n _ =>
    isCondHead flags n || n == "unless" || n == "newif" || n == "ifstrequal" ||
      Definer.readAsDefinition.contains n ||
      (overlayArity? n).isSome ||
      isFlagSetter flags n || loadedTests.any (·.ctrl == n) ||
      (deferredHooks.lookup n).isSome ||
      inputCommands.contains n || n == "markdownSetup" ||
      ["documentclass", "usepackage", "RequirePackage",
        "RequirePackageWithOptions", "PassOptionsToPackage", "PassOptionsToClass"].contains n ||
      (themeAsking.lookup n).isSome ||
      -- Length declarations and mutations execute at each use.
      ["newlength", "newdimen", "setlength", "addtolength", "advance", "multiply",
        "divide"].contains n ||
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

/-- A definition's operands as the pass reads them: where they stop, and which
are replacement texts. -/
private structure DefShape where
  stop : Nat
  bodies : List Nat

/-- The control word inside a group, ignoring whitespace around it. -/
private def ctrlName (raws : Array Raw) : Option String :=
  match raws.toList.filter (fun r => match r with | .space => false | _ => true) with
  | [.ctrl n _] => some n
  | _ => none

/-- The caption-skip declarations standing in front of a float's kernel core,
when they are the whole begin body. -/
private def floatCoreDecls (kind : String) : List Raw → Option (List (String × Array Raw))
  | [.ctrl "@float" _, .group n _] =>
    if (rawSrc n).trimAscii.toString == kind then some [] else none
  | .ctrl "setlength" _ :: .group reg _ :: .group v _ :: rest =>
    let skip := (ctrlName reg).filter fun r => r == "abovecaptionskip" || r == "belowcaptionskip"
    skip.bind fun r => (floatCoreDecls kind rest).map ((r, v) :: ·)
  | _ => none

/-- The floats a redefinition around their own kernel core reads. -/
public def floatRedefEnvs : List String := ["table", "figure"]

/-- Whether a float's redefinition at `raws[i]` is the kernel-core idiom `floatRedef?` reads: a
`\renewenvironment` without arguments, `\@float` with caption skips before it, `\end@float` after. -/
private def floatCoreAt (env : String) (raws : Array Raw) (i : Nat) (d : String) : Bool := Id.run do
  if d != "renewenvironment" then return false
  let (_, j) := takeGroups raws (skipStar raws (i + 1)) 1
  let (count, j) := takeOpt raws j
  let (dflt, jd) := takeRawOpt raws j
  if count.isSome || dflt.isSome then return false
  let items (xs : Array Raw) : List Raw := xs.toList.filter fun r =>
    match r with | .space | .par _ => false | _ => true
  let b := skipSpaces raws jd
  let some (.group beginB _) := raws[b]? | return false
  let some (.group endB _) := raws[skipSpaces raws (b + 1)]? | return false
  return (items endB matches [.ctrl "end@float" _]) && (floatCoreDecls env (items beginB)).isSome

/-- The environment an environment definer at `raws[i]` names in its first group. -/
private def definedEnv (raws : Array Raw) (i : Nat) : Option String :=
  match raws[skipSpaces raws (skipStar raws (i + 1))]? with
  | some (.group #[.word w _] _) => some w
  | _ => none

/-- Whether an environment definer at `raws[i]` defines a built-in the engine ignores whole: one of
`ignored`, or a float other than by its kernel-core idiom. -/
private def ignoredEnvDef (ignored : List String) (raws : Array Raw) (i : Nat) (d : String) :
    Bool :=
  match definedEnv raws i with
  | some e => ignored.contains (Tcolorbox.bindingName e) ||
      (floatRedefEnvs.contains e && !floatCoreAt e raws i d)
  | none => false

/-- The operands of the definer `d` at `raws[i]`, or `none`
for a shape the pass does not read. -/
private def definerShape (raws : Array Raw) (i : Nat) (d : String)
    (stored : Bool := false) : Option DefShape := Id.run do
  let groupFrom (k : Nat) : Option Nat := Id.run do
    let mut j := k
    for _ in [k:raws.size] do
      match raws[j]? with
      | some (.group _ _) => return some j
      | some (.par _) => return none
      | some (.sym '[' _) =>
        match takeRawOpt raws j with
        | (some _, j') => j := j'
        | (none, _) => j := j + 1
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
  if d == "NewEnviron" || d == "RenewEnviron" then
    let j := starred (i + 1)
    unless raws[j]? matches some (.group _ _) do return none
    let (_, k1) := takeOpt raws (j + 1)
    let (_, k2) := takeOpt raws k1
    let b := skipSpaces raws k2
    unless raws[b]? matches some (.group _ _) do return none
    return some { stop := (takeOpt raws (b + 1)).2, bodies := [b] }
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

-- conserves: none — drops what only a use can decide
/-- A replacement text with what only a use can decide removed at any depth, and
whether anything was. -/
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
    else if Definer.readAsDefinition.contains n then
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

/-- Records a definition of `n` whose readable value is `v`,
globally when `global`. -/
private def recordValue (n : String) (v : Option CondVal) (global : Bool)
    (copied : Bool := false) : M Unit := do
  let st ← get
  let s := st.serial + 1
  let v := v.map fun c =>
    { c with
      live := global || c.live || c.arity > 0 || c.optional.isSome || condLiveList st.flags st.binds c.raws.toList
      serial := s
      -- premise: Tests.macroHookScopeChecks — a local let executes before scope closes
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

/-- The prefixes standing before the definer at `raws[i]`, nearest first. -/
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

/-- The most steps an `\edef` expansion takes, each raw it walks and each call it makes, past which
it stays refused. -/
private def edefCap : Nat := 65536

/-- Where a `\dimexpr`'s text ends: the index of its own `\relax` among `rs`. -/
private def dimexprEnd : List Raw → Nat → Nat → Option Nat
  | [], _, _ => none
  | .ctrl "relax" _ :: rest, depth, i => if depth == 0 then some i else dimexprEnd rest (depth - 1) (i + 1)
  | .ctrl "dimexpr" _ :: rest, depth, i => dimexprEnd rest (depth + 1) (i + 1)
  | _ :: rest, depth, i => dimexprEnd rest depth (i + 1)

/-- The dimen e-TeX reads after `\the`, `\number` or `\strip@pt`: a length register, or a
`\dimexpr` over lengths and numbers up to its `\relax`; its exact value in inches and the raws
it took. -/
private def edefDimen (lenOf : String → Option Rat) (rs : List Raw) : Option (Rat × Nat) :=
  let lead := (rs.takeWhile (· matches .space)).length
  match rs.drop lead with
  | .ctrl "dimexpr" _ :: rest =>
    (dimexprEnd rest 0 0).bind fun i =>
      (Decl.exactLength lenOf (rawSrc (rest.take i).toArray)).map (·, lead + i + 2)
  | .ctrl r _ :: _ => (lenOf r).map (·, lead + 1)
  | _ => none

/-- A length as TeX prints it: its scaled points rounded half away from zero, then the fewest
decimals that read back to them, with `pt` for `\the`, as a whole number for `\number`. -/
private def edefPrint (cmd : String) (v : Rat) : String :=
  let x := v * 7227 / 100 * 65536
  let sp : Int := if x < 0 then -((-x + 1 / 2).floor) else (x + 1 / 2).floor
  let (whole, digits) := Decl.texScaledParts sp.natAbs
  let sign := if sp < 0 then "-" else ""
  let frac := String.join (digits.map toString)
  if cmd == "number" then toString sp
  else if cmd == "the" then s!"{sign}{whole}.{frac}pt"
  else if digits == [0] then s!"{sign}{whole}" else s!"{sign}{whole}.{frac}"

/-- A definition's undelimited arguments: `n` brace groups or single control words, spaces
before each skipped; the arguments and the raws they took. -/
private def edefArgs : Nat → List Raw → Nat → Array (Array Raw) → Option (Array (Array Raw) × Nat)
  | 0, _, used, acc => some (acc, used)
  | k + 1, .space :: rest, used, acc => edefArgs (k + 1) rest (used + 1) acc
  | k + 1, .group body _ :: rest, used, acc => edefArgs k rest (used + 1) (acc.push body)
  | k + 1, .ctrl n p :: rest, used, acc => edefArgs k rest (used + 1) (acc.push #[.ctrl n p])
  | _ + 1, _, _, _ => none

private theorem sizeOf_drop_le (l : List Raw) : ∀ k, sizeOf (l.drop k) ≤ sizeOf l := by
  induction l with
  | nil => intro k; cases k <;> simp
  | cons x xs ih =>
    intro k
    cases k with
    | zero => simp
    | succ k =>
      have := ih k
      simp only [List.drop_succ_cons, List.cons.sizeOf_spec]
      omega

/-- An `\edef` text expanded left to right in `budget` steps, with the steps left: text, groups and a
control after `\noexpand` stand, `\the`, `\number` and `\strip@pt` print a length or a `\dimexpr`,
and another control is a call `call` expands. -/
private def edefWalk (call : String → Pos → List Raw → Nat → Option (Array Raw × Nat × Nat))
    (lenOf : String → Option Rat) (l : List Raw) (acc : Array Raw) (budget : Nat) :
    Option (Array Raw × Nat) :=
  if budget == 0 then none else
  match l with
  | [] => some (acc, budget)
  | .space :: rest => edefWalk call lenOf rest (acc.push .space) (budget - 1)
  | .word w p :: rest => edefWalk call lenOf rest (acc.push (.word w p)) (budget - 1)
  | .sym c p :: rest => edefWalk call lenOf rest (acc.push (.sym c p)) (budget - 1)
  | .group body p :: rest =>
    (edefWalk call lenOf body.toList #[] (budget - 1)).bind fun (inner, left) =>
      edefWalk call lenOf rest (acc.push (.group inner p)) left
  | .ctrl "noexpand" _ :: .ctrl m q :: rest =>
    edefWalk call lenOf rest (acc.push (.ctrl m q)) (budget - 1)
  | .ctrl n p :: rest =>
    if n == "the" || n == "number" || n == "strip@pt" then
      (edefDimen lenOf rest).bind fun (v, used) =>
        edefWalk call lenOf (rest.drop used) (acc.push (.word (edefPrint n v) p)) (budget - 1)
    else
      (call n p rest (budget - 1)).bind fun (text, used, left) =>
        edefWalk call lenOf (rest.drop used) (acc ++ text) left
  | .par _ :: _ | .math .. :: _ | .env .. :: _ | .verb .. :: _ => none
termination_by sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := sizeOf_drop_le rest used; omega)
    | raws_dec

/-- An `\edef` text expanded where it is defined: a call of a definition in `defs` expands its text
with that definition unavailable below it, so the calls form no cycle, and a control `stands` names
is left as written. -/
private def edefExpand (defs : List (String × CondVal)) (stands : String → Bool)
    (lenOf : String → Option Rat) (l : List Raw) (budget : Nat) : Option (Array Raw × Nat) :=
  edefWalk (fun n p rest left =>
    match _h : defs.find? (·.1 == n) with
    | some d =>
      (edefArgs d.2.arity rest 0 #[]).bind fun (args, used) =>
        (edefExpand (defs.eraseP (·.1 == n)) stands lenOf
          (bindRawArgsList args #[] d.2.raws.toList).toList left).map fun (text, rest) =>
            (text, used, rest)
    | none => if stands n then some (#[.ctrl n p], 0, left) else Option.none) lenOf l #[] budget
termination_by defs.length
decreasing_by
  have hm := List.mem_of_find?_eq_some _h
  rw [List.length_eraseP_of_mem hm (List.find?_some _h)]
  have := List.length_pos_of_mem hm
  omega

/-- The definitions an `\edef` text can call, each looked up once: every name it or a text it reaches
mentions that is bound to a readable text with no optional argument and no `\protected` prefix;
`none` past the cap. -/
private def edefReach (binds : Std.HashMap String (Option CondVal)) (body : Array Raw) :
    Option (List (String × CondVal)) := Id.run do
  let mut todo : Array (Array Raw) := #[body]
  let mut seen : Std.HashSet String := {}
  let mut defs : Array (String × CondVal) := #[]
  for _ in [0:edefCap] do
    let some rs := todo.back? | return some defs.toList
    todo := todo.pop
    for r in rs do
      match r with
      | .ctrl n _ =>
        unless seen.contains n do
          seen := seen.insert n
          if let some (some c) := binds[n]? then
            if c.optional.isNone && !c.prot then
              defs := defs.push (n, c)
              todo := todo.push c.raws
      | .group inner _ => todo := todo.push inner
      | _ => pure ()
  return none

/-- The value the definer `d` at `raws[i]` gives the name it binds: body,
undelimited arity and prefixes. -/
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
    | some (.group body gp) =>
      return some { raws := body, arity, long, prot, edges := (gp.openEol, gp.closeEol) }
    | _ => return none
  if d == "edef" || d == "xdef" then
    let j := skipSpaces raws (i + 1)
    match raws[j]?, raws[j + 1]? with
    | some (.ctrl _ _), some (.group body gp) =>
      -- `\edef` leaves `\relax`, a length register and a `\protected` definition unexpanded.
      let stands (m : String) : Bool := m == "relax" || st.newLengths.contains m ||
        match st.binds[m]? with
        | some (some c) => c.prot
        | _ => false
      let text := (edefReach st.binds body).bind fun defs =>
        edefExpand defs stands (fun m => st.exactLens[m]?) body.toList edefCap
      -- Its text is final, so each use expands to it where the pass meets the use.
      return text.map fun (text, _) =>
        { raws := text, long, prot, live := true, edges := (gp.openEol, gp.closeEol) }
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
    | some (.group body gp) =>
      return some {
        raws := body, arity, optional
        long := arity > 0 && !star, prot := false, edges := (gp.openEol, gp.closeEol) }
    | _ => return none
  return none

/-- Whether the definer `d` at `raws[i]` defines globally. -/
private def definesGlobally (raws : Array Raw) (i : Nat) (d : String) : Bool :=
  d == "gdef" || d == "xdef" || (definerPrefixes raws i).contains "global"

/-- The documented `\newtcolorbox{name}[arity][default]{keys}`
head, read for its shape only. -/
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

/-- The control words between a `\foreach` and its `in`: its
variables and a `count=` counter. -/
private def condForeachVars (rs : List Raw) : Array String :=
  let head := rs.takeWhile fun r => !(r matches .word "in" _) && !(r matches .group _ _)
  (head.filterMap condCtrlName).toArray

mutual

-- conserves: none — answers a set of names
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
    undo := st.undo.size, globals := st.globals.size, lens := st.lenGlobals.size
    picBound := st.picBound.size, primitives := st.primitiveScopes.size }

/-- Sets whether the pass reads a spliced file's top level,
returning the value it replaces. -/
private def swapTop (b : Bool) : M Bool := do
  let old := (← get).fileTop
  write fun st => { st with fileTop := b }
  return old

/-- Whether `r` stands on source line `l`; a paragraph break ends the line. -/
private def onLine (l : Nat) : Raw → Bool
  | .space => true
  | .par _ => false
  | .word _ p | .ctrl _ p | .sym _ p | .group _ p | .math _ _ p | .env _ _ p
  | .verb _ _ p => p.line == l

/-- Unwinds the save stack to `m`, latest change first. -/
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
    | some (.len x prev) =>
      write fun st => { st with
        exactLens := match prev with
          | some v => st.exactLens.insert x v
          | none => st.exactLens.erase x }
    | none => pure ()

/-- Closes a TeX group: the save stack unwinds to its mark and only its global
definitions and length assignments outlive it. -/
private def condClose (m : CondMark) : M Unit := do
  let made := (← get).globals.extract m.globals (← get).globals.size
  let lens := (← get).lenGlobals.extract m.lens (← get).lenGlobals.size
  condUnwind m
  for (n, v) in made do setBind n v
  for (n, v) in lens do setExactLen n v false

/-- Ends the document's opening space scan at a nonexpandable token. -/
private def condStopSpaces : M Unit := do
  if (← get).ignoreSpaces then write fun st => { st with ignoreSpaces := false }

/-- A recognised box's preparation; its arguments are consumed even when
preparation is refused. -/
private inductive BoxPreparation where
  | ready (prepared : Tcolorbox.Prepared)
  | refused

/-- An executed prefix and the next unread source index, with a split word's
remainder kept apart. -/
private structure CondRun where
  raws : Array Raw
  stop : Nat
  tail : Array Raw := #[]
  box : Option BoxPreparation := none

/-- beamer's block templates, per kind: the begin and end elements, the `\style`
element, and the font and colour elements. -/
private def blockTemplateKinds : List (Ir.TitledKind × String × String × String × String × String) :=
  [(.block, "block begin", "block end", "block", "block title", "block body"),
   (.alert, "block alerted begin", "block alerted end", "alertblock", "block title alerted",
     "block body alerted"),
   (.example, "block example begin", "block example end", "exampleblock", "block title example",
     "block body example")]

/-- Is `el` one of the block templates the reader reads? -/
private def blockTemplateElement (el : String) : Bool :=
  blockTemplateKinds.any fun (_, b, e, _) => b == el || e == el

mutual

-- conserves: none — the control words a raw list names
private def namesIn (acc : Array String) : List Raw → Array String
  | [] => acc
  | r :: rest => namesIn (namesOf acc r) rest

private def namesOf (acc : Array String) : Raw → Array String
  | .ctrl n _ => if acc.contains n then acc else acc.push n
  | .group body _ | .env _ body _ | .math _ body _ => namesIn acc body.toList
  | .word .. | .space | .par _ | .sym .. | .verb .. => acc

end

/-- A block template's body after its definer's name, and the index past it. -/
private def templateBodyAt (definer : String) (rest : Array Raw) : Option (Array Raw × Nat) :=
  let j := skipSpaces rest 0
  let j := match rest[j]? with
    | some (.word "*" _) | some (.sym '*' _) => j + 1
    | _ => j
  let (head, j) := takeGroups rest j (if definer == "defbeamertemplate" then 2 else 1)
  let element := (rawSrc (head.getD 0 #[])).trimAscii.toString
  if head.size != (if definer == "defbeamertemplate" then 2 else 1) || !blockTemplateElement element
  then none else
  let j := if definer == "defbeamertemplate" then (takeRawOpt rest (takeOpt rest j).2).2 else j
  let (body, k) := takeGroups rest j 1
  body[0]?.map (·, k)

mutual

-- conserves: none — the bodies of the block templates a raw list installs
private def templateBodiesIn (acc : Array (Array Raw)) : List Raw → Array (Array Raw)
  | [] => acc
  | .ctrl n p :: rest =>
    if n == "defbeamertemplate" || n == "setbeamertemplate" then
      match templateBodyAt n rest.toArray with
      | some (body, _) => templateBodiesIn (acc.push body) rest
      | none => templateBodiesIn acc rest
    else templateBodiesIn (templateBodiesOf acc (.ctrl n p)) rest
  | r :: rest => templateBodiesIn (templateBodiesOf acc r) rest

private def templateBodiesOf (acc : Array (Array Raw)) : Raw → Array (Array Raw)
  | .group body _ | .env _ body _ => templateBodiesIn acc body.toList
  | .ctrl .. | .math .. | .word .. | .space | .par _ | .sym .. | .verb .. => acc

end

/-- A definition after its definer `d`: the macro it defines
and how many raws it spans. -/
private def definitionAt (d : String) (rest : Array Raw) : Option (String × Nat) :=
  let j := skipSpaces rest 0
  let j := match rest[j]? with
    | some (.word "*" _) | some (.sym '*' _) => skipSpaces rest (j + 1)
    | _ => j
  if d == "newcommand" || d == "renewcommand" || d == "providecommand" ||
      d == "DeclareRobustCommand" then
    let named : Option String := match (rest[j]? : Option Raw) with
      | some (.group body _) =>
        match body.toList.filter (fun r => !(r matches .space)) with
        | [.ctrl x _] => some x
        | _ => none
      | some (.ctrl x _) => some x
      | _ => none
    named.bind fun x =>
      let k := (takeRawOpt rest (takeOpt rest (j + 1)).2).2
      let (body, k) := takeGroups rest k 1
      if body.size == 1 then some (x, k) else none
  else if d == "def" || d == "gdef" || d == "edef" || d == "xdef" then
    match (rest[j]? : Option Raw) with
    | some (.ctrl x _) =>
      (((rest.extract (j + 1) rest.size).findIdx? (· matches .group ..)).map
        fun g => (x, j + 1 + g + 1))
    | _ => none
  else none

mutual

-- conserves: none — the control words named outside block templates
private def namesOutsideIn (code acc : Array String) (skip : Nat) : List Raw → Array String
  | [] => acc
  | r :: rest =>
    if skip > 0 then namesOutsideIn code acc (skip - 1) rest else
    match r with
    | .ctrl n _ =>
      let named := if acc.contains n then acc else acc.push n
      if n == "defbeamertemplate" || n == "setbeamertemplate" then
        match templateBodyAt n rest.toArray with
        | some (_, k) => namesOutsideIn code acc k rest
        | none => namesOutsideIn code named 0 rest
      else match definitionAt n rest.toArray with
        | some (x, k) =>
          if code.contains x then namesOutsideIn code acc k rest
          else namesOutsideIn code named 0 rest
        | none => namesOutsideIn code named 0 rest
    | .group .. | .env .. | .math .. | .word .. | .space | .par _ | .sym .. | .verb .. =>
      namesOutsideIn code (namesOutsideOf code acc r) 0 rest

private def namesOutsideOf (code acc : Array String) : Raw → Array String
  | .group body _ | .env _ body _ | .math _ body _ => namesOutsideIn code acc 0 body.toList
  | .ctrl .. | .word .. | .space | .par _ | .sym .. | .verb .. => acc

end

/-- The control words `seeds` name, closed over the
definitions `binds` holds for them. -/
private def closeNames (binds : Std.HashMap String (Option CondVal)) (seeds : Array String) :
    Array String := Id.run do
  let mut reach := seeds
  for _ in [0:binds.size + 1] do
    let next := reach.foldl (fun acc n => match binds[n]? with
      | some (some v) =>
        namesIn (match v.optional with
          | some (_, d) => namesIn acc d.toList
          | none => acc) v.raws.toList
      | _ => acc) reach
    if next.size == reach.size then break
    reach := next
  return reach

/-- The control words a preamble's block templates reach as TeX runs them. -/
private def templateClosure (binds : Std.HashMap String (Option CondVal)) (pre : Array Raw) :
    Array String :=
  closeNames binds ((templateBodiesIn #[] pre.toList).foldl (fun acc b => namesIn acc b.toList) #[])

/-- The macros a preamble's block templates reach, less any
the preamble names elsewhere. -/
private def templateReach (binds : Std.HashMap String (Option CondVal)) (pre : Array Raw) :
    Array String := Id.run do
  let reach := templateClosure binds pre
  let code := reach.filter fun n => binds[n]? matches some (some _)
  let elsewhere := namesOutsideIn code #[] 0 pre.toList
  return code.filter (!elsewhere.contains ·)

/-- The `\newif` flag a control word tests, when either state records it. -/
private def testedFlag (a b : Std.HashMap String Bool) (n : String) : Option String :=
  let x := (n.drop 2).toString
  if n.startsWith "if" && n.length > 2 && (a.contains x || b.contains x) then some x else none

/-- Notes each control word a block's templates reach whose meaning or flag
differs from where the body began. -/
private def noteTemplateDrift : M Unit := do
  let st ← get
  let serialOf (b : Std.HashMap String (Option CondVal)) (x : String) : Option (Option Nat) :=
    b[x]?.map (·.map (·.serial))
  let drift := st.templateNames.filter fun x =>
    !st.templateDrift.contains x &&
    (serialOf st.binds x != serialOf st.templateBinds x ||
      (testedFlag st.flags st.templateFlags x).any fun f => st.flags[f]? != st.templateFlags[f]?)
  unless drift.isEmpty do write fun st => { st with templateDrift := st.templateDrift ++ drift }

/-- Whether a control word is a unit or glue keyword inside
a value rather than a register. -/
private def valueCtrl (n : String) : Bool :=
  n == "p@" || n == "z@" || n == "@plus" || n == "@minus"

/-- The raw standing before index `i`, spaces skipped. -/
private def rawBefore (raws : Array Raw) (i : Nat) : Option Raw := Id.run do
  let mut k := i
  for _ in [0:i] do
    k := k - 1
    match raws[k]? with
    | some .space => pure ()
    | r => return r
  return none

/-- Whether the raw before a register reads it as an
operand, so no assignment opens there. -/
private def readsOperand : Option Raw → Bool
  | some (.ctrl c _) => ["hskip", "vskip", "kern", "mskip", "mkern", "the", "showthe",
      "advance", "multiply", "divide", "ifdim", "ifnum", "ifodd", "ifcase", "dimexpr",
      "glueexpr", "numexpr", "muexpr", "raise", "lower", "moveleft", "moveright"].contains c
  | some (.word w _) =>
    ["by", "plus", "minus", "to", "spread", "width", "height", "depth", "=", "<", ">"].contains w ||
      (!w.isEmpty && w.toList.all fun ch => ch.isDigit || ch == '.' || ch == '-' || ch == '+')
  | some (.sym c _) => "=<>+-*/(".toList.contains c
  | _ => false

/-- The LaTeX length assignments the conditional pass reads. -/
private def lengthAssigns : List String :=
  ["newlength", "setlength", "addtolength", "settowidth", "settoheight", "settodepth",
   "settototalheight"]

/-- The TeX register arithmetic, whose target is the next control word. -/
private def lengthArith : List String := ["advance", "multiply", "divide"]

/-- Whether the register at `raws[i]` is assigned there, as TeX's main loop reads a register token:
not after an operand reader (`readsOperand`), and before a value, which at a list's start must be
`=` or a number, since a register opening an argument is read. -/
private def assignsAt (regs : String → Bool) (raws : Array Raw) (i : Nat) : Bool :=
  let j := skipSpaces raws (i + 1)
  match rawBefore raws i with
  | none => match raws[j]? with
    | some (.word w _) => w.front == '=' || w.front == '.' || w.front.isDigit
    | some (.sym '=' _) => true
    | _ => false
  | before =>
    !readsOperand before && match raws[j]? with
      | some (.word w _) => w.front == '=' || w.front == '.' || w.front == '-' || w.front.isDigit
      | some (.sym c _) => c == '=' || c == '-' || c == '+'
      | some (.ctrl c _) => valueCtrl c || regs c || (paramSites.lookup c).isSome
      | _ => false

/-- The register a length assignment or arithmetic at `raws[i]` targets: the next control word,
braced or not. -/
private def lengthTarget (raws : Array Raw) (i : Nat) : Option String :=
  match raws[skipSpaces raws (i + 1)]? with
  | some (.ctrl m _) => some m
  | some (.group rs _) => match (rs.filter (!· matches .space)).toList with
    | [.ctrl m _] => some m
    | _ => none
  | _ => none

/-- The controls a text assigns when it runs, in its groups too: the targets of its length
assignments and arithmetic and each control `regs` names that it assigns bare, `\global` among them
when it assigns globally; `none` past the cap. -/
private def assignedIn (regs : String → Bool) (rs : Array Raw) : Option (Array String) := Id.run do
  let mut todo : Array (Array Raw) := #[rs]
  let mut out : Array String := #[]
  for _ in [0:edefCap] do
    let some cur := todo.back? | return some out
    todo := todo.pop
    for k in [0:cur.size] do
      match cur[k]? with
      | some (.ctrl n _) =>
        if n == "global" || n == "gdef" || n == "xdef" then out := out.push "global"
        else if lengthAssigns.contains n || lengthArith.contains n then
          if let some t := lengthTarget cur k then out := out.push t
        else if regs n && assignsAt regs cur k then out := out.push n
      | some (.group inner _) => todo := todo.push inner
      | some (.env _ inner _) => todo := todo.push inner
      | _ => pure ()
  return none

/-- The texts a call of `n` can run, each looked up once: its definition's and every definition
they mention; `none` past the cap. -/
private def runReach (binds : Std.HashMap String (Option CondVal)) (n : String) :
    Option (Array (Array Raw)) := Id.run do
  let mut todo : Array String := #[n]
  let mut seen : Std.HashSet String := {}
  let mut texts : Array (Array Raw) := #[]
  for _ in [0:edefCap] do
    let some m := todo.back? | return some texts
    todo := todo.pop
    unless seen.contains m do
      seen := seen.insert m
      if let some (some c) := binds[m]? then
        texts := texts.push c.raws
        let mut groups : Array (Array Raw) := #[c.raws]
        for _ in [0:c.raws.size + 1] do
          let some g := groups.back? | break
          groups := groups.pop
          for r in g do
            match r with
            | .ctrl k _ => todo := todo.push k
            | .group inner _ => groups := groups.push inner
            | _ => pure ()
  return none

/-- Forgets each tracked length in `names`, which code the pass does not run assigns: in the current
group, or everywhere when `names` holds `\global`. -/
private def forgetLengths (names : Array String) : M Unit := do
  let global := names.contains "global"
  for t in names do
    if (← get).exactLens.contains t then setExactLen t none global

/-- The controls the environment an environment definer at `raws[i]` defines assigns in its code,
which runs where the environment opens. -/
private def condNoteEnv (raws : Array Raw) (i : Nat) : M Unit := do
  let j := skipSpaces raws (skipStar raws (i + 1))
  let (_, k) := takeOpt raws (j + 1)
  let (_, k) := takeOpt raws k
  let (codes, _) := takeGroups raws k 2
  let some name := definedEnv raws i | return
  let assigned := (codes.toList.filterMap (assignedIn (fun _ => true))).foldl (· ++ ·) #[]
  write fun st => { st with envAssigns := st.envAssigns.insert name assigned }

/-- The control at `raws[i]` on the lengths the pass follows: `\newlength` allocates one at zero,
`\setlength` and `\addtolength` evaluate it, and any other assignment, one undecided, or code the
pass does not run that assigns one forgets it. -/
private def condNoteLength (raws : Array Raw) (i : Nat) (n : String) (undecided : Bool) :
    M Unit := do
  let st ← get
  let look (m : String) : Option Rat := st.exactLens[m]?
  let global := (definerPrefixes raws i).contains "global"
  if lengthAssigns.contains n || lengthArith.contains n then
    let some target := lengthTarget raws i | return
    if n == "newlength" then
      write fun st => { st with newLengths := st.newLengths.insert target }
      setExactLen target (if undecided then none else some 0) true
    else if st.newLengths.contains target then
      let operand : Option Rat := match raws[skipSpaces raws (skipSpaces raws (i + 1) + 1)]? with
        | some (.group v _) => Decl.exactLength look (rawSrc v)
        | _ => none
      let value : Option Rat := if undecided then none else match n with
        | "setlength" => operand
        | "addtolength" => (look target).bind fun old => operand.map (old + ·)
        | _ => none
      setExactLen target value global
  else if Definer.envs.contains n then condNoteEnv raws i
  else if st.exactLens.contains n then
    if assignsAt st.exactLens.contains raws i then setExactLen n none global
  else if let some (some v) := st.binds[n]? then
    unless v.live do
      let texts := (runReach st.binds n).getD #[]
      let assigned := texts.toList.filterMap (assignedIn st.exactLens.contains)
      if assigned.length < texts.size then forgetLengths (st.exactLens.keys.toArray.push "global")
      else forgetLengths (assigned.foldl (· ++ ·) #[])

mutual

/-- The decidable conditionals resolved at one level; `stack` holds every open
conditional, innermost first. -/
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
    -- `\newif\ifX` declares a decidable flag, initially false.
    if !(stack.all CondOpen.keeps) then
      condList ex [] raws following out stack rest (i + 2) 0
    else if n.startsWith "if" && n.length > 2 then
      condStopSpaces
      let x := (n.drop 2).toString
      setFlag x false
      recordDefined n
      recordDefined (x ++ "true")
      recordDefined (x ++ "false")
      -- premise: settleChecks — a settled text is read, not run
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
      -- premise: settleChecks — a settled text is read, not run
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
    -- `\endinput` cuts only a file's own top level, after the rest of its line.
    if !(stack.all CondOpen.keeps) then
      condList ex [] raws following out stack rest (i + 1) 0
    -- premise: endInputChecks — a wrapper's top level is a file's own text
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
    let unlessHead : Option (String × Pos) := if n == "unless" then
        match rest with
        | .ctrl h hp :: _ => if isCondHead st.flags h then some (h, hp) else none
        | _ => none
      else none
    let head := (unlessHead.map (·.1)).getD n
    let hi := if unlessHead.isSome then i + 1 else i
    if isCondHead st.flags head then
      if stack.isEmpty && !condExtent st.flags raws hi then
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
    else if let some (_, k) := (if n == "defbeamertemplate" || n == "setbeamertemplate" then
        templateBodyAt n (raws.extract (i + 1) raws.size) else none) then
      -- A block template's body passes through unexpanded for the template reader.
      let out := (raws.extract i (i + 1 + k)).foldl (fun o r => o.push r) out
      condList ex [] raws following out stack rest (i + 1) k
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
        -- premise: Tests.macroHookScopeChecks — hooks execute at their seam
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
      -- premise: Tests.stringConditionalChecks — the unselected branch stays inert
      let msg := if ans then
          "'\\ifstrequal': the literal strings agree, so the first branch is kept"
        else "'\\ifstrequal': the literal strings differ, so the second branch is kept"
      sayOnce ("string-test:" ++ msg) .N0114 msg (st.useSite.getD pos)
      condList ex [false, false, ans, !ans] raws following out stack rest (i + 1) 0
    else if let some (test, query) := (loadedTests.find? (·.ctrl == n)).bind fun test =>
        (loadedAt raws (i + 1) test).map (test, ·) then
      -- premise: loadedTestChecks — selected branches execute where the test stands
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
      let (_, k, _) := takeHookArgs raws (i + 1)
      condList ex [] raws following ((out.push (.ctrl n pos)) ++ raws.extract (i + 1) k)
        stack rest (i + 1) (k - (i + 1))
    else if n.endsWith "true" && st.flags.contains (n.dropEnd 4).toString then
      condStopSpaces
      let x := (n.dropEnd 4).toString
      setFlag x true
      -- premise: settleChecks — a settled text is read, not run
      unless st.settling.isSome do
        sayOnce ("cond:set:" ++ n) .N0114 s!"'\\{n}': '\\if{x}' is true from here on"
          (st.useSite.getD pos)
      condList ex [] raws following out stack rest (i + 1) 0
    else if n.endsWith "false" && st.flags.contains (n.dropEnd 5).toString then
      condStopSpaces
      let x := (n.dropEnd 5).toString
      setFlag x false
      -- premise: settleChecks — a settled text is read, not run
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
          -- premise: TcolorboxChecks.tcolorboxScopeChecks — refused definitions change nothing
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
    else if Definer.xparseEnvs.contains n && ignoredEnvDef st.ignoredDefs raws i n then
      condStopSpaces
      let j := skipSpaces raws (i + 1)
      let (groups, stop) := takeGroups raws j 4
      -- premise: ignoredDefinitionChecks — an ignored built-in's definition text runs nowhere
      if groups.size == 4 then
        let named : Raw := (raws[j]?).getD (.group #[] pos)
        condList ex [] raws following
          ((((out.push (.ctrl "renewenvironment" pos)).push named).push (.group #[] pos)).push
            (.group #[] pos)) stack rest (i + 1) (stop - (i + 1))
      else condList ex [] raws following (out.push (.ctrl n pos)) stack rest (i + 1) 0
    else if Definer.readAsDefinition.contains n then
      condStopSpaces
      let bound := if Definer.bindsNext.contains n then
          (rest.dropWhile isSpaceOrStar).head?.bind boundName
        else none
      let provide := Definer.provides n
      let ignored := match bound with
        | some m => st.ignoredDefs.contains m
        | none => ignoredEnvDef st.ignoredDefs raws i n
      -- premise: ignoredDefinitionChecks — an ignored built-in's definition text runs nowhere
      if ignored && !provide then
        if let some sh := definerShape raws i n then
          -- `\let` defines the name too, spelled here as the definer the rewrite reads.
          let (head, ops) : String × List Raw := if n == "let" then
              ("def", (raws[skipSpaces raws (i + 1)]?).toList ++ [Raw.group #[] pos])
            else (n, (List.range' (i + 1) (sh.stop - (i + 1))).filterMap fun k =>
              raws[k]?.map fun (r : Raw) => match r with
                | .group _ gp => if sh.bodies.contains k then Raw.group #[] gp else r
                | _ => r)
          return ← condList ex [] raws following ((out.push (.ctrl head pos)) ++ ops.toArray) stack
            rest (i + 1) (sh.stop - (i + 1))
      if Definer.envs.contains n then condNoteEnv raws i
      if let some m := bound then
        -- premise: Tests.xparseIgnoredOperandsChecks — ignored operands change no artifact
        if provide && (st.binds.contains m || st.provideKeeps.contains m ||
            (TikzCommands.pgfDefined.contains m && st.loads.pgf)) then
          if let some sh := definerShape raws i n then
            let why := if st.binds.contains m then
                s!"'\\{m}' is already defined and the existing definition is kept"
              else s!"'\\{m}' is built in and the built-in stands"
            discard s!"\\{n}\{\\{m}}" why s!"{n}:{m}" (st.useSite.getD pos)
            return ← condList ex [] raws following out stack rest (i + 1) (sh.stop - (i + 1))
        unless provide && st.binds.contains m do
          -- Inside an undecidable frame the name is bound but its value unread.
          let value := definedValue st raws i n
          let v := if stack.any (· matches .opaque) then none else value
          let global := definesGlobally raws i n
          -- A `\let` copies the wrapper, not its target.
          if n != "let" then
            if let some (key, _) := value.bind (·.optional) then
              recordValue key (v.map fun c => { c with optional := none }) global
          recordValue m v global (copied := n == "let")
      match definerShape raws i n with
      | none => condList ex [] raws following (out.push (.ctrl n pos)) stack rest (i + 1) 0
      | some sh =>
        -- The texts expand where the definition is used, never here.
        let st ← get
        -- premise: tcolorboxTitleBindingChecks — title-local definitions leave no inline syntax
        if st.materializeTitle &&
            (bound.bind (condValueOf st.binds ·)).any Option.isSome &&
            !(bound.any st.provideKeeps.contains) then
          let kept := (definerPrefixes raws i).reverse.foldl (init := out.raws.toList.reverse)
            fun rs name => match rs.dropWhile (· matches .space) with
              | .ctrl found _ :: rest => if found == name then rest else rs
              | _ => rs
          let out := OverlayPrefix.ofArray kept.reverse.toArray
          let stop := ((definerShape raws i n (stored := true)).getD sh).stop
          became s!"\\{n}\\{bound.getD n}" "a scoped title binding"
            (st.useSite.getD pos) (subject := bound)
          return ← condList ex [] raws following out stack rest (i + 1) (stop - (i + 1))
        let liveVal := match bound.bind (condValueOf st.binds ·) with
          | some (some v) => if v.live then some v else none
          | _ => none
        -- A built-in the pass never expands is settled at the preamble's end.
        let expands := liveVal.isSome && !(bound.any st.provideKeeps.contains)
        -- premise: Tests.macroDefaultChecks — copied readable meanings execute at their uses
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
          -- premise: Tests.macroArgumentChecks — readable undelimited calls execute after binding
          sayOnce ("cond:body:" ++ n ++ ":" ++ (bound.getD "")) .W0104
            (s!"'\\{n}' makes a definition whose text holds a conditional, a flag \
setting or another definition, which TeX executes where it is used; this engine cannot \
execute this definition there, so that part of the text is skipped whole")
            (site.getD pos)
            (help := "use \\def with undelimited arguments or \\newcommand")
        -- An `\edef` the pass expanded is done: its uses expand to its text, so it goes out as nothing.
        let j := skipSpaces raws (i + 1)
        if (n == "edef" || n == "xdef") && expands then
          became s!"\\{n}\\{bound.getD n}" "its text, expanded where it stands and used at each call"
            (site.getD pos) (subject := bound)
          return ← condList ex [] raws following out stack rest (i + 1) (j + 1 - i)
        condList ex [] raws following ((out.push (.ctrl n pos)) ++ ops) stack rest (i + 1)
          (sh.stop - (i + 1))
    else if condNoExpand.contains n then
      condStopSpaces
      match rest with
      | r :: _ => condList ex [] raws following ((out.push (.ctrl n pos)).push r) stack rest (i + 1) 1
      | [] => condList ex [] raws following (out.push (.ctrl n pos)) stack rest (i + 1) 0
    else
      if (lengthAssigns ++ lengthArith ++ Definer.envs).contains n || !st.exactLens.isEmpty then
        condNoteLength raws i n (stack.any (· matches .opaque))
      if !st.condInDoc then recordLoad raws n i
      -- premise: Tests.overlayInputChecks — a selector reads macro fragments at its use
      if out.scan.opened then
        let r := match overlayFragment st.binds st.binds.size n with
          | some text => .word text pos
          | none => .ctrl n pos
        -- A refused fragment stays inside the selector unexecuted.
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

/-- Descends into a group, math or an environment body,
restoring the definition state at its close. -/
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
        -- premise: Tests.macroPhaseChecks — only opening spaces disappear
        write fun st => { st with ignoreSpaces := true }
      else condStopSpaces
      if (← get).condInDoc && overlayTitled (overlayName n) then noteTemplateDrift
      let m ← condMark
      if let some names := (← get).envAssigns[n]? then forgetLengths names
      let inPic := (← get).inPicture
      if pictureEnvs.contains n then
        let names := condBoundLevel #[] body.toList
        write fun st => { st with picBound := st.picBound ++ names, inPicture := true }
      let top ← swapTop false
      let box ← ex (Tcolorbox.bindingName n) p body 0
      let head := if overlayTitled n then #[Raw.ctrl "titled overlay" p] else #[]
      let front := head ++ (box.map (·.tail)).getD #[]
      let body' ← condList ex [] body #[] (OverlayPrefix.ofArray front) [] body.toList 0
        ((box.map (·.stop)).getD 0)
      let result ← match box.bind (·.box) with
        | some (.ready prepared) => do
          let lowered := prepared.lower body'.raws p
          became s!"\\begin\{{n}}" "a native block" p
          for key in lowered.inPart do
            sayOnce ("partial:\\begin{" ++ n ++ "}:" ++ key) .W0110
              s!"'\\begin\{{n}}' key '{key}' is not fully applied: the native block spaces the box" p
              (help := "use native block styles for portable decoration")
          for key in lowered.unsupported do
            unreadParam s!"\\begin\{{n}}" key s!"'\\begin\{{n}}' key '{key}'" p
              (help := "use native block styles for portable decoration")
          unless lowered.refusedValues.isEmpty do
            write fun st => { st with mentions := st.mentions ++ lowered.refusedValues }
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

/-- A readable command's optional first argument and
remaining undelimited arguments, bound. -/
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

-- conserves: none — a predicate over surface tokens
/-- Whether a substituted replacement can neither request
another expansion nor execute a control. -/
private def condTerminalList : List Raw → Bool
  | [] => true
  | r :: rest => condTerminalRaw r && condTerminalList rest

private def condTerminalRaw : Raw → Bool
  | .group body _ | .math _ body _ => condTerminalList body.toList
  | .ctrl _ _ | .env _ _ _ => false
  | .word _ _ | .space | .par _ | .sym _ _ | .verb _ _ _ => true

end

/-- The request of an unbound input command at its executed site. -/
private def inputRequestAt (st : St) (n : String) (pos : Pos)
    (raws : Array Raw) (start : Nat) : Option (InputRequest × Nat) := do
  if st.settling.isSome then none else do
    let input := inputCommands.contains n
    -- premise: frontendInputRequestChecks — only live execution loads a local style
    let style := !st.condInDoc &&
      (n == "usepackage" || n == "RequirePackage" || (themeAsking.lookup n).isSome)
    if !(input || style) then none else do
      let optioned := ["markdownInput", "inputminted", "inputlean"].contains n
      let (_, k) := if optioned || style then takeOpt raws start else (none, start)
      let j := skipSpaces raws k
      let some (.group _ _) := raws[j]? | none
      -- minted's file command names its language in a group before the file's.
      let j ← if n == "inputminted" then
          let j' := skipSpaces raws (j + 1)
          match raws[j']? with
          | some (.group _ _) => some j'
          | _ => none
        else some j
      some ({
        command := n
        file := st.file
        pos := st.useSite.getD pos
        callPos := pos
        operands := raws.extract start (j + 1) }, j + 1)

/-- The flag holding the markdown package's `citations` where a request stands, named by no control
word. -/
private def markdownCitationsFlag : String := "markdown citations"

/-- The flag holding the markdown package's `hybrid` where a request stands, named by no control
word. -/
private def markdownHybridFlag : String := "markdown hybrid"

/-- The flag naming the markdown package loaded, its first load's options standing, named by no
control word. -/
private def markdownLoadedFlag : String := "markdown loaded"

/-- The markdown package's `citations` and `hybrid` set where they are given. -/
private def setMarkdown (opts : MarkdownOptions) : M Unit := do
  if let some b := opts.citations then setFlag markdownCitationsFlag b
  if let some b := opts.hybrid then setFlag markdownHybridFlag b

/-- The markdown package's `citations` and `hybrid` in force where a request stands: as it loaded,
then as `\markdownSetup` sets them for the rest of a group. -/
public def InputContext.markdown (context : InputContext) : MarkdownOptions :=
  { citations := context.state.flags[markdownCitationsFlag]?
    hybrid := context.state.flags[markdownHybridFlag]? }

/-- The context once the markdown package loads with `options`, after the options passed to it
before, as LaTeX applies them; a later load's options apply to nothing. -/
public def InputContext.loadMarkdown (context : InputContext) (options : String) : InputContext :=
  if context.state.flags.contains markdownLoadedFlag then context else
  let passed := (context.state.loads.passed.filter (·.1 == "markdown")).toList.flatMap (·.2.toList)
  let opts := MarkdownOptions.read (",".intercalate (passed ++ PackageImports.literalOptions options))
  let st := (setMarkdown opts context.state).2
  { state := { st with flags := st.flags.insert markdownLoadedFlag true } }

/-- The context with the markdown package's options as `saved` holds them, a file that set them
having ended. -/
public def InputContext.restoreMarkdown (context : InputContext) (saved : MarkdownOptions) :
    InputContext :=
  let put (flags : Std.HashMap String Bool) (x : String) : Option Bool → Std.HashMap String Bool
    | some b => flags.insert x b
    | none => flags.erase x
  { state := { context.state with
      flags := put (put context.state.flags markdownCitationsFlag saved.citations)
        markdownHybridFlag saved.hybrid } }

/-- What an inclusion with `options` reads under, its own over those in force where it stands, and
a note naming every other option it writes. -/
public def InputContext.markdownFor (context : InputContext) (options : String) (site : Span) :
    Bool × Bool × Array Diag :=
  let opts := MarkdownOptions.read options
  let note := if opts.others.isEmpty then #[] else #[Diag.of .W0110 s!"'\\markdownInput' options \
'{", ".intercalate opts.others.toList}' are not applied; the Markdown document dialect reads only \
'citations' and 'hybrid'" (some site) (subject := some "markdownInput:options")]
  (opts.citations.getD (context.markdown.citations.getD false),
    opts.hybrid.getD (context.markdown.hybrid.getD false), note)

/-- `\markdownSetup{options}`: the markdown package's `citations` and `hybrid` set for the rest of
its group, every other option named. -/
private def markdownSetupAt (n : String) (pos : Pos) (raws : Array Raw) (start : Nat) :
    M (Option CondRun) := do
  let st ← get
  if n != "markdownSetup" || st.settling.isSome then return none
  let j := skipSpaces raws start
  let some (.group body _) := raws[j]? | return none
  let opts := MarkdownOptions.read (rawSrc body)
  setMarkdown opts
  -- premise: markdownHybridChecks — the driver reads citations and hybrid where the package does
  unless opts.others.isEmpty do
    say .W0110 s!"'\\markdownSetup' options '{", ".intercalate opts.others.toList}' are not \
applied; the Markdown document dialect reads only 'citations' and 'hybrid'" (st.useSite.getD pos)
      (help := "remove the other options") (subject := some "markdownSetup:options")
  return some { raws := #[], stop := j + 1 }

/-- The unbound-command arm of the production evaluator. -/
private def condReadAt [Monad m] (reader : Option (InputReader m))
    (n : String) (pos : Pos) (raws : Array Raw) (start : Nat) :
    EvalM m (Option CondRun) := do
  let st ← get
  let some (request, stop) := inputRequestAt st n pos raws start |
    return (← markdownSetupAt n pos raws start)
  let some reader := reader | return none
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

/-- Expands the macro `n` where the conditional pass meets it in live content,
when the use's state decides it. -/
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
    -- premise: tcolorboxPreparationChecks — copied helpers remain executable
    if _hstage : prepareBox then
      -- Selected colours are captured before either font hook runs.
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
  -- TikZ restores a document's meanings of its commands in a group of text, one holding no statement.
  let own := st.picBound.contains n || st.provideKeeps.contains n ||
    (inPic && TikzCommands.walkOwned.contains n && raws.any fun r => match r with
      | .word w _ => w.contains ';'
      | _ => false)
  match condValueOf st.binds n with
  | some (some v) =>
    -- premise: Tests.macroDefaultChecks — optional selection changes both artifacts
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
    -- Replacement text executes in the using file, so it is relocated before binding.
    let usePos := site.getD pos
    let atUse := fun p : Pos => { p with line := usePos.line, col := usePos.col }
    let defaultArg := v.optional.map fun (_, arg) => arg.map (rebase atUse false)
    -- premise: Tests.macroHookScopeChecks — copied texts execute locally
    let descends := serial < bound || textSerial < textBound
    -- premise: Tests.macroRoleChecks — a terminal substituted call executes without recursion
    let terminal := !descends &&
      (takeCondArgs raws start body.arity defaultArg).any
        (fun (args, _, _) => args.size == body.arity &&
          condTerminalList (bindRawArgsList args #[] body.raws.toList).toList)
    if descends || terminal then
      let call := (takeCondArgs raws start body.arity defaultArg).filter
        fun (args, _, _) => args.size == body.arity
      let some (args, stop, tail) := call | do
        -- premise: macroForwardArgumentsChecks — an incomplete stored forwarder waits for its use
        if st.settling.isSome then return none
        sayOnce ("cond:arguments:" ++ n) .W0104
          s!"'\\{n}' needs {body.arity} arguments before its replacement text can execute; \
the argument boundary is unread here, so its optional selection and state changes are not applied"
          (site.getD pos)
          (help := "close an optional argument with ']' and put each required argument in braces")
        return none
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

/-- The expander running text uses, with every definition
made so far visible. -/
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
      undo := st.undo.size, globals := st.globals.size, lens := st.lenGlobals.size
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
    (hflags : st.flags = {}) (hlens : st.exactLens = {})
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
  have hdef : Definer.readAsDefinition.contains name = false := by
    rcases hc with rfl | rfl <;> decide
  have hno : condNoExpand.contains name = false := by
    rcases hc with rfl | rfl <;> decide
  have hbox : (name == "newtcolorbox" || name == "renewtcolorbox") = false := by
    rcases hc with rfl | rfl <;> decide
  have htcb : name ≠ "tcbuselibrary" := by
    rcases hc with rfl | rfl <;> decide
  have htpl : (name == "defbeamertemplate" || name == "setbeamertemplate") = false := by
    rcases hc with rfl | rfl <;> decide
  have hlen : ((lengthAssigns ++ lengthArith ++ Definer.envs).contains name ||
      !st.exactLens.isEmpty) = false := by
    have h : (lengthAssigns ++ lengthArith ++ Definer.envs).contains name = false := by
      rcases hc with rfl | rfl <;> decide
    simp only [h, hlens, Std.HashMap.isEmpty_empty, Bool.not_true, Bool.or_false]
  have hxp : (Definer.xparseEnvs.contains name && ignoredEnvDef st.ignoredDefs raws i name) =
      false := by
    have h : Definer.xparseEnvs.contains name = false := by
      rcases hc with rfl | rfl <;> decide
    simp only [h, Bool.false_and]
  rw [condList.eq_16]
  all_goals try solve | simp_all
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure]
  simp only [hn.2.2.2.2.2.1, beq_iff_eq, ↓reduceIte, Option.map_none,
    Option.getD_none, hcond, List.all_nil,
    Bool.not_true, Bool.false_eq_true, hg, hp, Array.back?_empty,
    Option.any_none, hh, hn.2.2.2.2.2.2.1, hl, Option.bind_none,
    hn.2.2.2.2.2.2.2.1, ht, hf,
    hbox, htcb, hdef, hno, hd, Bool.not_false, ho, htpl, hlen, hxp]
  cases hload : recordLoad raws name i st with
  | mk tick loaded =>
    cases tick
    simp only [hload] at he
    simp only [evalLift_id, bind, StateT.bind, hload,
      he, condStopSpaces_quiet after hs]

/-- One live package call with a literal comma-separated name argument. -/
public def packageCall (command names : String) (pos groupPos namePos : Pos) : Array Raw :=
  #[.ctrl command pos, .group #[.word names namePos] groupPos]

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
  have hm : (command == "inputminted") = false := by rcases hc with rfl | rfl <;> decide
  have hm' : command ≠ "inputminted" := by rcases hc with rfl | rfl <;> decide
  have ht := (packageCall_readers command names pos groupPos namePos).2.1
  have hj := (packageCall_readers command names pos groupPos namePos).1
  simp [inputRequestAt, hs, hd, hp, ht, hj, hm, hm']
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
    (hflags : st.flags = {}) (hlens : st.exactLens = {}) (hi : st.ignoreSpaces = false)
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
    hc hp hd hflags hlens rfl hex hi]
  rw [condList_literal_group_exact _ names np gp _ #[] _ 1 attempted hi]
  simp [OverlayPrefix.push, OverlayPrefix.ofArray, packageFailed,
    attempted, loaded, packageLoaded, packageRequest, packageCall, Nat.add_assoc]

/-- A parsed file answer executed in its request's state before the caller
continues; the wrapper opens no TeX group. -/
public def resumeInput [Monad m] (reader : InputReader m) (context : InputContext)
    (raws : Array Raw) (diags : Array Diag := #[]) : m (Array Raw × InputContext) := do
  let (run, state) ←
    (condList (condTopExpand (some reader)) [] raws #[] (OverlayPrefix.ofArray #[]) [] raws.toList 0 0).run
      { context.state with
        diags := context.state.diags ++ diags
        sourceTriggers := sourceTriggers context.state.file context.state.sourceTriggers raws.toList }
  return (run.raws, { state := state })

/-- Runs `act` and restores the definition state, so nothing a settled text
binds outlives its reading. -/
private def condSandbox [Monad m] (act : EvalM m CondRun) : EvalM m (Array Raw) := do
  let saved ← get
  let m ← condMark
  let r ← act
  condUnwind m
  write fun st => { st with
    globals := st.globals.shrink m.globals, lenGlobals := st.lenGlobals.shrink m.lens
    loads := saved.loads, deferred := saved.deferred, ignoreSpaces := saved.ignoreSpaces }
  return r.raws

/-- The pending preamble definitions settled against the
state at the preamble's end. -/
private def condSettle [Monad m] (reader : Option (InputReader m)) (pre : Array Raw) :
    EvalM m (Array (String × Pos × Array Raw)) := do
  let pend := (← get).pending
  write fun st => { st with pending := #[], condInDoc := true
                            templateCode := templateReach st.binds pre }
  let mut out : Array (String × Pos × Array Raw) := #[]
  for p in pend do
    match condValueOf (← get).binds p.name with
    | some (some v) =>
      if v.serial == p.serial && v.arity == 0 then
        let file := (← get).file
        -- premise: templateCodeChecks — a template macro names its losses at its use
        let quiet := (← get).templateCode.contains p.name
        let (said, warned) := ((← get).diags.size, (← get).warned)
        write fun st => { st with file := p.file, settling := some p.name }
        let replacement := bindRawArgsList #[] #[] v.raws.toList
        let body ← condSandbox
          (condList (fun n q rs k => condExpandAt reader v.serial v.textSerial true n q rs k)
            [] replacement #[] (OverlayPrefix.ofArray #[]) [] replacement.toList 0 0)
        write fun st => { st with file := file, settling := none
                                  diags := if quiet then st.diags.extract 0 said else st.diags
                                  warned := if quiet then warned else st.warned }
        out := out.push (p.file, p.pos, body)
    | _ => pure ()
  return out

mutual

-- conserves: none — swaps each settled text in where its definition stands
/-- Each settled text put back into the definition it came
out of, found by its file and position. -/
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

/-- One deferred bucket executed in registration order, in
its declaring files. -/
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

/-- The preamble, its end hooks, the begin-document hooks, then the body,
executed against one shared state. -/
private def condDocument [Monad m] (reader : Option (InputReader m))
    (raws : Array Raw) : EvalM m (Array Raw) := do
  let seam := raws.findIdx? (· matches .env "document" _ _)
  let d := seam.getD raws.size
  let pre := raws.extract 0 d
  let post := raws.extract d raws.size
  let pre' ← condList (condTopExpand reader) [] pre #[] (OverlayPrefix.ofArray #[]) [] pre.toList 0 0
  let hooks := (← get).deferred
  let endHooks ← condReplay reader hooks .endPreamble
  let texts ← if seam.isSome then condSettle reader pre'.raws else pure #[]
  let file := (← get).file
  let patch (file : String) (body : Array Raw) :=
    if texts.isEmpty then body else condPatchList texts file #[] body.toList
  let endHooks := endHooks.map fun (pt, f, pos, body) => (pt, f, pos, patch f body)
  let beginHooks ← condReplay reader hooks .beginDocument
  write fun st => { st with deferred := endHooks ++ beginHooks }
  if seam.isSome then
    write fun st => { st with templateBinds := st.binds, templateFlags := st.flags
                              templateNames := templateClosure st.binds pre'.raws }
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
    (hflags : st.flags = {}) (hlens : st.exactLens = {}) (hi : st.ignoreSpaces = false)
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
      hc hp hd hflags hlens hi hsettling hv hr) hdeferred]
  simp [packageFailed, packageLoaded, Nat.add_assoc, hdeferred]

/-- The dimension spelled past a glue keyword run into it,
as TeX reads `plus2pt`. -/
private def keyRun? (w key : String) : Option String :=
  let rest := (w.drop key.length).toString
  if w.startsWith key && rest.toList.head?.any (fun c => c.isDigit || c == '.' || c == ',' || c == '-' || c == '+')
  then some rest else none

/-- A TeX length in the native spelling: `0.75\beat` is `0.75 * beat`, `\relax`
vanishes, a word reads in lower case. -/
public def lengthSrcBy (ref : String → Bool → Option String) (raws : Array Raw) :
    Option String := Id.run do
  let mut s := ""
  let mut prevNumber := false
  let mut depth := 0
  let mut past := 0
  for h : k in [0:raws.size] do
    if k < past then continue
    match raws[k] with
    | .ctrl "stretch" _ =>
      let g := skipSpaces raws (k + 1)
      let some (.group body _) := raws[g]? | return none
      let lead := if s.isEmpty || s.endsWith " " then "" else " "
      s := s ++ lead ++ s!"0pt plus {(rawSrc body).trimAscii}fill"
      past := g + 1
      prevNumber := false
    | .ctrl "relax" _ =>
      if depth > 0 then
        s := s ++ ")"
        depth := depth - 1
    | .ctrl "dimexpr" _ =>
      s := s ++ (if prevNumber then " * (" else "(")
      depth := depth + 1
      prevNumber := false
    | .ctrl "p@" _ =>
      -- `\p@` is 1pt and `\z@` 0pt (plain.tex); `\@plus`/`\@minus` are the glue keywords.
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
      let t := s.trimAsciiEnd.toString
      let pre := if prevNumber || t.back.isDigit || t.back == '.' then " * "
        else if t == "-" || t.endsWith "(-" then "1 * " else ""
      s := s ++ pre ++ v
      prevNumber := false
    | .word w _ =>
      let w := w.toLower
      let lead := if s.isEmpty || s.endsWith " " then "" else " "
      -- TeX's lexer drops the space after a control word, so a keyword may abut a register.
      let (w, num) := match keyRun? w "plus", keyRun? w "minus" with
        | some rest, _ => (lead ++ "plus " ++ rest, rest)
        | none, some rest => (lead ++ "minus " ++ rest, rest)
        | none, none => (if w == "plus" || w == "minus" then lead ++ w else w, w)
      s := s ++ w
      prevNumber := num.toList.all fun c => c.isDigit || c == '.'
    | .space => s := s ++ " "
    | other => s := s ++ rawSrcOne other
  -- `\dimexpr` ends with its argument when no `\relax` closes it.
  return some (s ++ String.ofList (List.replicate depth ')')).trimAscii.toString

/-- A TeX length in the native spelling, every name standing as itself. -/
private def lengthSrc (raws : Array Raw) : String :=
  (lengthSrcBy (fun n _ => some n) raws).getD ""

/-- The parameter a `\setlength` target names: a control word, or a register
reference such as `\skip\footins`. -/
private def paramName (raws : Array Raw) : Option String :=
  match raws.toList.filter (fun r => match r with | .space => false | _ => true) with
  | [.ctrl n _] => some n
  | [.ctrl "skip" _, .ctrl n _] => some n
  | _ => none

/-- A parameter no engine site reads, named once where it is set. -/
private def nameParam (n why : String) (pos : Pos) : M Unit := do
  sayOnce ("ctrl:setlength:" ++ n) .W0104 s!"'\\{n}' is not honoured: it {why}" pos
    -- premise: paramDemoteChecks — a style file's setting ships the same page
    (demote := packageFile (← get).file)

/-- Lengths a package spells as macros whose redefinition no
engine site reads. -/
private def macroParams : List (String × String) :=
  [("minalignsep", "separates an aligned's column pairs, which stand amsmath's 10 pt apart here")]

/-- The kernel's three vertical skip amounts, the same in every class. -/
public def kernelSkip : String → Option String
  | "smallskipamount" => some "3pt plus 1pt minus 1pt"
  | "medskipamount" => some "6pt plus 2pt minus 2pt"
  | "bigskipamount" => some "12pt plus 4pt minus 4pt"
  | _ => none

/-- Class-independent length defaults readable before an assignment: the skip
amounts and the column gap. -/
private def kernelLength (n : String) : Option String :=
  if n == "columnsep" then some s!"{Ir.columnSep.sp.toPtString}pt" else kernelSkip n

/-- The operand `\ht\strutbox` or `\dp\strutbox` reads as, under a name no document spells. -/
private def strutOperand (dimen : String) : String := dimen ++ " strutbox"

/-- The strut box's height or depth at a `\baselineskip`: latex.ltx's `.7` and `.3` of it, in
TeX's scaled arithmetic. -/
public def strutDimen (dimen : String) (skip : Int) : Int :=
  skip * (if dimen == "ht" then 45875 else 19661) / 65536

/-- A length's raws with `\ht\strutbox` and `\dp\strutbox` each one operand. -/
private def strutOperands (raws : Array Raw) : Array Raw := Id.run do
  let mut out : Array Raw := #[]
  let mut i := 0
  for _ in [0:raws.size] do
    match (raws[i]? : Option Raw) with
    | some (.ctrl d p) =>
      let j := skipSpaces raws (i + 1)
      if (d == "ht" || d == "dp") && raws[j]? matches some (.ctrl "strutbox" _) then
        out := out.push (.ctrl (strutOperand d) p)
        i := j + 1
      else
        out := out.push (.ctrl d p)
        i := i + 1
    | some r =>
      out := out.push r
      i := i + 1
    | none => break
  return out

/-- A length value as the door reads it where it stands; the strut box reads at `strut`, the
`\baselineskip` it was set at, where that is known. -/
private def lenValue (lens : Array (String × String)) (raws : Array Raw)
    (deferred : Bool := false) (preamble : Bool := false) (measureKnown : Bool := true)
    (flowPage : Bool := false) (strut : Option Int := none) : Option String :=
  -- premise: unreadableLengthChecks — a kernel parameter in a definition body stands by name
  let kernel (n : String) : Bool := !deferred && (paramSites.lookup n).isSome
  let set (n : String) : Option String := (lens.find? (·.1 == n)).map (·.2)
  let line (n : String) : Bool := n == "linewidth" || n == "columnwidth"
  let raws := strutOperands raws
  let held (n : String) : Option String :=
    -- premise: columnGeometryChecks — class defaults are readable register values
    if kernel n then (set n).orElse fun _ => kernelLength n
    else if (kernelSkip n).isSome then
      match set n with
      | some v => if deferred then none else some v
      | none => kernelSkip n
    -- premise: strutLengthChecks — the strut box reads where the class's strut stands
    else if n == strutOperand "ht" then
      if deferred then none else strut.map fun s => s!"{strutDimen "ht" s}sp"
    else if n == strutOperand "dp" then
      if deferred then none else strut.map fun s => s!"{strutDimen "dp" s}sp"
    else none
  -- premise: kernelLengthChecks — a flow page without a measure withholds `textwidth`
  let unknown (n : String) : Bool :=
    (kernel n && n != "textwidth") || n == "ht" || n == "wd" || n == "dp" ||
      n == strutOperand "ht" || n == strutOperand "dp" ||
      (!deferred && ((line n && (!preamble || flowPage || (set "textwidth").isSome)) ||
        (preamble && !measureKnown && n == "textwidth")))
  let ref (n : String) (arg : Bool) : Option String :=
    if arg then none
    else match held n with
      | some v => some s!"({v})"
      | none => if unknown n then none else some (if line n && !deferred then "textwidth" else n)
  match raws.filter (!· matches .space) with
  | #[.ctrl n _] =>
    (held n).orElse fun _ => lengthSrcBy ref raws
  | _ => lengthSrcBy ref raws

/-- The names a native length spells, in order. -/
private def lengthNames (s : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  for c in s.toList ++ [' '] do
    if c.isAlphanum || c == '@' || c == '_' then cur := cur.push c
    else
      if !cur.isEmpty && (cur.front.isAlpha || cur.front == '@') then out := out.push cur
      cur := ""
  return out

/-- TeX's units and keywords, the only letters a length's spelling holds outside its control
words. -/
private def texLengthWords : List String :=
  ["filll", "fill", "fil", "true", "plus", "minus", "pt", "pc", "in", "bp", "cm", "mm", "dd", "cc",
   "nd", "nc", "sp", "em", "ex", "px", "mu"]

/-- Whether a run of letters splits into TeX's length keywords, each place the run reaches marked as
the keywords before it are read. -/
private def keywordRun (cs : List Char) : Bool := Id.run do
  let a := cs.toArray
  let mut reach := (Array.replicate (a.size + 1) false).modify 0 fun _ => true
  for i in [0:a.size] do
    if reach.getD i false then
      for w in texLengthWords do
        if (a.extract i (i + w.length)).toList == w.toList then
          reach := reach.modify (i + w.length) fun _ => true
  return reach.getD a.size false

/-- Whether a length's TeX spelling holds letters only in its control words and TeX's keywords. -/
private def texWordsOnly (s : String) : Bool := Id.run do
  let mut ctrl := false
  let mut run : Array Char := #[]
  let mut ok := true
  for c in s.toList ++ [' '] do
    if ctrl && (c.isAlpha || c == '@') then continue
    ctrl := false
    if c.isAlpha then run := run.push c.toLower
    else
      if !run.isEmpty && !keywordRun run.toList then ok := false
      run := #[]
      if c == '\\' then ctrl := true
  return ok

/-- Whether the declaration reader takes `s` as a length. -/
private def readsAsLength (s : String) : Bool :=
  match Decl.parseValue s ((lengthNames s).map fun n => (n, {})) with
  | some (.glue _) | some (.dim _) => true
  | _ => false

/-- The list parameters a level's style carries. -/
private def listCarried : List String := ["leftmargin", "topsep", "itemsep", "parsep"]

/-- What `\list` spends where a list opens. -/
public def listSpent : List String :=
  ["leftmargin", "rightmargin", "listparindent", "parsep", "topsep", "partopsep"]

/-- What a list's items read as they set. -/
public def listPerItem : List String := ["itemsep", "itemindent", "labelsep", "labelwidth", "parskip"]

/-- Whether a body assignment of `n` reaches the lists after it in LaTeX. -/
private def reachesLists (st : St) (n : String) : Bool :=
  listCarried.contains n && st.listiKept &&
    (st.listDefs.find? (·.1 == 1)).any fun (_, _, as) => !as.any (·.name == n)

/-- One length assignment, natively, at the site `paramSites` gives it. -/
private def setLength (n src what : String) (pos : Pos) : M (Array Raw) := do
  let st ← get
  -- premise: registerScopeChecks — a scoped assignment leaves later arithmetic unchanged
  unless st.inDef do
    write fun st => { st with lens := Ir.redeclare st.lens n src }
  let preamble ← docPreamble
  let own : Native.Setting := .tokens #[(n, src)]
  let emit (native : Native.Setting) : M (Array Raw) := setting what native pos
  let nothing (why : String) (tokens : Bool := true) : M (Array Raw) := do
    discard what why s!"setlength:{n}" pos
    if tokens then carry own pos else pure #[]
  let named (why : String) : M (Array Raw) := do
    nameParam n why pos
    return #[]
  -- premise: listBodyChecks — a list-body parameter ships the page without it
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
    if preamble && key == .textwidth then write fun st => { st with measureKnown := true }
    if st.inDoc && !st.inDef && key == .textwidth then
      return ← nothing "'\\begin{document}' set the lines' measure from it, and no later value \
moves a line" (tokens := false)
    -- premise: paramCensusChecks — a page setting in the body ships the page without it
    if st.inDoc && !st.inDef then
      return ← named "sets the page, which the body leaves as the preamble declared it"
    emit (.page #[(key, src)])
  | .token t, _ =>
    unless st.inDef do
      write fun st => { st with localLengths :=
        if st.localLengths.contains t then st.localLengths else st.localLengths.push t }
    -- premise: listLevelChecks — a body setting under a kept `\@listi` ships the page without it
    if !st.inDef && !preamble && !st.inList && reachesLists st n then
      named "opens the lists after it, whose level macro leaves it be; a list here opens \
with the space its level sets in the preamble, and only the trivlists after it read it"
    -- premise: paramCensusChecks — a page-level token in the body ships the page without it
    else if !st.inDef && !preamble && !st.inList && pageTokens.contains t then
      named "is read where the preamble sets it; the body leaves the page as declared"
    -- A preamble `\topsep` reaches only a trivlist outside every list.
    else if !st.inDef && preamble && n == Ir.trivlistSkipName then
      let native : Native.Setting := .tokens #[(t, src)]
      if let some note := native.note? then
        became what s!"{note}, which a trivlist outside a list reads; every list sets '\\topsep' \
again from its class's parameters" pos
      carry native pos
    else emit (.tokens #[(t, src)])
  | _, true => emit own
  | .listIndent _, false => emit own
  | .sizeReset body, false =>
    if preamble then
      nothing "'\\begin{document}' runs '\\normalsize', which sets it again"
        (tokens := !(body matches .token _))
    else match body with
      | .token t => emit (.tokens #[(t, src)])
      | .unmodelled why => named why
      | _ => emit own
  | .listReset, false =>
    if preamble then
      write fun st => { st with listResets := st.listResets.push (n, what, st.file, pos) }
      carry own pos
    else if reachesLists st n then
      -- premise: listLevelChecks — a body setting under a kept `\@listi` ships the page without it
      named "spaces the lists after it, whose level macro leaves it be; a list here is \
spaced per level, in the preamble"
    else
      nothing s!"the next list sets '\\{n}' again from its class's parameters, so no list reads it"
  | .unmodelled why, false =>
    if n == "parindent" && Decl.parseGlue src == some {} then
      nothing "paragraphs here are set flush, as declared"
    else named why

/-- The one warning for a length assignment the door cannot read, the length
keeping what it held. -/
private def unreadableLength (n shown : String) (pos : Pos) : M (Array Raw) := do
  sayOnce ("length:" ++ n) .W0107
    s!"'\\{n}' is set to '{shown}', a value this engine cannot read: skipped, and \
the length keeps its value" pos
    -- premise: unreadableLengthChecks — an unreadable spelling warns once
    (demote := packageFile (← get).file)
  return #[]

/-- A length value as the native declaration spells it, a LaTeX word included. -/
private def spelledValue? (value : Array Raw) : M (Option String) := do
  let st ← get
  return (lenValue st.lens value st.inDef (!st.inDoc && !st.seam) st.measureKnown
    st.flowPage (if st.inDoc then none else st.strutSkip)).filter readsAsLength

/-- A length value as the assignment door reads it; `none`
for one it cannot read. -/
private def doorValue? (value : Array Raw) : M (Option String) := do
  return (← spelledValue? value).filter fun _ => texWordsOnly (rawSrc value)

/-- The native declaration a length assignment translates to. -/
private def lengthNative (n src : String) : Native.Setting :=
  match paramSites.lookup n with
  | some (.page key) => .page #[(key, src)]
  | _ => .tokens #[(n, src)]

/-- A length assignment from its value's raws, landed by `setLength` or named and skipped; a
`\setlength` whose value is a word keeps the translation it spells. -/
private def assignLength (n : String) (value : Array Raw) (what : String) (pos : Pos)
    (noted : Bool := false) : M (Array Raw) := do
  if let some src ← doorValue? value then return ← setLength n src what pos
  if noted then
    if let some src ← spelledValue? value then became what (lengthNative n src).render pos
  unreadableLength n (rawSrc value).trimAscii.toString pos

/-- A document macro used in a list's body whose definition is only length
settings, as those settings. -/
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

/-- A length operand the rewrite evaluates: a literal, or a length whose value
it set, negated or not. -/
private def lenOperand (lens : Array (String × String)) : List Raw → Option String
  | [.word w _] => (Decl.parseLength w).map fun _ => w
  | [.sym '-' _, .word w _] => (Decl.parseLength ("-" ++ w)).map fun _ => "-" ++ w
  | [.ctrl y _] => (lens.find? (·.1 == y)).map fun (_, v) => s!"({v})"
  | [.sym '-' _, .ctrl y _] => (lens.find? (·.1 == y)).map fun (_, v) => s!"-({v})"
  | [.word "-" _, .ctrl y _] => (lens.find? (·.1 == y)).map fun (_, v) => s!"-({v})"
  | _ => none

private def isSign : Raw → Bool
  | .sym '-' _ | .sym '+' _ | .word "-" _ | .word "+" _ => true
  | _ => false

/-- Where one dimension ends: an optional sign, then a factor with its unit, a
factor of a register, or a register alone. -/
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

/-- The index past an optional glue keyword and the dimension after it. -/
private def afterKey (raws : Array Raw) (k : Nat) (key : String) : Nat :=
  let j := skipSpaces raws k
  match raws[j]? with
  | some (.ctrl c _) => if c == "@" ++ key then dimenEnd raws (j + 1) else k
  | some (.word w _) =>
    if w == key then dimenEnd raws (j + 1)
    else match keyRun? w key with
      | some rest =>
        if rest.toList.any Char.isAlpha then j + 1
        else
          let u := skipSpaces raws (j + 1)
          match raws[u]? with
          | some (.ctrl _ _) => u + 1
          | some (.word unit _) => if unit.toList.all Char.isAlpha then u + 1 else j + 1
          | _ => j + 1
      | none => k
  | _ => k



/-- Where a glue value ends: a register it copies, or a dimension with optional
`plus` and `minus` parts. -/
private def glueEnd (raws : Array Raw) (i : Nat) : Nat :=
  let i := skipSpaces raws i
  let rubber (k : Nat) : Nat := afterKey raws (afterKey raws k "plus") "minus"
  match raws[i]? with
  | some (.ctrl r _) => if valueCtrl r then rubber (i + 1) else i + 1
  | _ =>
    let d := dimenEnd raws i
    if d == i then i else rubber d

/-- The parameter assignments `raws` spells from `i`, in
order, and where they stop. -/
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

/-- The index past the spaces and the optional `=` before a
TeX assignment's value. -/
private def skipEq (raws : Array Raw) (i : Nat) : Nat :=
  let j := skipSpaces raws i
  match raws[j]? with
  | some (.sym '=' _) | some (.word "=" _) => skipSpaces raws (j + 1)
  | _ => j

/-- The display skips a redefined `\normalsize` assigns from `start`, each read
through the length door in order. -/
private def sizeSkips (body : Array Raw) (start : Nat) (pos : Pos) :
    M (Array (String × String)) := do
  let mut lens := (← get).lens
  let known := (← get).measureKnown
  let flow := (← get).flowPage
  let mut out : Array (String × String) := #[]
  for a in (readAssigns body start).1 do
    if !a.add && (paramSites.lookup a.name) matches some (.sizeReset (.token _)) then
      if let some src := (lenValue lens a.value (preamble := true) (measureKnown := known)
          (flowPage := flow)).filter readsAsLength then
        out := out.push (a.name, src)
        lens := Ir.redeclare lens a.name src
      else
        let _ ← unreadableLength a.name (rawSrc a.value).trimAscii.toString pos
        pure ()
  return out

/-- TeX's own assignment to a kernel parameter, when the
control word `name` opens one. -/
private def plainAssign? (name : String) (raws : Array Raw) (start : Nat) :
    Option (Array Raw × Nat) :=
  if (paramSites.lookup name).isNone then none
  else if readsOperand (rawBefore raws (start - 1)) then none
  else
    let j := skipSpaces raws start
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

/-- The list depth a class's parameter macro sets up,
`\@listi` to `\@listvi`. -/
private def listLevelOf : String → Option Nat
  | "@listi" => some 1
  | "@listii" => some 2
  | "@listiii" => some 3
  | "@listiv" => some 4
  | "@listv" => some 5
  | "@listvi" => some 6
  | _ => none

/-- Whether a body runs `\let\@listi\@listI`, a class `\normalsize`'s reset of
the outermost list level. -/
private def resetsListi (body : Array Raw) : Bool :=
  let xs := body.toList.filter (!· matches .space)
  (xs.zip xs.tail).any fun p => (p.1 matches .ctrl "let" _) && (p.2 matches .ctrl "@listi" _)

/-- A redefined list-level macro whose body is only parameter assignments,
recorded for the level; `false` for any other. -/
private def listLevelDef (level : Nat) (what : String) (body : Array Raw) (pos : Pos) :
    M Bool := do
  let (assigns, stop) := readAssigns body 0
  if stop < body.size || assigns.isEmpty then return false
  write fun st => { st with
    listDefs := Ir.redeclare st.listDefs level (pos, assigns) }
  for n in (assigns.map (·.name)).toList.eraseDups do
    if let some (.unmodelled why) := paramSites.lookup n then nameParam n why pos
    else if assigns.any (fun a => a.add && a.name == n) && listCarried.contains n then
      sayOnce "ctrl:advance" .W0104
        s!"TeX register arithmetic ('\\advance') is not supported; skipped" pos
  let spacing := ["topsep", "itemsep", "parsep"].filter fun n => assigns.any (·.name == n)
  if level > 4 && !spacing.isEmpty then
    let why := s!"spaces the lists {level} deep; past the fourth level a level macro's \
spacing is not read"
    for n in spacing do nameParam n why pos
    became what s!"the level-{level} list margin, set where a list that deep opens" pos
  else became what s!"the level-{level} list parameters, set where a list that deep opens" pos
  return true

/-- A list-level value as one native operand; `none` for anything else. -/
private def listOperand (run : List (String × Option String)) (lens : Array (String × String))
    (value : Array Raw) : Option String :=
  match value.toList.filter (!· matches .space) with
  | [.ctrl r _] =>
    if valueCtrl r then some (lengthSrc value)
    else match run.lookup r with
      | some o => o
      | none =>
        if lens.any (·.1 == r) || Ir.leftMarginNamed r then
          some r
        else none
  | vs =>
    if vs.all (fun x => match x with | .ctrl c _ => valueCtrl c | _ => true)
    then some (lengthSrc value) else none

/-- Each list level a redefined macro sets, as LaTeX's `\list` computes it where
a list of that depth opens. -/
private def flushListLevels : M (Array Raw) := do
  let st ← get
  -- premise: listLevelChecks — `\normalsize` resets `\@listi`, so the redefinition ships nothing
  let defOf (level : Nat) : Option (Pos × Array TexAssign) :=
    if level == 1 && !st.listiKept then none
    else (st.listDefs.find? (·.1 == level)).map fun (_, p, a) => (p, a)
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
  -- The class sets `\leftmargin` to `\leftmargini` as it loads, and its own level macros each to
  -- their depth's.
  let classMargin (level : Nat) (n : String) : Option String :=
    if n == "leftmargin" then some (Ir.leftMarginName level) else none
  let mut run : List (String × Option String) :=
    listCarried.map fun n => (n, (preamble n).orElse fun _ => classMargin 1 n)
  let mut out : Array Raw := #[]
  for level in [1:7] do
    match defOf level with
    | none => run := listCarried.map fun n => (n, classMargin level n)
    | some (pos, assigns) =>
      for a in assigns do
        if listCarried.contains a.name then
          let v := if a.add then none else listOperand run lens a.value
          run := run.map fun (n, o) => if n == a.name then (n, v) else (n, o)
      let op (n : String) : Option String := (run.lookup n).bind id
      let r := (["i", "ii", "iii", "iv"][level - 1]?).getD ""
      -- The margin is the depth's, which every kind of list and quotation that deep reads.
      if let some v := op "leftmargin" then
        unless v == Ir.leftMarginName level do
          out := out ++ (← carry (.tokens #[(Ir.leftMarginName level, v)]) pos)
      let mut keys : Array (String × String) := #[]
      if level ≤ 4 then
        if let some v := op "topsep" then keys := keys.push ("before", v)
        if let (some i, some p) := (op "itemsep", op "parsep") then
          out := out ++ (← carry (.tokens #[(s!"itemsep{r}", i), (s!"parsep{r}", p)]) pos)
          keys := keys.push ("gap", s!"itemsep{r} + parsep{r}")
      unless keys.isEmpty do
        for kind in ["itemize", "enumerate"] do
          out := out ++ (← carry (.style (if level == 1 then kind else s!"{kind}{level}") keys) pos)
  return out

/-- A TeX length from option text: `3\\gapunit` is
`3 * gapunit`, `\\x` is `x`. -/
private def lengthOfTeX (v : String) : String :=
  let t := v.trimAscii.toString
  match t.splitOn "\\" with
  | [plain] => plain.trimAscii.toString
  | num :: name :: _ =>
    let n := num.trimAscii.toString
    let name := name.trimAscii.toString
    if n.isEmpty then name else s!"{n} * {name}"
  | [] => t

/-- An xparse argument spec, or a plain count, as native
parameters `a1 … an`. -/
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

/-- The output drivers geometry and crop choose among, which
change nothing this engine sets. -/
public def driverOptions : List String :=
  ["dvips", "dvipdfm", "dvipdfmx", "dvisvgm", "pdftex", "luatex", "xetex", "vtex", "driver"]

/-- crop's options that turn its marks on or off. -/
public def cropModes : List (String × Bool) := [("cam", true), ("off", false)]

/-- crop's options the engine's marks already answer, each with why. -/
public def cropInert : List (String × String) :=
  [("noaxes", "the cut marks stand without axis marks, as drawn")] ++
    driverOptions.map (·, "the engine writes its own output")

/-- The geometry keys read as the `\page` key of the same name. -/
public def geometryPageKeys : List Native.PageKey :=
  [.margin, .vmargin, .hmargin, .width, .height, .textwidth, .textheight, .headsep, .footskip]

/-- The geometry keys read as one side's margin, which its opposite side's equal value completes. -/
public def geometrySideKeys : List String := ["top", "bottom", "left", "right"]

/-- geometry's flags asking for a page without running furniture, the page the engine starts from. -/
public def geometryNoFurniture : List String := ["noheadfoot", "nohead", "nofoot"]

/-- The native spacing entries one enumitem option entry sets: a vertical key with its length as
the length door reads it, or a shorthand's zeros; `none` for any other entry. -/
private def listSpacingEntries (what reader : String) (e : Entries.Entry) (pos : Pos) :
    M (Option (Array (String × String))) := do
  let zeros (keys : List String) : Array (String × String) := keys.toArray.map (·, "0pt")
  match e.key, e.value.map rawSrc with
  | "nosep", none | "nosep", some "true" => return some (zeros Ir.listSetKeys)
  | "noitemsep", none | "noitemsep", some "true" => return some (zeros ["itemsep", "parsep"])
  | "nolistsep", none | "nolistsep", some "true" =>
    return some ((zeros ["partopsep", "itemsep", "parsep"]).push ("topsep", "0pt plus 0.1pt"))
  | key, some v =>
    if !Ir.listSetKeys.contains key then return none
    let st ← get
    let read := (lenValue st.lens (e.value.getD #[]) (preamble := !st.inDoc)
      (measureKnown := st.measureKnown) (flowPage := st.flowPage)).filter fun n =>
        readsAsLength n && texWordsOnly v
    match read with
    | some n => return some #[(key, n)]
    | none =>
      unreadParam reader key s!"'{what}' key '{key}={v}', a length this engine cannot read," pos
        (help := "give a length such as 2pt, 0.5em or \\smallskipamount")
      return some #[]
  | _, _ => return none

/-- A list's options with enumitem's vertical keys and shorthands as native spacing keys, the rest
as written, for the list to read where it opens. -/
private def listOptions (n : String) (body : Array Raw) (pos : Pos) : M (Array Raw) := do
  let j := skipSpaces body 0
  unless body[j]? matches some (.sym '[' _) do return body
  let (opt, k) := takeRawOpt body j
  let some optRaws := opt | return body
  let what := s!"\\begin\{{n}}[{rawSrc optRaws}]"
  let mut rest : Array Entries.Entry := #[]
  let mut spacing : Array (String × String) := #[]
  let mut read := false
  let mut named := false
  for e in Entries.read .keyval optRaws do
    match ← listSpacingEntries what n e pos with
    | some vs =>
      read := true
      if vs.isEmpty then named := true
      for (key, v) in vs do spacing := Ir.redeclare spacing key v
    | none => rest := rest.push e
  unless read do return body
  let native := ", ".intercalate
    ((spacing.toList.map fun (key, v) => s!"{key} = {v}") ++ rest.toList.map (·.src))
  -- A value or key the list does not read is named where it stands, which accounts for the options.
  unless named || rest.any fun e => !e.key.isEmpty do
    became what s!"\\begin\{{n}}[{native}]" pos
  return #[.sym '[' pos] ++ (if native.isEmpty then #[] else #[.word native pos]) ++ #[.sym ']' pos] ++
    body.extract k body.size

/-- Each run of letters a native length spells, a unit after its number included. -/
private def letterRuns (s : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  for c in s.toList ++ [' '] do
    if c.isAlpha then cur := cur.push c
    else
      unless cur.isEmpty do out := out.push cur
      cur := ""
  return out

/-- The units a page length takes whatever its font or device, and the keywords around them. -/
private def absoluteWords : List String :=
  ["true", "plus", "minus", "pt", "pc", "in", "bp", "cm", "mm", "dd", "cc", "nd", "nc", "sp"]

/-- A key's value as the preamble's length door reads a `\dimexpr` to a literal, sums and scalings of
lengths it holds, else the value as written. -/
private def dimexprValue (v : Array Raw) : M String := do
  let src := rawSrc v
  if !src.startsWith "\\dimexpr" then return src
  let st ← get
  -- premise: strutLengthChecks — a value naming a length the page cannot resolve stays dropped
  let read := (lenValue st.lens v (preamble := !st.inDoc) (measureKnown := st.measureKnown)
    (flowPage := st.flowPage) (strut := if st.inDoc then none else st.strutSkip)).filter fun s =>
      readsAsLength s && texWordsOnly src && !s.contains '/' && (letterRuns s).all absoluteWords.contains
  return read.getD src

/-- `\usepackage[opts]{geometry}`, `\geometry{...}` and
`\newgeometry{...}` as `\page{...}`. -/
private def geometry (opts : Array Raw) (pos : Pos)
    (spelling : String := "\\usepackage{geometry}") : M (Array Raw) := do
  let mut keys : Array (Native.PageKey × String × Array String) := #[]
  let mut dropped : Array String := #[]
  let mut droppedExpr : Array String := #[]
  let mut sides : Array (String × String) := #[]
  for entry in Entries.read .keyval opts do
    let e := entry.src
    match entry.key, entry.value with
    | f, none =>
      if f.endsWith "paper" then
        keys := keys.push (.size, (f.dropEnd "paper".length).toString, #[e])
      else if geometryNoFurniture.contains f then
        -- geometry's flags zero the head's separation, the foot's skip, or both.
        if f != "nofoot" then keys := keys.push (.headsep, "0pt", #[e])
        if f != "nohead" then keys := keys.push (.footskip, "0pt", #[e])
      -- premise: driverOptionChecks — a driver option ships the page without it
      else if driverOptions.contains f then
        inertParam "geometry" f spelling "the engine writes its own output" pos
      else if f == "verbose" then inertParam "geometry" f spelling "the engine writes no TeX log" pos
      else dropped := dropped.push f
    | k, some v0 =>
      -- geometry's width/height size the text block, paperwidth/paperheight the page.
      let k := if k == "paperwidth" then "width" else if k == "paperheight" then "height" else k
      let v ← dimexprValue v0
      -- premise: driverOptionChecks — a driver option ships the page without it
      if driverOptions.contains k then
        inertParam "geometry" k spelling "the engine writes its own output" pos
      else if k == "verbose" then inertParam "geometry" k spelling "the engine writes no TeX log" pos
      else if v.startsWith "\\dimexpr" then
        droppedExpr := droppedExpr.push s!"{k} = {v}"
      else match k, ← (if v == rawSrc v0 then (Entries.read .keyval v0).toList.mapM (dimexprValue ·.item)
          else pure (KeyVal.items v).toList) with
      | "margin", a :: b :: _ | "hmargin", a :: b :: _ | "vmargin", a :: b :: _ =>
        if a.startsWith "\\dimexpr" || b.startsWith "\\dimexpr" then
          droppedExpr := droppedExpr.push s!"{k} = {v}"
        else if k == "margin" then
          keys := keys ++ #[(.hmargin, lengthOfTeX a, #[e]), (.vmargin, lengthOfTeX b, #[e])]
        else if lengthOfTeX a == lengthOfTeX b then
          keys := keys.push (if k == "hmargin" then .hmargin else .vmargin, lengthOfTeX a, #[e])
        else dropped := dropped.push k
      | _, _ :: _ :: _ => dropped := dropped.push k
      | _, _ =>
        if let some key := geometryPageKeys.find? (·.name == k) then
          keys := keys.push (key, lengthOfTeX v, #[e])
        else if k == "headheight" then
          inertParam "geometry" k spelling
            "the running head takes its content's height, and the text block stays where the margins put it" pos
        else if geometrySideKeys.contains k then
          sides := sides.push (k, lengthOfTeX v)
        else dropped := dropped.push k
  -- An equal pair of side margins is the symmetric margin; an unequal or lone side stays named.
  let side (n : String) : Option String :=
    (sides.findRev? (·.1 == n)).map (·.2)
  for (a, b, key) in [("top", "bottom", Native.PageKey.vmargin), ("left", "right", .hmargin)] do
    match side a, side b with
    | some va, some vb =>
      if va == vb then keys := keys.push (key, va, #[a, b])
      else dropped := dropped ++ #[a, b]
    | some _, none => dropped := dropped.push a
    | none, some _ => dropped := dropped.push b
    | none, none => pure ()
  -- geometry reads its keys in order, a later value of a key replacing the earlier one.
  let read := keys.foldl (init := #[]) fun acc kv => (acc.filter (·.1 != kv.1)).push kv
  -- A value standing as no single entry is its keys' loss, named with the others dropped.
  let (fit, unfit) := read.partition fun (k, v, _) => Native.Setting.carried (k.name, v)
  for (_, _, items) in unfit do
    for i in items do unless dropped.contains i do dropped := dropped.push i
  let native : Native.Setting := .page (fit.map fun (k, v, _) => (k, v))
  if fit.any fun (k, _, _) => k == .margin || k == .hmargin || k == .textwidth then
    write fun st => { st with measureKnown := true }
  if let some n := native.note? then became spelling n pos
  -- premise: nativeCarrierChecks — a load setting no key ships the class's page
  if read.isEmpty && dropped.isEmpty && droppedExpr.isEmpty then
    if spelling == "\\geometry" then discard spelling "it sets no key" "geometry" pos
    else
      unreadParam "usepackage:geometry" "layout" "geometry's default layout" pos
        (help := "declare the layout with geometry's keys, such as margin=1in")
  for k in dropped do
    unreadParam "usepackage:geometry" (KeyVal.entry k).1 s!"geometry key '{k}'" pos
  unless droppedExpr.isEmpty do
    say .W0101 s!"geometry values the engine cannot evaluate were dropped: \
{String.intercalate ", " droppedExpr.toList}" pos
      (help := "TeX register arithmetic has no value here; write the \
length as one literal")
  carry native pos

/-- `\usepackage[opts]{crop}` and `\crop[opts]` as `\page{ marks = cut }`. -/
private def crop (opts : String) (pos : Pos)
    (spelling : String := "\\usepackage{crop}") (key : String := "usepackage:crop") :
    M (Array Raw) := do
  let mut mode : Option Bool := none
  let mut dropped : Array String := #[]
  for e in KeyVal.items opts do
    let o := (KeyVal.entry e).1
    if let some on := cropModes.lookup o then mode := some on
    -- premise: driverOptionChecks — a driver option ships the page without it
    else if let some why := cropInert.lookup o then inertParam "crop" o spelling why pos
    else if !o.isEmpty then dropped := dropped.push o
  for o in dropped do
    unreadParam "usepackage:crop" (KeyVal.entry o).1 s!"crop option '{o}'" pos
  match mode with
  | some on =>
    setting spelling (.page #[(.marks, if on then "cut" else "none")]) pos
      (subject := some (paramSubject "crop" (if on then "cam" else "off")))
  | none =>
    discard spelling "crop draws no marks until an option asks for them" key pos
    return #[]

/-- The beamerposter size table from beamerposter.sty v1.13: board size in mm
and font scale per name. -/
private def beamerposterSizes : List (String × (Nat × Nat) × Nat) :=
  [("a0b", (1190, 880), 100000000),
   ("a0", (1189, 841), 100000000),
   ("a1", (841, 594), 70710678),
   ("a2", (594, 420), 50000000),
   ("a3", (420, 297), 35355339),
   ("a4", (297, 210), 25000000)]

/-- Fixed-point `v/10000` pt as a decimal `pt` value. -/
private def ptTenThousandths (v : Int) : String :=
  let whole := v / 10000
  let frac := (v % 10000).toNat
  if frac == 0 then s!"{whole}pt"
  else
    let digits := String.ofList (Nat.toDigits 10 frac)
    let padded := String.ofList (List.replicate (4 - digits.length) '0') ++ digits
    let fs := String.ofList (padded.toList.reverse.dropWhile (· == '0')).reverse
    s!"{whole}.{fs}pt"

/-- `\usepackage[size=…,orientation=…,scale=…]{beamerposter}` as the poster
class with its page size and font size. -/
private def beamerposter (opts : String) (pos : Pos) : M (Array Raw) := do
  let mut size := "a0"
  let mut portrait := false
  let mut scaleNum : Int := 1
  let mut scaleDen : Nat := 1
  let mut customW : Option String := none
  let mut customH : Option String := none
  let mut dropped : Array String := #[]
  for e in KeyVal.items opts do
    match KeyVal.entry e with
    | ("size", some v) => size := v
    | ("orientation", some v) => portrait := v == "portrait"
    -- A bare `orientation` takes the sty's declared default, portrait.
    | ("orientation", none) => portrait := true
    | ("scale", some v) =>
      match Decl.parseDecimal v with
      | some (m, s) => scaleNum := m; scaleDen := s
      | none => dropped := dropped.push e
    | ("scale", none) => pure ()
    | ("width", some v) => customW := some v
    | ("height", some v) => customH := some v
    | _ => dropped := dropped.push e
  let mut keys : Array (Native.PageKey × String) := #[]
  let mut fontscale : Nat := 100000000
  if size == "custom" then
    match customW, customH with
    | some w, some h =>
      let (w, h) := if portrait then (h, w) else (w, h)
      if (Decl.parseDecimal w).isSome && (Decl.parseDecimal h).isSome then
        keys := keys ++ #[(.width, s!"{w}cm"), (.height, s!"{h}cm")]
      else dropped := dropped.push "size=custom (needs width= and height= as numbers)"
    | _, _ =>
      dropped := dropped.push "size=custom (needs width= and height=)"
  else
    match beamerposterSizes.lookup size with
    | some ((w, h), fs) =>
      fontscale := fs
      let (w, h) := if portrait then (h, w) else (w, h)
      keys := keys ++ #[(.width, s!"{w}mm"), (.height, s!"{h}mm")]
    | none => dropped := dropped.push s!"size={size}"
  -- myfontscale is scale × fontscale rounded to two decimals; normalsize is 24.88 pt × myfontscale.
  let den : Int := (scaleDen : Int) * 100000000
  let cents := (scaleNum * (fontscale : Int) * 100 + den / 2) / den
  keys := keys.push (.fontsize, ptTenThousandths (2488 * cents))
  let page : Native.Setting := .page keys
  became "\\usepackage{beamerposter}" ("\\documentclass{poster}" ++ (page.note?.getD "")) pos
  for o in dropped do
    sayOnce ("param:usepackage:beamerposter:" ++ (KeyVal.entry o).1) .W0367
      s!"beamerposter option '{o}' is outside the poster model; ignored" pos
      (help := "size, orientation, scale, and custom width/height carry over; \
\\page{ ... } declares anything further")
  return (Native.Head.documentclass #[] "poster").raws pos ++ (← carry page pos)

/-- Whether a name spells a key of a native declaration. -/
private def nativeName (n : String) : Bool :=
  !n.isEmpty && n.all Decl.isIdentChar

mutual

/-- Whether raws hold a macro parameter token: `#` before a digit or another `#`. -/
private def holdsParam : List Raw → Bool
  | [] => false
  | .sym '#' _ :: .sym '#' _ :: _ => true
  | .sym '#' _ :: .word w _ :: rest => w.toList.head?.any Char.isDigit || holdsParam rest
  | r :: rest => holdsParamRaw r || holdsParam rest

private def holdsParamRaw : Raw → Bool
  | .group b _ | .env _ b _ | .math _ b _ => holdsParam b.toList
  | .word .. | .space | .par _ | .ctrl .. | .sym .. | .verb .. => false

end

/-- Whether, in a definition body, an argument or option holds a parameter, whose value only each
use gives. -/
private def paramArgs (args : Array (Array Raw)) (opts : Array (Option (Array Raw)) := #[]) :
    M Bool := do
  -- premise: templateArgChecks — a parameter's value is judged where each use gives it
  return (← get).inDef &&
    (args.any (holdsParam ·.toList) || opts.any (·.any (holdsParam ·.toList)))

/-- Accounts a setting whose value is a parameter: named in an environment's code, which the
elaborator expands without substituting it, and noted in a macro body, whose uses are rewritten
with their values. -/
private def unappliedParam (cmd stands : String) (pos : Pos) : M Unit := do
  if (← get).envCode then
    sayOnce ("envcode:" ++ cmd) .W0104
      s!"'\\{cmd}' in an environment's code takes its value from the environment's arguments, \
which this engine does not substitute there; skipped, and {stands}" pos
      (help := s!"write '\\{cmd}' with its value where the environment is used")
  else became s!"\\{cmd}" "a rewrite at each use, where its parameters hold their values" pos

/-- hyperref's keys whose values the engine reads as words, not TeX it sets: its dates and its
trapping state, each as its `\pdfmeta` key. -/
private inductive MetaWord where
  | created
  | modified
  | trapped
  | outline
  | outlineOpen
  | outlineNumbered
  | pageMode

/-- The hyperref key a word is read from. -/
private def MetaWord.hyperref : MetaWord → String
  | .created => "pdfcreationdate"
  | .modified => "pdfmoddate"
  | .trapped => "pdftrapped"
  | .outline => "bookmarks"
  | .outlineOpen => "bookmarksopen"
  | .outlineNumbered => "bookmarksnumbered"
  | .pageMode => "pdfpagemode"

private def MetaWord.name : MetaWord → String
  | .created => "created"
  | .modified => "modified"
  | .trapped => "trapped"
  | .outline => "outline"
  | .outlineOpen => "outline-open"
  | .outlineNumbered => "outline-numbered"
  | .pageMode => "pagemode"

private def MetaWord.all : List MetaWord :=
  [.created, .modified, .trapped, .outline, .outlineOpen, .outlineNumbered, .pageMode]

/-- Whether a word is a switch, which hyperref reads as `true` when written bare. -/
private def MetaWord.isSwitch : MetaWord → Bool
  | .outline | .outlineOpen | .outlineNumbered => true
  | .created | .modified | .trapped | .pageMode => false

/-- A word's value as its `\pdfmeta` key reads it: a date in either spelling, or a trapping state
in any case, as hyperref lowers it. -/
private def MetaWord.read (w : MetaWord) (v : String) : Option String :=
  let t := v.trimAscii.toString
  match w with
  | .created | .modified => if (PdfDate.parse? t).isSome then some t else none
  | .trapped => if ["true", "false", "unknown"].contains t.toLower then some t.toLower else none
  | .outline | .outlineOpen | .outlineNumbered =>
    if ["true", "false"].contains t.toLower then some t.toLower else none
  | .pageMode => if Ir.pageModes.contains t then some t else none

/-- How a word's value reads, for the help a misread one draws. -/
private def MetaWord.grammar : MetaWord → String
  | .created | .modified => "a date reads as D:20260131090000Z or 2026-01-31"
  | .trapped => "trapping reads as True or False"
  | .outline | .outlineOpen | .outlineNumbered => "a bookmark switch reads as true or false"
  | .pageMode => "a page mode reads as " ++ String.intercalate ", " Ir.pageModes

/-- What hyperref's keys declare: its metadata keys with their TeX values, its dates and trapping
as words, whether a link key was read, and whether a dropped key was named. -/
private structure HyperrefRead where
  metadata : Array (Native.TextMetaKey × Array Raw)
  words : Array (MetaWord × String)
  linked : Bool
  warned : Bool

/-- hyperref's settings, spelled `key` or `key=value`, whose meaning the engine's own output already
carries, each with why. -/
public def hyperrefInert : List (String × String) :=
  let either (k why : String) : List (String × String) := [(k, why), (k ++ "=true", why)]
  let any (k why : String) : List (String × String) :=
    [(k, why), (k ++ "=true", why), (k ++ "=false", why)]
  either "unicode" "the PDF's text strings are Unicode" ++
  either "final" "links are written, as without the option" ++
  either "breaklinks" "a link's text breaks across lines as other text does" ++
  either "pdfusetitle" "the title and author fall back to the document's own" ++
  either "pdfdisplaydoctitle" "the viewer shows the document's title" ++
  any "hypertexnames" "anchors are named by the engine" ++
  any "naturalnames" "anchors are named by the engine" ++
  any "plainpages" "anchors are named by the engine" ++
  either "pageanchor" "hyperref's default, as without the option" ++
  ["dvips", "dvipdfm", "dvipdfmx", "dvisvgm", "pdftex", "luatex", "xetex", "hypertex", "vtex"].map
    (·, "the engine writes its own output") ++
  [("verbose", "the engine writes no TeX log"), ("debug", "the engine writes no TeX log"),
   ("pdfborder=0 0 0", "links are written without a border"),
   ("pdfencoding=auto", "text strings are written in PDFDocEncoding where it holds them and in \
UTF-16 otherwise, as the option asks"),
   ("pdfencoding=unicode", "text strings read as the same Unicode text in either encoding"),
   ("hyperfootnotes=false", "a footnote mark carries no link here, as the option asks"),
   ("pdfpagelabels=false", "the PDF carries no page labels, as the option asks")]

/-- hyperref's keys, as `\hypersetup` and the package options give them, with its link keys
written into the setup. -/
private def hyperrefKeys (opts : Array Raw) (pos : Pos) : M HyperrefRead := do
  let mut metadata : Array (Native.TextMetaKey × Array Raw) := #[]
  let mut words : Array (MetaWord × String) := #[]
  let mut links := (← get).links
  let mut linked := false
  let mut cut : Array String := #[]
  let mut unread : Array String := #[]
  let mut misread : Array String := #[]
  let mut grammars : Array String := #[]
  for entry in Entries.read .keyval opts do
    let e := entry.src
    let k := entry.key
    let value := entry.value.map rawSrc
    let v := value.getD ""
    if let some m := Native.TextMetaKey.all.find? (k == "pdf" ++ ·.key.name) then
      metadata := metadata.push (m, Parse.trimSpace (Parse.asSpelled (entry.value.getD #[]).toList #[]))
    if let some w := MetaWord.all.find? (k == ·.hyperref) then
      let v := if v.trimAscii.isEmpty && w.isSwitch then "true" else v
      unless v.trimAscii.isEmpty do
        match w.read v with
        | some x => words := words.push (w, x)
        | none =>
          misread := misread.push s!"'{e}'"
          unless grammars.contains w.grammar do grammars := grammars.push w.grammar
    if ["linkcolor", "urlcolor", "citecolor", "allcolors"].contains k &&
        !(v.isEmpty || Decl.wholeValue v) then
      unread := unread.push s!"'{e}'"
    else if let some l := links.read k v then
      -- A colour style an earlier setup declared stands, so turning colouring off is not read.
      if (← get).links.colorlinks && !l.colorlinks then
        unreadParam "hyperref" k s!"hyperref key '{e}' after an earlier setup coloured links" pos
      links := l
      linked := true
    else if value.isNone && KeyVal.unbalanced e then cut := cut.push s!"'{e}'"
    else if (Native.TextMetaKey.all.find? (k == "pdf" ++ ·.key.name)).isNone &&
        (MetaWord.all.find? (k == ·.hyperref)).isNone then
      match hyperrefInert.lookup (optionSpelling e) with
      | some why => inertParam "hyperref" k e why pos
      | none => unreadParam "hyperref" k s!"hyperref key '{e}'" pos
  if linked then write fun st => { st with links }
  let dropped := cut ++ misread
  unless dropped.isEmpty do
    let hints := (if cut.isEmpty then [] else ["brace a value that holds a comma: key={...}"]) ++
      grammars.toList
    say .W0101 s!"hyperref entries without a native equivalent were dropped: \
{String.intercalate ", " dropped.toList}" pos (help := String.intercalate "; " hints)
  unless unread.isEmpty do
    say .W0102 s!"hyperref link colours no palette entry reads were dropped: \
{String.intercalate ", " unread.toList}" pos
      (help := "give a colour name, a mix such as blue!50!black, or #RRGGBB")
  return { metadata, words, linked, warned := !(dropped.isEmpty && unread.isEmpty) }

/-- A group holding `s` as one word, which the elaborator reads as written, never lexed as TeX. -/
private def wordGroup (s : String) (pos : Pos) : Raw :=
  .group (if s.isEmpty then #[] else #[.word s pos]) pos

/-- The mark opening a `\pdfmeta` group of TeX values: the construct, the link styles it lowers and
its dates and trapping as `\pdfmeta` entries, then each key's group and its value's group. -/
public def metaTextMark : String := "pdfmeta text"

/-- The marker standing where a read title-page template applies, its group the template's index
in the rewrite's typed templates. -/
public def titlePageMark : String := "title page template"

private theorem toList_sizeOf_lt (b : Array Raw) : sizeOf b.toList < sizeOf b := by
  cases b; simp

/-- A metadata value's TeX read as its text at every depth, onto `out`: `\texorpdfstring` as its
PDF argument, `\@title` and `\@author` as the declared title and author, a box as its content, `\and` as a separator between names, and `\label`, `\index`, `\footnote` and
`\thanks` as no text, a footnote being no part of the words it marks (`metaEscapeChecks`). -/
private def pdfStringList (out : Array Raw) : List Raw → Array Raw
  | [] => out
  | .ctrl "texorpdfstring" _ :: .group _ _ :: .group b _ :: rest
  | .ctrl "texorpdfstring" _ :: .group _ _ :: .space :: .group b _ :: rest =>
    pdfStringList (pdfStringList out b.toList) rest
  | .ctrl "label" _ :: .group _ _ :: rest | .ctrl "index" _ :: .group _ _ :: rest
  | .ctrl "footnote" _ :: .group _ _ :: rest | .ctrl "thanks" _ :: .group _ _ :: rest =>
    pdfStringList out rest
  | .ctrl "mbox" _ :: .group b _ :: rest | .ctrl "hbox" _ :: .group b _ :: rest
  | .ctrl "raisebox" _ :: .group _ _ :: .group b _ :: rest =>
    pdfStringList (pdfStringList out b.toList) rest
  | .ctrl "@title" p :: rest => pdfStringList (out.push (.ctrl "inserttitle" p)) rest
  | .ctrl "@author" p :: rest => pdfStringList (out.push (.ctrl "insertauthor" p)) rest
  | .ctrl "and" p :: rest =>
    let out := if out.back? matches some .space then out.pop else out
    pdfStringList (if out.isEmpty || rest.all (· matches .space) then out
      else (out.push (.word ";" p)).push .space) rest
  | .group b p :: rest => pdfStringList (out.push (.group (pdfStringList #[] b.toList) p)) rest
  | r :: rest => pdfStringList (out.push r) rest
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := toList_sizeOf_lt b; omega)

/-- hyperref's metadata, dates, trapping and link styles lowered, the metadata as TeX the
elaborator sets as text, the dates and trapping as quoted `\pdfmeta` entries it reads beside them,
and all named in its note. -/
private def hyperrefLowered (what key : String) (r : HyperrefRead) (pos : Pos) : M (Array Raw) := do
  let setup := (← get).links
  let settings := if r.linked then setup.native else #[]
  let links := String.join (settings.toList.filterMap (·.note?))
  let styles ← settings.foldlM (init := #[]) fun out s => return out ++ (← carry s pos)
  if r.metadata.isEmpty && r.words.isEmpty then
    if !links.isEmpty then became what links pos
    else unless r.warned do discard what "the engine does this itself" key pos
    return styles
  let entries := String.intercalate ", " (r.words.toList.map fun (w, v) => s!"{w.name} = {Decl.quote v}")
  let mut body : Array Raw :=
    #[.ctrl metaTextMark pos, .group #[.word what pos] pos, .group #[.word links pos] pos,
      wordGroup entries pos]
  for (k, v) in r.metadata do
    body := (body.push (.group #[.word k.key.name pos] pos)).push
      (.group (pdfStringList #[] (v.map (rebase (fun _ => pos) true)).toList) pos)
  return #[Raw.ctrl "pdfmeta" pos, .group body pos] ++ styles

/-- `\DocumentMetadata{...}`: `lang`, `pdfversion`, `pdfstandard=X-4` and the `X` entry of
`colorprofiles` land on the native `\pdfmeta` keys. -/
private def documentMetadata (opts : String) (pos : Pos) : M (Array Raw) := do
  let mut lang : Option String := none
  let mut version : Option String := none
  let mut standard : Option String := none
  let mut profile : Option String := none
  let mut dropped : Array String := #[]
  for e in KeyVal.items opts do
    match KeyVal.entry e with
    | ("lang", some v) => if v.isEmpty then dropped := dropped.push e else lang := some v
    | ("pdfversion", some v) =>
      if v == "1.6" || v == "1.7" || v == "2.0" then version := some v
      else dropped := dropped.push (if v.isEmpty then e else "pdfversion")
    | ("pdfstandard", some v) =>
      if v == "X-4" || v == "x-4" then standard := some "X-4"
      else dropped := dropped.push s!"pdfstandard={v}"
    | ("colorprofiles", some v) =>
      for p in KeyVal.items v do
        match KeyVal.entry p with
        | ("X", some f) | ("x", some f) | ("GTS_PDFX", some f) =>
          if f.isEmpty then dropped := dropped.push s!"colorprofiles {p}" else profile := some f
        | _ => dropped := dropped.push s!"colorprofiles {p}"
    | (key, some v) => dropped := dropped.push (if key.isEmpty || v.isEmpty then e else key)
    | (_, none) => dropped := dropped.push e
  unless dropped.isEmpty do
    say .W0101 s!"\\DocumentMetadata keys without a native equivalent were \
dropped: {String.intercalate ", " dropped.toList}" pos
      (help := "the engine writes PDF 2.0, or 1.6 or 1.7 when 'pdfversion' asks, and PDF/X-4 \
with an X output profile; other standards and compression keys have no effect here")
  write fun st => { st with intentProfile := profile }
  let keys : Array (Native.MetaKey × String) := (lang.map (.language, Decl.quote ·)).toArray ++
    (version.map (.version, Decl.quote ·)).toArray ++ (standard.map (.standard, Decl.quote ·)).toArray ++
    (profile.map (.intent, Decl.quote ·)).toArray
  if keys.isEmpty then return #[]
  setting "\\DocumentMetadata" (.pdfmeta keys) pos

/-- An expl3 key-value list as the expl3 catcodes read it: spaces dropped, `~` a space. -/
private def explKeyVals (src : String) : Array (String × String) :=
  let flat := String.ofList ((src.toList.filter (!·.isWhitespace)).map fun c =>
    if c == '~' then ' ' else c)
  (KeyVal.items flat).filterMap fun e => match KeyVal.entry e with
    | (key, some v) => some (key, v)
    | (_, none) => none

/-- The native output-intent key for one of pdfmeta's colour profile property keys. -/
private def explProfileKey : String → Option Native.MetaKey
  | "OutputConditionIdentifier" => some .intentCondition
  | "Info" => some .intentInfo
  | "RegistryName" => some .intentRegistry
  | _ => none

/-- The property name and its two groups after `\prop`, where the name spells
`_const_from_keyval:cn`. -/
private def propGroups (toks : Array Raw) (j : Nat) : Option (Array Raw × Array Raw × Nat) := Id.run do
  let mut name : String := ""
  for k in [j:toks.size] do
    match toks[k]?, toks[k + 1]? with
    | some (.group body _), some (.group kv _) =>
      return if name == "_const_from_keyval:cn" then some (body, kv, k + 2) else none
    | some (.group _ _), _ => return none
    | some r, _ => name := name ++ (rawSrc #[r]).trimAscii.toString
    | none, _ => return none
  return none

/-- One pdfmeta colour profile description as `\pdfmeta` keys, and its keys without a native one. -/
private def explProfileKeys (kv : String) : Array (Native.MetaKey × String) × Array String := Id.run do
  let mut keys : Array (Native.MetaKey × String) := #[]
  let mut dropped : Array String := #[]
  for (key, v) in explKeyVals kv do
    if let some n := explProfileKey key then
      keys := keys.push (n, Decl.quote v)
    else if key == "N" && (v == "1" || v == "3" || v == "4") then
      keys := keys.push (.intentComponents, v)
    else dropped := dropped.push key
  return (keys, dropped)

/-- pdfmeta's description of a profile it does not ship, `\prop_const_from_keyval:cn
{ c__pdfmeta_colorprofile_<file> } {…}`, read as the intent's `\pdfmeta` keys when `<file>` is the
declared X profile, and whether the block holds more. -/
private def explProfiles (block : Array Raw) (pos : Pos) : M (Array Raw × Bool) := do
  let toks := block.filter fun r => !(r matches .space) && !(r matches .par _)
  let mut out : Array Raw := #[]
  let mut rest := false
  let mut i := 0
  for _ in [0:toks.size + 1] do
    if i ≥ toks.size then break
    let read : Option (String × Array Raw × Nat) := match toks[i]? with
      | some (.ctrl "prop" _) => (propGroups toks (i + 1)).bind fun (nameBody, kv, k) =>
        let key := String.ofList ((rawSrc nameBody).toList.filter (!·.isWhitespace))
        (key.dropPrefix? "c__pdfmeta_colorprofile_").map fun file => (file.toString, kv, k)
      | _ => none
    match read with
    | none =>
      rest := true
      i := i + 1
    | some (file, kv, k) =>
      let label := s!"\\prop_const_from_keyval:cn\{c__pdfmeta_colorprofile_{file}}"
      -- premise: Tests.PrintX4.checks — a description of another profile names no field of the intent
      if (← get).intentProfile == some file then
        let (keys, dropped) := explProfileKeys (rawSrc kv)
        unless dropped.isEmpty do
          say .W0101 s!"the colour profile description's keys without a native equivalent \
were dropped: {String.intercalate ", " dropped.toList}" pos
        if keys.isEmpty then
          discard label "it describes no key the output intent reads" "explprofile" pos
        else out := out ++ (← setting label (.pdfmeta keys) pos)
      else
        discard label "it describes a profile no output intent of the document names" "explprofile" pos
      i := k
  return (out, rest)

/-- `\AddToHook{hook}[label]{code}`, skipped whole: the
engine has no hook machinery. -/
private def addToHook (pos : Pos) : M Unit :=
  sayOnce "ctrl:AddToHook" .W0104
    "'\\AddToHook' registers code on a kernel hook; the engine has no \
hook machinery; skipped" pos

/-- The page attribute code assigns with `\pdfvariable pageattr` or `\pdfpageattr`: its text when
literal, and whether it keeps the attribute in force, as `\expandafter{\the\pdfvariable pageattr …}`
does; `none` for any other code. -/
private def pageAttrText (look : String → Option (Array Raw)) (code : Array Raw) :
    Option (Option String × Bool) :=
  let literal (rs : List Raw) : Option String :=
    if rs.any (· matches .ctrl _ _ | .group _ _ | .env .. | .math .. | .verb ..) then none
    else some (rawSrc rs.toArray)
  -- After `\expandafter`, a leading `\the` of the attribute expands to the attribute in force.
  let expanded (rs : Array Raw) : Option String × Bool :=
    match rs.toList.dropWhile (· matches .space) with
    | .ctrl "the" _ :: .ctrl "pdfpageattr" _ :: rest => (literal rest, true)
    | .ctrl "the" _ :: .ctrl "pdfvariable" _ :: rest =>
      match rest.dropWhile (· matches .space) with
      | .word "pageattr" _ :: more => (literal more, true)
      | _ => (none, false)
    | rest => (literal rest, false)
  let arg : List Raw → Option String × Bool
    | [.group body _] => (literal body.toList, false)
    | [.ctrl "expandafter" _, .group body _] =>
      match (body.filter (!· matches .space)).toList with
      | [.ctrl m _] => ((look m).map fun t => (literal t.toList, false)).getD (none, false)
      | _ => expanded body
    | _ => (none, false)
  match (code.filter (!· matches .space)).toList with
  | .ctrl "pdfvariable" _ :: .word "pageattr" _ :: rest => some (arg rest)
  | .ctrl "pdfpageattr" _ :: rest => some (arg rest)
  | _ => none

/-- Where a page-attribute assignment starting at `raws[i]` ends: past its braces, after the
`pageattr` word for `\pdfvariable`. -/
private def pageAttrEnd (raws : Array Raw) (i : Nat) : Option Nat :=
  let j := match raws[i]? with
    | some (.ctrl "pdfvariable" _) => match raws[skipSpaces raws (i + 1)]? with
      | some (.word "pageattr" _) => some (skipSpaces raws (i + 1) + 1)
      | _ => none
    | some (.ctrl "pdfpageattr" _) => some (i + 1)
    | _ => none
  j.bind fun j =>
    let k := skipSpaces raws j
    match raws[k]? with
    | some (.group _ _) => some (k + 1)
    | some (.ctrl "expandafter" _) =>
      let g := skipSpaces raws (k + 1)
      if raws[g]? matches some (.group _ _) then some (g + 1) else none
    | _ => none

/-- The four corners of a page box a page attribute writes, as written, when it is an array of
four numbers. -/
private def boxCorners : PdfRead.Obj → Option (List String)
  | .arr xs =>
    let nums := xs.toList.filterMap fun o => match o with
      | .int n => some (toString n)
      | .real r => if (Decl.parseDecimal r).isSome then some r else none
      | _ => none
    if xs.size == 4 && nums.length == 4 then some nums else none
  | _ => none

/-- A page-attribute assignment read into the page's boxes, declared once at the preamble's end: its
four-number `/TrimBox`, `/BleedBox`, `/ArtBox` and `/CropBox` replace the boxes in force, or join
them when it keeps the attribute, and each entry it cannot write is named lost. -/
private def pageAttrBoxes (text : Option String) (keep : Bool) (what : String) (pos : Pos) :
    M Unit := do
  let lost (msg help subject : String) : M Unit :=
    say .W0443 msg pos (help := help) (subject := some subject) (output := some .pdf)
  let entries : Option (Array (String × PdfRead.Obj)) := text.bind fun t =>
    match (PdfRead.parseVal ("<< " ++ t ++ " >>").toUTF8 0).toOption with
    | some (.dict es, _) => some es
    | _ => none
  if entries.isNone then
    lost "the page attribute is not literal PDF entries; none of it is written, and it replaces \
the boxes before it" "write the entries themselves: '/TrimBox [9 9 261 153]'" "pageattr"
  let mut keys : Array (Native.PageKey × String) := #[]
  for (k, v) in entries.getD #[] do
    let native? : Option Native.PageKey := match k with
      | "TrimBox" => some .trimbox
      | "BleedBox" => some .bleedbox
      | "ArtBox" => some .artbox
      | "CropBox" => some .cropbox
      | _ => none
    match native?, boxCorners v with
    | some key, some cs => keys := keys.push (key, s!"\"{" ".intercalate cs}\"")
    | some _, none =>
      lost s!"the page attribute /{k} is not four numbers; the engine writes no {k}"
        "write the box as '[llx lly urx ury]' in PDF points" s!"pageattr:{k}"
    | none, _ =>
      lost s!"the page attribute /{k} is not a page box; the engine writes the page \
dictionary itself, without it"
        "a page attribute's '/TrimBox', '/BleedBox', '/ArtBox' and '/CropBox' are written; \
'\\page' declares the rest of the page" s!"pageattr:{k}"
  let old := (← get).pageBoxes
  let boxes := [Native.PageKey.trimbox, .bleedbox, .artbox, .cropbox].filterMap fun key =>
    match (keys.filter (·.1 == key)).back? with
    | some e => some e
    | none => if keep then old.find? (·.1 == key) else none
  let native : Native.Setting := .page boxes.toArray
  became what (native.note?.getD "no page box") pos
  let declared ← if boxes.isEmpty then pure #[] else carry native pos
  write fun st => { st with pageBoxes := boxes.toArray, pageAttr := declared }

/-- A shipout picture flattened to a token stream with its
group and environment brackets explicit. -/
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
/-- The flat stream of a raw list, each control word through `onCtrl`. -/
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

/-- A picture length as a native expression. -/
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

/-- A shipout picture's rules, read from its `\put` and `\rule` commands
relative to the page's top-left corner. -/
private def shipoutRules (look : String → Option (Array Raw)) (lengths : Array String)
    (code : Array Raw) : Option (Array (String × String × String × String × String)) := Id.run do
  let flat0 := picFlatList (fun n acc => acc.push (.ctrl n))
  let draws (body : Array Raw) : Bool :=
    (flat0 body.toList #[]).any fun t => t == .ctrl "put" || t == .ctrl "rule"
  let toks := picFlatList (fun n acc => match look n with
    | some body => if draws body then flat0 body.toList acc else acc.push (.ctrl n)
    | none => acc.push (.ctrl n)) code.toList #[]
  let mut stack : Array (String × String × String) := #[("0pt", "0pt", "black")]
  let mut mode : Nat := 0
  let mut buf : Array PicTok := #[]
  let mut first : Array PicTok := #[]
  let mut name := ""
  let mut rules : Array (String × String × String × String × String) := #[]
  for t in toks do
    let (ox, oy, ink) := stack.back?.getD ("0pt", "0pt", "black")
    if mode == 13 then
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
  if (mode == 0 || mode == 13) && stack.size == 1 then return some rules else return none

/-- `\pagecolor[model]{colour}`: the page background from here on. -/
private def pageColor (value : String) (pos : Pos) : M (Array Raw) := do
  became "\\pagecolor" s!"the {value} page-ground epoch" pos
  return #[.ctrl (Marker.name .pageColor value) pos]

private def modeledColorSource (model : Option String) (value : String) : String :=
  match model with
  | some m => s!"{m.trimAscii.toString}({value})"
  | none => value

/-- colorspace's `\definespotcolor{name}{colorant}[model]{values}`: the native `spot(...)` colour
with its CMYK alternate as xcolor stores it, converted from the model as `cmyk:<model>` does. -/
private def defineSpotColor (raws : Array Raw) (start : Nat) (pos : Pos) :
    M (Option (Array Raw × Nat)) := do
  let (names, j) := takeGroups raws start 2
  let (modelRaws, j) := takeRawOpt raws j
  let model := modelRaws.map rawSrc
  let (vals, k) := takeGroups raws j 1
  if ← paramArgs (names ++ vals) #[modelRaws] then
    unappliedParam "definespotcolor" "the colour is not defined" pos
    return some (#[], k)
  let (some n, some colorant, some v) := (names[0]?, names[1]?, vals[0]?)
    | say .W0102 "'\\definespotcolor' needs a colour name, a colorant and its values; nothing \
is defined" pos (help := "write \\definespotcolor{name}{colorant}{c,m,y,k}")
      return some (#[], k)
  let n := (rawSrc n).trimAscii.toString
  unless nativeName n do
    say .W0102 s!"'\\definespotcolor\{{n}}' names a colour no palette entry spells; the colour is \
not defined" pos (help := "name the colour with ASCII letters, digits, '.' or '_'")
    return some (#[], k)
  let flat := String.ofList ((rawSrc colorant).toList.map fun c => if c.isWhitespace then ' ' else c)
  let ink := " ".intercalate ((flat.splitOn " ").filter (!·.isEmpty))
  if ink.isEmpty || ink.contains '"' then
    say .W0102 s!"'\\definespotcolor\{{n}}' names a colorant the PDF cannot carry; the colour \
is not defined" pos (help := "name the colorant without double quotes, as \\definespotcolor{name}{Ink Name}{c,m,y,k}")
    return some (#[], k)
  let m := (model.map (·.trimAscii.toString)).getD "cmyk"
  let alternate := match Decl.parseColorSpec (some m) (rawSrc v) with
    | .ok spec => spec.cmykOf?
    | .error _ => none
  match alternate with
  | some (c, mg, y, kk) =>
    let modeled := s!"spot(\"{ink}\", cmyk({c.pdfUnit}, {mg.pdfUnit}, {y.pdfUnit}, {kk.pdfUnit}))"
    became s!"\\definespotcolor\{{n}}" (Native.Setting.palette #[(n, modeled)]).render pos
    return some (← carry (.palette #[(n, Decl.xcolorDefinitionPrefix ++ modeled)]) pos, k)
  | none =>
    say .W0102 s!"'\\definespotcolor\{{n}}' gives the alternate of '{ink}' in a model or values the \
engine does not convert to CMYK; the colour is not defined" pos
      (help := "give the alternate as '[cmyk]', '[rgb]', '[RGB]', '[HTML]' or '[gray]' values")
    return some (#[], k)

/-- colorspace's options: the overprint mode and a Lab alternate's illuminant, which the engine
has no state for. -/
private def colorspaceOptions (opts : String) (pos : Pos) : M Unit := do
  -- `opm=1` is the package's default, and an illuminant serves only the Lab alternate it refuses.
  let given := (KeyVal.items opts).filter fun o =>
    !o.isEmpty && o != "opm=1" && !o.startsWith "illuminant="
  if given.isEmpty then
    discard "\\usepackage{colorspace}" "the engine writes each ink's separation itself"
      "usepackage:colorspace" pos
  else
    for o in given do
      unreadParam "usepackage:colorspace" (KeyVal.entry o).1 s!"colorspace option '{o}'" pos
        (help := "the engine writes each ink's separation itself")

/-- The ink source `\normalcolor` names: the colour in force
when the body opened. -/
public def normalInkSource : String := "\\normalcolor"

/-- KOMA's `\sectionlinesformat` read as a coloured rule after a heading; any
other non-empty body is a named loss. -/
private def sectionRule (src : String) (pos : Pos) : M (Array Raw) := do
  let dropped (why : String) : M (Array Raw) := do
    if src.trimAscii.toString.isEmpty then
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
      let spec := (((afterRule.replace "\\p@" "pt").replace "\\z@" "0pt").splitOn "\\"
        |>.headD "").splitOn "}" |>.headD "" |>.trimAscii.toString
      let height? : Option String :=
        if spec.isEmpty then some "0.4pt"
        else if spec.startsWith "height" then
          let h := (spec.drop 6).trimAscii.toString
          if (h.splitOn " ").any (fun w => w == "depth" || w == "width") then none
          else some (if h.startsWith "." then "0" ++ h else h)
        else none
      match height? with
      | some h =>
        setting "\\sectionlinesformat"
          (.style "section" #[("rule", color), ("rule-position", "baseline"), ("rule-thickness", h)]) pos
      | none => dropped s!" (rule dimensions '{spec}' other than a height)"
    | none => dropped ""
  | none => dropped ""

/-- Whether environ's `\BODY` stands anywhere in the tree. -/
private def mentionsBody : List Raw → Bool
  | [] => false
  | .ctrl "BODY" _ :: _ => true
  | .group body _ :: rest => mentionsBody body.toList || mentionsBody rest
  | .env _ body _ :: rest => mentionsBody body.toList || mentionsBody rest
  | .math _ body _ :: rest => mentionsBody body.toList || mentionsBody rest
  | _ :: rest => mentionsBody rest
termination_by l => sizeOf l
decreasing_by raws_dec

/-- The code before and after environ's `\BODY` placed once at a definition's
top level; `none` otherwise. -/
public def bodySlot? (code : Array Raw) : Option (Array Raw × Array Raw) :=
  (code.findIdx? (· matches .ctrl "BODY" _)).bind fun i =>
    let before := code.extract 0 i
    let after := code.extract (i + 1) code.size
    if mentionsBody before.toList || mentionsBody after.toList then none
    else some (before, after)

/-- The words naming an environment definition the document body holds. -/
public def bodyEnvDefMessage : String :=
  "an environment definition in the document body is not applied"

public def bodyEnvDefHelp : String :=
  "define the environment in the preamble, before '\\begin{document}'"

/-- An environment definer in the document body, outside a macro's replacement text, named as
unapplied, the uses of an undefined name following `spec` for their arguments and dropping the body
when it `discards`; a preamble definition outside one records its name. -/
private def refusedEnvDef (name env spec : String) (discards : Bool) (pos : Pos) : M Bool := do
  let st ← get
  let env := env.trimAscii.toString
  if st.inDef then return false
  if !st.inDoc then
    write fun st => { st with definedEnvs := st.definedEnvs.push env }
    return false
  sayOnce ("ctrl:" ++ name ++ ":body") .W0104 bodyEnvDefMessage pos (help := bodyEnvDefHelp)
  unless name.startsWith "re" || name.startsWith "Re" || st.definedEnvs.contains env ||
      st.provideKeeps.contains (Tcolorbox.bindingName env) do
    write fun st => { st with refusedEnvs := Ir.redeclare st.refusedEnvs env (spec, discards) }
  return true

/-- The arguments a use of a native environment reads, from its definition's text past the name:
an optional one for a parameter marked `?`. -/
private def nativeEnvSpec (sig : String) : String :=
  let sig := sig.trimAscii.toString
  if !sig.startsWith "(" then "" else
  let inner := String.ofList ((sig.toList.drop 1).takeWhile (· != ')'))
  String.ofList ((inner.splitOn ",").filterMap fun part =>
    let nm := ((part.splitOn ":").getD 0 "").trimAscii.toString
    if nm.isEmpty then none else some (if nm.endsWith "?" then 'o' else 'm'))

/-- The arguments `spec` reads at a use's start, their contents each followed by a space, and the
index past them. -/
private def plainArgs (spec : String) (body : Array Raw) : Array Raw × Nat :=
  spec.toList.foldl (fun (out, k) c =>
    if c == 'o' then
      match takeRawOpt body k with
      | (some a, k') => ((out ++ a).push .space, k')
      | (none, _) => (out, k)
    else
      let j := skipSpaces body k
      match body[j]? with
      | some (.group g _) => ((out ++ g).push .space, j + 1)
      | _ => (out, k)) (#[], 0)

/-- The index past a native `\defineenv`'s operands from `i`: its name, its signature and
`[default]`, and its two codes, or environ's one code and optional final code. -/
public def defineEnvEnd (raws : Array Raw) (i : Nat) : Nat := Id.run do
  let j := skipSpaces raws i
  unless raws[j]? matches some (.group _ _) do return i
  let mut k := j + 1
  let mut environ := false
  for _ in [k:raws.size] do
    match raws[k]? with
    | some (.group _ _) => break
    | some (.sym '[' _) =>
      match takeRawOpt raws k with
      | (some _, k') => k := k'
      | (none, _) => return raws.size
    | some r =>
      match r with
      | .ctrl n _ => if n == Marker.name .environBody "" then environ := true
      | _ => pure ()
      k := k + 1
    | none => break
  unless raws[k]? matches some (.group _ _) do return k
  let f := skipSpaces raws (k + 1)
  if environ then return (takeRawOpt raws (k + 1)).2.max (k + 1)
  if raws[f]? matches some (.group _ _) then return f + 1
  return k + 1

/-- The index past a `\newtheorem`'s operands from `i`, or a `\theoremstyle`'s group. -/
public def theoremDeclEnd (raws : Array Raw) (name : String) (i : Nat) : Nat :=
  if name == "theoremstyle" then (takeGroups raws i 1).2 else
    let i0 := skipStar raws i
    let (_, j) := takeGroups raws i0 1
    let (shared, j) := takeOpt raws j
    let (_, j) := takeGroups raws j 1
    -- A numbered definition without a shared counter tests for a numbering-within argument,
    -- reading past spaces.
    if i0 != i || shared.isSome then j else match takeOpt raws j with
      | (some _, k) => k
      | (none, _) => skipSpaces raws j

/-- A caption skip's value inside the float-core idiom, read
in the code's order. -/
private def floatSkipValue? (assigned : Array (String × String)) (v : Array Raw) :
    M (Option String) := do
  if let #[.ctrl n _] := v.filter (!· matches .space) then
    if let some (_, src) := assigned.find? (·.1 == n) then return some src
  if v.any (· matches .ctrl "belowcaptionskip" _) then return none
  doorValue? v

/-- A float redefined around its own kernel core, as a scoped caption-skip
declaration for its kind. -/
private def floatRedef? (envName : String) (raws : Array Raw) (j : Nat) (pos : Pos) :
    M (Option (Array Raw × Nat)) := do
  let some kind := Ir.FloatKind.ofCaptionType? envName | return none
  unless floatRedefEnvs.contains envName do return none
  let items (xs : Array Raw) : List Raw := xs.toList.filter fun r =>
    match r with | .space | .par _ => false | _ => true
  let b := skipSpaces raws j
  let some (.group beginB _) := raws[b]? | return none
  let e := skipSpaces raws (b + 1)
  let some (.group endB _) := raws[e]? | return none
  match items endB, floatCoreDecls envName (items beginB) with
  | [.ctrl "end@float" _], some decls =>
    let mut assigned : Array (String × String) := #[]
    for (r, v) in decls do
      match ← floatSkipValue? assigned v with
      | some src => assigned := Ir.redeclare assigned r src
      | none => let _ ← unreadableLength r (rawSrc v).trimAscii.toString pos
    let tokens : Native.Setting := .tokens (assigned.map fun (r, src) =>
      (kind.captionScope ++ (if r == "abovecaptionskip" then "captionsep" else "belowcaptionskip"), src))
    -- premise: captionScopeChecks — the kernel's order applies without a caption package
    let packaged := (← get).loads.pkgs.any fun (p, _) => p == "caption" || p == "subcaption"
    let caption := Native.Head.captionsetup (some envName) "position=bottom"
    let (out, natives) ← if assigned.isEmpty then pure (#[], []) else do
      let out ← carry tokens pos
      if packaged then pure (out, tokens.note?.toList)
      else pure (out ++ caption.raws pos, tokens.note?.toList ++ [caption.render])
    let what := if natives.isEmpty then s!"the built-in \{{envName}}"
      else String.intercalate " " natives
    became s!"\\renewenvironment\{{envName}}" what pos
    return some (out, e + 1)
  | _, _ => return none

/-- LaTeX's documented sectioning idiom: a definer whose whole body is one
`\@startsection` call. -/
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
        -- A negative afterskip declares a run-in heading.
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
        | .ctrl n _ => if alignments.contains n then none else some (Raw.ctrl ((aliases.lookup n).getD n) pos)
        | _ => none
      let font := if fonts.isEmpty then #[] else #[("font", Native.StyleValue.tex fonts)]
      return some (← texSetting s!"\\{cmd} = \\@startsection\{{element}}" element
        (#[("before", .text before), ("after", .text after)] ++ font) pos)
    else return none
  | _ => return none

/-- The mark before `\vspace*`'s space, which keeps the
space at a page's top. -/
public def vspaceAnchorMark : String := "vspace anchor"

/-- A document skip's value as the native `before` spells it, and whether it
carried an infinite stretch. -/
private structure SkipSpelling where
  width : String
  fill : Bool := false
  unranked : Bool := false

private def skipSrc (src : String) : SkipSpelling :=
  match src.splitOn " plus " with
  | [w, st] =>
    let (st, shrink) := match st.splitOn " minus " with
      | [a, b] => (a, " minus " ++ b)
      | _ => (st, "")
    match Decl.filFactor? (st.replace " " "") with
    | some ((m, sc), order) =>
      let width := w.trimAscii.toString ++ shrink
      if order == 2 && m == (sc : Int) then
        if (Decl.parseLength w).any (· == ({} : Dim.Length)) && shrink.isEmpty then { width := "fill" }
        else { width, fill := true }
      else { width, unranked := true }
    | none => { width := src }
  | _ => { width := src }

/-- A skip as the native block it is: its width and its infinite stretch, or its width alone where
no entry carries it, so the skip is dropped whole. -/
private def skipNative (sp : SkipSpelling) (kind : String := "") : Native.Setting :=
  if !Native.Setting.carried ("before", sp.width) then .block #[("before", sp.width)] else
  .block (#[("before", sp.width)] ++ (if kind.isEmpty then #[] else #[("kind", kind)]) ++
    (if sp.unranked then #[("stretch", "unranked")] else if sp.fill then #[("stretch", "fill")] else #[]))

/-- One argument a control's signature reads: a star right after it, an optional `[...]`, a group
or bare control word where one stands, one that must stand or the control is left to elaboration,
and a brace group that must stand next and stays in the walk. -/
public inductive ArgKind where
  | star
  | opt
  | group
  | needed
  | kept
  deriving BEq, Repr

/-- A signature's arguments read from `i` after `acc`, each as written or none where it does not
stand, with the index past them; none where one that must stand does not. -/
public def argsRead (raws : Array Raw) (acc : Array (Option (Array Raw))) :
    List ArgKind → Nat → Option (Array (Option (Array Raw)) × Nat)
  | [], i => some (acc, i)
  | .star :: sig, i =>
    if raws[i]? matches some (.word "*" _) then argsRead raws (acc.push (some #[])) sig (i + 1)
    else argsRead raws (acc.push none) sig i
  | .opt :: sig, i => argsRead raws (acc.push (takeRawOpt raws i).1) sig (takeRawOpt raws i).2
  | .group :: sig, i =>
    argsRead raws (acc.push (takeGroups raws i 1).1[0]?) sig (takeGroups raws i 1).2
  | .needed :: sig, i => (takeGroups raws i 1).1[0]?.bind fun g =>
    argsRead raws (acc.push (some g)) sig (takeGroups raws i 1).2
  | .kept :: sig, i =>
    match raws[skipSpaces raws i]? with
    | some (.group body _) => argsRead raws (acc.push (some body)) sig (skipSpaces raws i)
    | _ => none

/-- Where a lowered control is left, as written, to elaboration: in a definition body, whose uses
read it; in the document body; in a hook's seam; outside the whole document's preamble proper;
without a package loaded; or where argument `i` is not one control word. -/
public inductive CtrlLeave where
  | inDef
  | inBody
  | inSeam
  | outsidePreamble
  | without (pkg : String)
  | notCtrl (i : Nat)
  deriving BEq, Repr

/-- A lowered control's gates: where it is left to elaboration, what stands while an argument holds
a macro parameter only a use settles, and the help where the body ignores it as a declaration. -/
public structure CtrlGates where
  leaves : List CtrlLeave := []
  paramStands : Option String := none
  bodyHelp : Option String := none
  deriving Repr

/-- Where a row's refusal says itself: once per control under `ctrl:` or `beamer:`, or at each
use. -/
public inductive RefusalKey where
  | ctrl
  | beamer
  | each
  deriving BEq, Repr

/-- The code a lowered control's arguments run through, one per family of controls. -/
public inductive Lowering where
  | packages | passOptions | defineColor | colorLet | pageColor | geometry | crop | microtypeSetup
  | documentMetadata | defineColorspace | addToHook | counter | newLength | newDimen
  | mathOperator | hyperSetup | runningField | fancyField | clearPageStyles | pageStyle
  | thisPageStyle | addBibResource | bibResources | natbibStyle | bibliographyStyle
  | printBibliography | crefRange | fontSeries | lineNumbers | selectLanguage | vspace | pageBreak
  | komaFont | sectionSkips | setList | sectionLines | uniMathSetup | unreadKeys | newCounter
  | ensureMath | box | beamerFont | columnRatio | useTheme | molochSet | titleGraphic | fontTheme
  | beamerOption | beamerCovered | inputEncoding | komaOptions | graphColor | blueprintSite
  deriving BEq, Repr

/-- What a table row's control does where it stands. -/
public inductive CtrlAction where
  /-- Fixed tokens, named in a translation note where one spells their native form. -/
  | tokens (toks : List Raw) (note : Option String)
  /-- A native setting, named in its translation note. -/
  | native (s : Native.Setting)
  /-- The kernel skip `amount`: its declared value, else its default. -/
  | skip (amount : String)
  /-- Refused with `code`. -/
  | refuse (code : DiagCode) (key : RefusalKey) (msg : String) (help : Option String)
  /-- Read to nothing, its note keyed `ctrl:nothing:<key>`. -/
  | discard (why key : String)
  /-- Read to nothing with no report of its own, so the dispatcher's guard names it. -/
  | inert
  /-- Its arguments run through a lowering, behind its gates. -/
  | lower (l : Lowering) (gates : CtrlGates)

/-- A control the dispatcher answers from data: the arguments it consumes and what it does. -/
public structure CtrlRow where
  name : String
  sig : List ArgKind
  action : CtrlAction

/-- A registered control where it stands: its arguments as its signature reads them, and the walk's
raws with the span they occupy. -/
public structure CtrlCall where
  name : String
  pos : Pos
  args : Array (Option (Array Raw))
  raws : Array Raw
  start : Nat
  stop : Nat

/-- Argument `i` as written, if it stands. -/
public def CtrlCall.given (c : CtrlCall) (i : Nat) : Option (Array Raw) := c.args[i]?.join

/-- Argument `i`'s raws, empty where it does not stand. -/
public def CtrlCall.arg (c : CtrlCall) (i : Nat) : Array Raw := (c.given i).getD #[]

/-- Argument `i` as source text. -/
public def CtrlCall.src (c : CtrlCall) (i : Nat) : String := rawSrc (c.arg i)

/-- Optional argument `i` as source text, if it stands. -/
public def CtrlCall.optSrc (c : CtrlCall) (i : Nat) : Option String := (c.given i).map rawSrc

/-- A control read to nothing, its arguments `n` groups, named by why. -/
private def nothingRow (name : String) (n : Nat) (why : String) : CtrlRow :=
  ⟨name, List.replicate n .group, .discard why name⟩

private def packageLog : String := "package diagnostics address TeX's log, not the document"
private def classLog : String := "class diagnostics address TeX's log, not the document"
private def kernelLog : String := "kernel diagnostics address TeX's log, not the document"
private def pageInks : String := "every page lists each ink it paints"
private def packageHelp : String := "load the package in the preamble, before '\\begin{document}'"

/-- A declaration's gates: the body ignores it, named with the help to declare it in the
preamble. -/
private def declared : CtrlGates := { bodyHelp := some Diag.declareInPreamble }

/-- A package load: in a definition body left to its uses, in the body ignored as a declaration. -/
public def packageRow (name : String) : CtrlRow :=
  ⟨name, [.opt, .needed], .lower .packages { leaves := [.inDef], bodyHelp := some packageHelp }⟩

/-- A control refused once by name. -/
private def refusedRow (name : String) (sig : List ArgKind) (msg help : String) : CtrlRow :=
  ⟨name, sig, .refuse .W0104 .ctrl msg (some help)⟩

/-- A beamer configuration command the engine does not have, with its `{...}` groups. -/
private def beamerConfigRow (name : String) (n : Nat) : CtrlRow :=
  ⟨name, .opt :: List.replicate n .group, .refuse .W0104 .beamer
    s!"'\\{name}' is beamer configuration the engine does not have; skipped"
    (some ((beamerNative.lookup name).getD "a theme is a token bundle here: \\theme selects one, \
and \\palette and \\tokens declare the design directly"))⟩

/-- A hook reached past its moment: every hook was collected before this pass, so its group is read
where it stands. -/
private def hookRow (name : String) : CtrlRow :=
  ⟨name, [], .refuse .W0340 .ctrl
    s!"'\\{name}' cannot defer from here; its group is read where it stands"
    (some "declare the hook before '\\begin{document}'")⟩

private def ctrlRows0 : List CtrlRow :=
  [⟨"@latex@error", List.replicate 2 .group, .inert⟩,
   nothingRow "@latex@info" 1 kernelLog,
   nothingRow "@latex@info@no@line" 1 kernelLog,
   nothingRow "@latex@note" 1 kernelLog,
   nothingRow "@latex@note@no@line" 1 kernelLog,
   nothingRow "@latex@warning" 1 kernelLog,
   nothingRow "@latex@warning@no@line" 1 kernelLog,
   ⟨"AddToHook", [.group, .opt, .group], .lower .addToHook {}⟩] ++
  deferredHooks.map (hookRow ·.1) ++
  [⟨"ClassError", List.replicate 3 .group, .inert⟩,
   nothingRow "ClassInfo" 2 classLog,
   nothingRow "ClassNote" 2 classLog,
   nothingRow "ClassNoteNoLine" 2 classLog,
   nothingRow "ClassWarning" 2 classLog,
   nothingRow "ClassWarningNoLine" 2 classLog,
   ⟨"Crefrange", [.star, .needed, .needed], .lower .crefRange {}⟩]

private def ctrlRows1 : List CtrlRow :=
  [⟨"DeclareMathOperator", [.star, .needed, .needed],
     .lower .mathOperator { leaves := [.notCtrl 1] }⟩,
   ⟨"DocumentMetadata", [.needed], .lower .documentMetadata {}⟩,
   ⟨"GenericError", List.replicate 4 .group, .inert⟩,
   nothingRow "GenericInfo" 2 packageLog,
   nothingRow "GenericWarning" 2 packageLog,
   ⟨"IfValueT", [], .tokens [.ctrl "ifgiven" {}] none⟩,
   ⟨"IfValueTF", [], .tokens [.ctrl "ifgiven" {}] none⟩,
   ⟨"KOMAoptions", [.group], .lower .komaOptions {}⟩,
   nothingRow "MessageBreak" 0 "a line break in a log message, not in the document",
   ⟨"PackageError", List.replicate 3 .group, .inert⟩,
   nothingRow "PackageInfo" 2 packageLog,
   nothingRow "PackageNote" 2 packageLog,
   nothingRow "PackageNoteNoLine" 2 packageLog,
   nothingRow "PackageWarning" 2 packageLog,
   nothingRow "PackageWarningNoLine" 2 packageLog,
   ⟨"PassOptionsToClass", [.needed, .needed], .lower .passOptions { leaves := [.inDef] }⟩]

private def ctrlRows2 : List CtrlRow :=
  [⟨"PassOptionsToPackage", [.needed, .needed], .lower .passOptions { leaves := [.inDef] }⟩,
   ⟨"RedeclareSectionCommand", [.opt, .group], .lower .sectionSkips {}⟩,
   packageRow "RequirePackage",
   ⟨"addbibresource", [.opt, .needed], .lower .addBibResource {}⟩,
   ⟨"addtocounter", [.needed, .needed], .lower .counter { leaves := [.outsidePreamble] }⟩,
   beamerConfigRow "beamertemplatenavigationsymbolsempty" 0,
   ⟨"bibliography", [.needed], .lower .bibResources { leaves := [.inBody, .without "biblatex"] }⟩,
   ⟨"bibliographystyle", [.needed], .lower .bibliographyStyle { leaves := [.inBody, .inSeam] }⟩,
   ⟨"bibpunct", [.opt, .needed, .needed, .needed, .needed, .needed, .needed],
     .lower .natbibStyle declared⟩,
   ⟨"bigskip", [], .skip "bigskipamount"⟩,
   ⟨"cfoot", [.group], .lower .runningField {}⟩,
   ⟨"chead", [.group], .lower .runningField {}⟩,
   ⟨"citestyle", [.needed], .lower .natbibStyle declared⟩,
   -- With no floats to flush, `\clearpage` and `\newpage` are the declared page break.
   ⟨"clearpage", [], .tokens [.ctrl "pagebreak" {}] (some "\\pagebreak")⟩,
   ⟨"clearpairofpagestyles", [], .lower .clearPageStyles {}⟩,
   ⟨"colorlet", [.needed, .needed],
     .lower .colorLet { paramStands := some "the colour is not defined" }⟩]

private def ctrlRows3 : List CtrlRow :=
  [refusedRow "column" [.group] "'\\column' is not at the top level of a {columns} body; \
it starts no column there and is skipped" "\\column{width} splits the body of \\begin{columns} \
... \\end{columns}",
   ⟨"columnratio", [.needed, .opt], .lower .columnRatio {}⟩,
   ⟨"crefrange", [.star, .needed, .needed], .lower .crefRange {}⟩,
   ⟨"crop", [.opt], .lower .crop {}⟩,
   ⟨"definecolor", [.needed, .needed, .needed],
     .lower .defineColor { paramStands := some "the colour is not defined" }⟩,
   ⟨"definecolorspace", [.star, .needed, .needed, .needed], .lower .defineColorspace {}⟩,
   -- Running Lua is refused by design.
   refusedRow "directlua" [.group] "'\\directlua' is Lua code for luatex; the engine \
does not run Lua, so it is skipped" "\\allow{W0104} accepts the skip",
   ⟨"dochome", [.needed],
     .lower .blueprintSite { declared with leaves := [.without "blueprint"] }⟩,
   ⟨"doublespacing", [], .native (.page #[(.leading, "1.667")])⟩,
   nothingRow "endlinenomath" 0 "display math lines are numbered like every galley line",
   ⟨"ensuremath", [.needed], .lower .ensureMath {}⟩,
   ⟨"fancyfoot", [.opt, .group], .lower .fancyField {}⟩,
   ⟨"fancyhead", [.opt, .group], .lower .fancyField {}⟩,
   ⟨"fancyhf", [.opt, .group], .lower .fancyField {}⟩,
   -- The page's bottom (latex.ltx `\flushbottom`, `\raggedbottom`).
   ⟨"flushbottom", [], .native (.page #[(.bottom, "flush")])⟩,
   ⟨"fontseries", [.needed],
     .lower .fontSeries { paramStands := some "the weight in force stands" }⟩]

private def ctrlRows4 : List CtrlRow :=
  [⟨"footercontent", [], .tokens [.ctrl "runningfoot" {}] (some "\\runningfoot{...}")⟩,
   nothingRow "frenchspacing" 0 "inter-sentence space is uniform here either way",
   ⟨"geometry", [.needed], .lower .geometry {}⟩,
   ⟨"github", [.needed],
     .lower .blueprintSite { declared with leaves := [.without "blueprint"] }⟩,
   ⟨"graphcolor", [.needed, .needed, .needed],
     .lower .graphColor { leaves := [.without "blueprint"] }⟩,
   ⟨"home", [.needed],
     .lower .blueprintSite { declared with leaves := [.without "blueprint"] }⟩,
   ⟨"hypersetup", [.group], .lower .hyperSetup
     { declared with paramStands := some "hyperref's settings stand" }⟩,
   ⟨"ifoot", [.group], .lower .runningField {}⟩,
   ⟨"ihead", [.group], .lower .runningField {}⟩,
   ⟨"inputencoding", [.group], .lower .inputEncoding {}⟩,
   ⟨"lfoot", [.group], .lower .runningField {}⟩,
   ⟨"lhead", [.group], .lower .runningField {}⟩,
   nothingRow "linenomath" 0 "display math lines are numbered like every galley line",
   ⟨"linenumbers", [.star, .opt], .lower .lineNumbers {}⟩,
   nothingRow "makeatletter" 0 "@-names are always readable here",
   nothingRow "makeatother" 0 "@-names are always readable here"]

private def ctrlRows5 : List CtrlRow :=
  [⟨"makebox", [.opt, .opt], .lower .box {}⟩,
   ⟨"mbox", [], .lower .box {}⟩,
   ⟨"medskip", [], .skip "medskipamount"⟩,
   beamerConfigRow "metroset" 1,
   ⟨"microtypesetup", [.needed], .lower .microtypeSetup {}⟩,
   ⟨"modulolinenumbers", [.star, .opt], .lower .lineNumbers {}⟩,
   ⟨"molochset", [.needed], .lower .molochSet {}⟩,
   ⟨"newcounter", [.needed, .opt],
     .lower .newCounter { paramStands := some "no counter is allocated" }⟩,
   ⟨"newdimen", [.group], .lower .newDimen { leaves := [.notCtrl 0] }⟩,
   ⟨"newgeometry", [.needed], .lower .geometry {}⟩,
   ⟨"newlength", [.group], .lower .newLength { leaves := [.notCtrl 0] }⟩,
   ⟨"newpage", [], .tokens [.ctrl "pagebreak" {}] (some "\\pagebreak")⟩,
   nothingRow "noindent" 0 "no paragraph carries a first-line indent here",
   ⟨"nolinenumbers", [.star, .opt], .lower .lineNumbers {}⟩,
   nothingRow "nonfrenchspacing" 0 "inter-sentence space is uniform here either way",
   ⟨"nopagecolor", [], .tokens [.ctrl (Marker.name .pageColorReset "") {}]
     (some "the document's default page ground")⟩]

private def ctrlRows6 : List CtrlRow :=
  [⟨"normalcolor", [], .tokens [.ctrl (Marker.name .ink normalInkSource) {}]
     (some "the document's normal ink, to the end of the group")⟩,
   ⟨"ofoot", [.group], .lower .runningField {}⟩,
   ⟨"ohead", [.group], .lower .runningField {}⟩,
   ⟨"onehalfspacing", [], .native (.page #[(.leading, "1.25")])⟩,
   ⟨"overprintstate", [.needed], .refuse .W0104 .each "'\\overprintstate' sets the \
overprint state; the engine knocks out every colour it paints; skipped" none⟩,
   ⟨"pagebreak", [.opt], .lower .pageBreak {}⟩,
   ⟨"pagecolor", [.opt, .needed], .lower .pageColor {}⟩,
   ⟨"pagecolorspace", [.needed], .discard pageInks "pagecolorspace"⟩,
   ⟨"pagestyle", [.group],
     .lower .pageStyle { paramStands := some "the page style in force stands" }⟩,
   ⟨"printbibliography", [.opt], .lower .printBibliography {}⟩,
   ⟨"raggedbottom", [], .native (.page #[(.bottom, "ragged")])⟩,
   refusedRow "raisebox" [.needed, .opt, .opt] "'\\raisebox' lift, height and depth are not \
applied; its content is set as if unboxed" "remove the box dimensions to use the surrounding \
line's natural spacing",
   ⟨"refstepcounter", [.needed], .lower .counter { leaves := [.outsidePreamble] }⟩,
   nothingRow "relax" 0 "it means do nothing",
   ⟨"resetpagecolorspace", [], .discard pageInks "pagecolorspace"⟩,
   ⟨"rfoot", [.group], .lower .runningField {}⟩]

private def ctrlRows7 : List CtrlRow :=
  [⟨"rhead", [.group], .lower .runningField {}⟩,
   ⟨"runninglinenumbers", [.star, .opt], .lower .lineNumbers {}⟩,
   ⟨"sectionlinesformat", [.opt, .group], .lower .sectionLines {}⟩,
   nothingRow "selectfont" 0 "font declarations apply where they stand",
   ⟨"selectlanguage", [.needed],
     .lower .selectLanguage { paramStands := some "the language in force stands" }⟩,
   ⟨"setbeamercovered", [.group], .lower .beamerCovered {}⟩,
   ⟨"setbeamerfont", [.star, .needed, .needed], .lower .beamerFont {}⟩,
   ⟨"setbeameroption", [.opt, .group], .lower .beamerOption {}⟩,
   ⟨"setbeamersize", [.needed], .lower .unreadKeys {}⟩,
   ⟨"setcitestyle", [.needed], .lower .natbibStyle declared⟩,
   ⟨"setcounter", [.needed, .needed], .lower .counter { leaves := [.outsidePreamble] }⟩,
   ⟨"setkomafont", [.needed, .needed], .lower .komaFont {}⟩,
   ⟨"setlist", [.star, .opt, .group], .lower .setList declared⟩,
   nothingRow "shortcites" 1 "citations are set short throughout, which is what it asks",
   ⟨"singlespacing", [], .native (.page #[(.leading, "1")])⟩,
   ⟨"sloppy", [], .refuse .W0104 .ctrl "'\\sloppy' loosens TeX's line-breaking \
tolerance; the breaker keeps its own and an overfull line warns by itself" none⟩]

private def ctrlRows8 : List CtrlRow :=
  [⟨"smallskip", [], .skip "smallskipamount"⟩,
   ⟨"stepcounter", [.needed], .lower .counter { leaves := [.outsidePreamble] }⟩,
   ⟨"tcbset", [.needed], .lower .unreadKeys {}⟩,
   ⟨"textasciitilde", [], .tokens [.word "~" {}] none⟩,
   ⟨"textbackslash", [], .tokens [.word "\\" {}] none⟩,
   ⟨"textbar", [], .tokens [.word "|" {}] none⟩,
   ⟨"textemdash", [], .tokens [.ctrl "emdash" {}] none⟩,
   ⟨"textendash", [], .tokens [.ctrl "endash" {}] none⟩,
   ⟨"textoverprint", [.opt, .kept], .refuse .W0104 .each "'\\textoverprint' overprints \
its text; the engine knocks it out, and the text is kept" none⟩,
   ⟨"textperiodcentered", [], .tokens [.ctrl "middot" {}] none⟩,
   ⟨"thepage", [], .tokens [.ctrl "pagenumber" {}] none⟩,
   ⟨"thispagestyle", [.group], .lower .thisPageStyle {}⟩,
   ⟨"titlegraphic", [.group], .lower .titleGraphic {}⟩,
   -- Core reads no clock, so `\today` is refused.
   refusedRow "today" [] "'\\today' asks for the day the document is built; the engine \
reads no clock, so nothing is inserted" "write the date as text where it should appear; \
\\allow{W0104} accepts the skip",
   ⟨"ul", [], .tokens [.ctrl "underline" {}] (some "\\underline")⟩,
   ⟨"unimathsetup", [.needed], .lower .uniMathSetup {}⟩]

private def ctrlRows9 : List CtrlRow :=
  [beamerConfigRow "usecolortheme" 1,
   ⟨"usefonttheme", [.opt, .group], .lower .fontTheme {}⟩,
   beamerConfigRow "useinnertheme" 1,
   beamerConfigRow "useoutertheme" 1,
   packageRow "usepackage",
   ⟨"usetheme", [.opt, .group], .lower .useTheme {}⟩,
   ⟨"vfill", [], .native (.block #[("before", "fill")])⟩,
   ⟨"vspace", [.star, .opt, .group], .lower .vspace {}⟩]

/-- The controls the dispatcher answers from its table, in byte order of their names. -/
public def ctrlRows : List CtrlRow :=
  [ctrlRows0, ctrlRows1, ctrlRows2, ctrlRows3, ctrlRows4,
   ctrlRows5, ctrlRows6, ctrlRows7, ctrlRows8, ctrlRows9].flatten

/-- The row answering a control. -/
public def ctrlRow? (name : String) : Option CtrlRow := ctrlRows.find? (·.name == name)

/-- A row's native setting, where it is one. -/
private def ctrlNative? (name : String) : Option Native.Setting :=
  match (ctrlRow? name).map (·.action) with
  | some (CtrlAction.native src) => some src
  | none | some (.tokens ..) | some (.skip _) | some (.refuse ..) | some (.discard ..)
  | some .inert | some (.lower ..) => none

/-- Options of a native package without an option reader of its own whose meaning is one native
declaration: setspace's spacings as its commands read, and microtype's switches. -/
public def packageOptionNatives : List (String × List (String × Native.Setting)) :=
  let off : Native.Setting := .page #[(.protrusion, "off"), (.expansion, "off")]
  [("setspace", ["singlespacing", "onehalfspacing", "doublespacing"].filterMap fun o =>
     (ctrlNative? o).map (o, ·)),
   ("microtype", [("protrusion", .page #[(.protrusion, "on")]),
     ("protrusion=true", .page #[(.protrusion, "on")]),
     ("protrusion=false", .page #[(.protrusion, "off")]),
     ("expansion", .page #[(.expansion, "on")]), ("expansion=true", .page #[(.expansion, "on")]),
     ("expansion=false", .page #[(.expansion, "off")]),
     ("disable", off), ("disable=true", off), ("activate=false", off)])]

/-- moloch's `block` option values as the theme's own block
colour declarations. -/
private def molochBlockColors : String → Option (List (String × String))
  | "fill" => some [("block title", "bg=normal text.bg!80!fg"),
      ("block body", "use=block title,bg=block title.bg!50!normal text.bg"),
      ("block title alerted", "bg=block title.bg"),
      ("block title example", "bg=block title.bg")]
  | "transparent" => some [("block title", "bg="), ("block body", "bg="),
      ("block title alerted", "bg="), ("block title example", "bg=")]
  | _ => none

/-- moloch's options: `block` declares the theme's block colours, `sectionpage=none` drops its
section page as its own `\AtBeginSection{}` does; every other key is named. -/
private def molochOptions (cmd src : String) (pos : Pos) : M (Array Raw) := do
  let mut out := #[]
  for entry in KeyVal.items src do
    match KeyVal.entry entry with
    | ("sectionpage", some "none") =>
      became s!"{cmd} sectionpage=none" "\\AtBeginSection{}: no section page, as moloch's own" pos
      out := out ++ #[.ctrl "AtBeginSection" pos, .group #[] pos]
    | (key, some value) =>
      match key, molochBlockColors value with
      | "block", some decls =>
        became s!"{cmd} block={value}" "moloch's block colours, declared with \\setbeamercolor" pos
        for (element, body) in decls do
          out := out ++ #[.ctrl BeamerColor.marker pos, .group #[.word element pos] pos,
            .group #[.word body pos] pos]
      | "block", none =>
        sayOnce ("moloch:" ++ key) .W0104
          s!"'{cmd}' option '{key}={value}' is moloch configuration the engine does not have; skipped" pos
          (help := "moloch's block option takes fill or transparent")
      | _, _ =>
        sayOnce ("moloch:" ++ key) .W0104
          s!"'{cmd}' option '{key}={value}' is moloch configuration the engine does not have; skipped" pos
    | (key, none) =>
      sayOnce ("moloch:" ++ key) .W0104
        s!"'{cmd}' option '{key}' is moloch configuration the engine does not have; skipped" pos
  return out

/-- A beamer theme's options: moloch's read as its own, any other theme's named unread at the load
spelled `load`. -/
private def themeOptions (cmd load tname opts : String) (pos : Pos) : M (Array Raw) := do
  if tname == "moloch" then return ← molochOptions cmd opts pos
  if (Theme.find? tname).isNone then return #[]
  for o in KeyVal.items opts do
    unreadParam s!"usetheme:{tname}" (KeyVal.entry o).1 s!"'{load}' option '{o}'" pos
  return #[]

/-- The finite block-hook grammar: whitespace and the kernel's skip commands at their default
amounts. -/
private def blockHookSkips (out : Array Native.Setting) : List Raw → Option (Array Native.Setting)
  | [] => some out
  | .space :: rest => blockHookSkips out rest
  | .ctrl name _ :: rest =>
    match (ctrlRow? name).map (·.action) with
    | some (CtrlAction.skip amount) =>
      (kernelSkip amount).bind fun v => blockHookSkips (out.push (skipNative { width := v })) rest
    | none | some (.tokens ..) | some (.native ..) | some (.refuse ..) | some (.discard ..)
    | some .inert | some (.lower ..) => none
  | _ => none

/-- `\addtobeamertemplate` on the block templates, read
where it is a top-level preamble addition. -/
private def blockHookArm (pos : Pos) (raws : Array Raw) (start : Nat) :
    M (Option (Array Raw × Nat)) := do
  let (args, k) := takeGroups raws start 3
  let element := (rawSrc (args.getD 0 #[])).trimAscii.toString
  match blockHookSkips #[] (args.getD 1 #[]).toList,
      blockHookSkips #[] (args.getD 2 #[]).toList with
  | some before, some after =>
    -- premise: beamerHookChecks — scoped additions cannot set a global gap
    if args.size == 3 && element == "block begin" && before.isEmpty && (← docPreamble) then
      let native := String.join (after.toList.filterMap (·.note?))
      let spacing ← after.foldlM (init := #[]) fun out s => return out ++ (← carry s pos)
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

/-- Whether a footline body reads exactly the standout foreground and the
current canvas background. -/
private def standoutFootColors (body : Array Raw) : Bool :=
  let fields := (KeyVal.items (rawSrc body)).toList
  let entries := fields.filterMap fun e => match KeyVal.entry e with
    | (k, some v) => some (k, v)
    | (_, none) => none
  fields.length == 3 && entries.length == 3 &&
    entries.lookup "fg" == some "standout.fg" &&
    entries.lookup "bg" == some "background canvas.bg" &&
    ((entries.lookup "use").map KeyVal.items) == some #["standout", "background canvas"]

/-- Whether an appended body is the supported standout footline restoration. -/
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

/-- The appended alias grammar, its operands kept as original groups. -/
private def standoutAliasList (out : Array Raw) : List Raw → Option (Array Raw)
  | [] => some out
  | .ctrl "colorlet" pos :: .group name np :: .group source sp :: rest =>
    standoutAliasList
      (out ++ #[.ctrl BeamerColor.standoutMarker pos, .group name np, .group source sp]) rest
  | _ => none

/-- etoolbox's append onto the beamer standout option, of which only the empty
success callback runs. -/
private def standoutFootHookArm (pos : Pos) (raws : Array Raw) (start : Nat) :
    M (Option (Array Raw × Nat)) := do
  let (args, k, tail) := takeHookArgs raws start
  -- premise: beamerHookChecks — altered bodies, callbacks and scopes refuse whole
  if args.size == 4 && (← get).deck && (← docPreamble) &&
      ctrlName (args.getD 0 #[]) == some "KV@beamerframe@standout" &&
      (args.getD 2 #[]).all (· matches .space) then
    if standoutFootBody (args.getD 1 #[]) then
      return some ((← setting "\\apptocmd{\\KV@beamerframe@standout}"
        (.chrome #[("standout-note", "true")]) pos) ++ tail, k)
    -- premise: standoutPaletteChecks — aliases change only standout frames
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

/-- Whether `\alert` takes the alert colour: a shipped theme
stands, or the deck names none. -/
private def alertThemed : M Bool := do
  let st ← get
  return st.themed || (st.deck && !st.themeNamed)

/-- `\alert{body}` without an overlay spec. -/
private def alertPlain (pos : Pos) (raws : Array Raw) (start : Nat) (picture : Bool := false) :
    M (Option (Array Raw × Nat)) := do
  let themed ← alertThemed
  let (args, k) := takeGroups raws start 1
  match args[0]? with
  | some body =>
    if themed && !picture then
      became "\\alert" "the alert colour" pos
      return some (#[.ctrl (alertMark true) pos, .group body pos], k)
    became "\\alert"
      (if themed then "\\textcolor{alert}{...}" else "{\\bfseries ...}") pos
    return some (alertStyled themed body pos, k)
  | none =>
    if themed then
      let alert := Native.Head.textcolor "alert"
      became "\\alert" alert.render pos
      return some (alert.raws pos, start)
    else
      became "\\alert" "\\textbf" pos
      return some (#[.ctrl "textbf" pos], start)

/-- The list depth each of beamer's three marker templates selects. -/
private def beamerMarkerElement : String → Option String
  | "itemize item" => some "itemize"
  | "itemize subitem" => some "itemize2"
  | "itemize subsubitem" => some "itemize3"
  | _ => none

/-- A colour-box footer with a left note and a right frame counter, as the
native two-slot footer. -/
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

/-- A template body with `#1` replaced by the declared default. -/
private def substArg (default : Array Raw) : List Raw → Array Raw → Array Raw
  | [], acc => acc
  | .sym '#' _ :: .word w p :: rest, acc =>
    if w == "1" then substArg default rest (acc ++ default)
    else if w.startsWith "1" then substArg default rest ((acc ++ default).push (.word (w.drop 1).toString p))
    else substArg default rest ((acc.push (.sym '#' p)).push (.word w p))
  | r :: rest, acc => substArg default rest (acc.push r)

/-- The line ends at the braces of the group at or after
`j`, which TeX reads as spaces. -/
private def bodyEdges (raws : Array Raw) (j : Nat) : Bool × Bool :=
  match raws[skipSpaces raws j]? with
  | some (.group _ gp) => (gp.openEol, gp.closeEol)
  | _ => (false, false)

/-- Installs a block template, replacing what
`\addtobeamertemplate` appended to the one before. -/
private def installBlockTemplate (element : String) (body : Array Raw) (pos : Pos) : M Unit :=
  write fun st => { st with
    beamerTemplates := Ir.redeclare st.beamerTemplates element (st.file, pos, body)
    beamerBlockBegin := if element == "block begin" then #[] else st.beamerBlockBegin }

/-- The block templates the preamble installed, read in pairs where it ends. -/
private def flushBeamerBlocks : M (Array Raw) := do
  let installed := (← get).beamerTemplates
  if installed.isEmpty then return #[]
  let mut out : Array Raw := #[]
  for (kind, beginEl, endEl, styleEl, titleEl, bodyEl) in blockTemplateKinds do
    let b := installed.find? (·.1 == beginEl)
    let e := installed.find? (·.1 == endEl)
    let site := match b, e with
      | some (_, f, p, _), _ => some (f, p)
      | none, some (_, f, p, _) => some (f, p)
      | none, none => none
    let some (file, pos) := site | continue
    let savedFile := (← get).file
    write fun st => { st with file := file }
    let wrap (rs : Array Raw) : Array Raw :=
      if file == savedFile then rs else #[Raw.env (Parse.inputEnv file) rs pos]
    let st ← get
    let defs : String → Option BlockTemplate.Macro := fun n =>
      match st.templateBinds[n]? with
      | some (some v) =>
        some { serial := v.serial, arity := v.arity, body := BlockTemplate.edged v.edges v.raws
               optional := v.optional.map (·.2) }
      | _ => none
    let flags : String → Option Bool := fun x => st.templateFlags[x]?
    let unread : Array String ← match b, e with
      | some (_, _, _, bb), some (_, _, _, eb) =>
        -- premise: unreadTemplateChecks — templates no document follows shape no block
        if !st.wholeDoc then pure #["no '\\begin{document}' ends a preamble for them"] else
        -- premise: capitalRegisterChecks — no text outside the templates reads their registers
        let lengths : String → Option (Option BlockTemplate.Dimen) := fun n =>
          if st.allocated.contains n then some none else none
        -- premise: wholeBarReadingChecks — templates run against the state the body began in
        let drift := (closeNames st.templateBinds (namesIn (namesIn #[] bb.toList) eb.toList)).filter
          st.templateDrift.contains
        if !drift.isEmpty then
          pure #[s!"the document's body changes {String.intercalate ", " (drift.toList.map ("\\" ++ ·))}, \
which they run, before a block"]
        else
        match BlockTemplate.read bb eb defs (st.serial + 1) lengths flags with
        | .error us => pure us
        | .ok r =>
          -- The kind's own element binds the foreground last.
          let inks (p : Option BlockTemplate.Paint) (el : String) : Bool :=
            match p with
            | some (.beamer (latest :: _) "fg") => latest == el
            | _ => false
          let titleOk := r.titleFont == some titleEl && inks r.titlePaint titleEl
          let bodyOk := (r.bodyFont.isNone || r.bodyFont == some bodyEl) &&
            (r.bodyPaint.isNone || inks r.bodyPaint bodyEl)
          if !titleOk then pure #[s!"a title set in another font or colour than '{titleEl}'"]
          else if !bodyOk then pure #[s!"a body set in another font or colour than '{bodyEl}'"]
          else if r.edges.any (fun e => e.paint.any fun
              | .named n => !Decl.wholeValue n
              | .beamer .. => false) then
            pure #["a rule painted in a colour no palette entry spells"]
          else
            let mut colors : Array String := #[]
            for (edge, i) in r.edges.zipIdx do
              let role := kind.roleStem ++ "edge" ++ (if i == 0 then "" else toString (i + 1))
              match edge.paint with
              | some (.beamer chain ch) =>
                let elements := chain.toArray.map fun el => Raw.group #[.word el pos] pos
                out := out ++ wrap #[.ctrl BeamerColor.siteMarker pos, .group elements pos,
                  .group #[.word ch pos] pos, .group #[.word role pos] pos]
                colors := colors.push role
              | some (.named n) =>
                out := out ++ wrap (← carry (.palette #[(role, n)]) pos)
                colors := colors.push role
              | none => colors := colors.push "fg"
            became s!"{beginEl} / {endEl}" s!"the shape of each '{styleEl}'" pos
            let decl := TemplateDecl.block styleEl r colors file pos
            write fun st => { st with templates := st.templates.push decl }
            pure #[]
      | some _, none => pure #[s!"its '{endEl}' half, which the document never sets"]
      | none, _ => pure #[s!"its '{beginEl}' half, which the document never sets"]
    unless unread.isEmpty do
      sayOnce ("beamer:template:" ++ beginEl) .W0110
        s!"the '{beginEl}' and '{endEl}' templates are not read: \
{String.intercalate "; " unread.toList}; those blocks keep beamer's default template" pos
        (help := "write the template with \\setbox, \\vbox, \\llap, \\vrule, \\strut and \\usebeamercolor")
    write fun st => { st with file := savedFile }
  return out

/-- A stored footer resolved through the font-size marker
and native footer declarations. -/
private def flushBeamerFootline : M (Array Raw × Array Raw) := do
  let some (file, pos, body) := (← get).beamerFootline | return (#[], #[])
  let savedFile := (← get).file
  let wrap (rs : Array Raw) : Array Raw :=
    if file == savedFile then rs else #[Raw.env (Parse.inputEnv file) rs pos]
  if body.isEmpty then
    return (wrap #[.ctrl "runningfoot" pos, .group #[.ctrl "hfill" pos] pos],
      wrap #[Raw.ctrl "framefoot" pos, Raw.group #[] pos])
  let some (left, counter, fontName, options) := numberedFootline? body
    | return (#[], #[])
  write fun st => { st with file := file }
  let mut fontPrefix : Array Raw := #[]
  let mut unread : Array String := #[]
  if let some name := fontName then
    if let some fields := (← get).beamerFonts.toList.lookup name then
      let font := beamerTemplateFont name fields pos
      if let some size := font.size then
        fontPrefix := fontPrefix.push (.ctrl (Marker.fontSizeName size (font.leading.getD "")) pos)
      fontPrefix := fontPrefix ++ (templateFontCommands fields pos).map (rebase (fun _ => pos) true)
      unread := font.unread
      -- premise: beamerTemplateChecks — the selected font reaches the footer note
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
  let pre ← carry (.chrome #[("footer", "{right=\\" ++ counter ++ "}")]) pos
  let note := #[Raw.ctrl "framefoot" pos, Raw.group (fontPrefix ++ left) pos]
  write fun st => { st with file := savedFile }
  return (wrap pre, wrap note)

/-- The marker of a spliced file's option diagnostics request, unforgeable
because it holds a space. -/
private def styOptionsLoadMark : String := "package options load"
private def styOptionsProcessedMark : String := "package options processed"
private def styOptionsUnhandledMark : String := "package options unhandled"

private def unhandledStyOption (pkg option why : String) (pos : Pos) : M Unit :=
  sayOnce ("package-option:" ++ pkg ++ ":" ++ option) .W0110
    s!"option '{option}' for local package '{pkg}' {why}; ignored" pos
    (help := "remove the option or declare and process its handler in the local style")

/-- A spliced file's option diagnostics, settled through the accounting door of
other ignored options. -/
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
    -- premise: packageOptionChecks — only a live process discharges its options
    if raws.any (fun r => r matches .ctrl "package options processed" _) then
      discard s!"option list for local package '{pkg}'"
        "its options are checked by '\\ProcessOptions'" ("package-options:" ++ pkg) pos
    else
      for r in args.getD 1 #[] do
        if let .word option _ := r then
          unhandledStyOption pkg option "was not processed" pos
  return some (#[], k)

/-- The first share in a two-column `\columnratio` declaration, in per mille. -/
private def paracolRatio? (src : String) : Option Nat := do
  let first ← (KeyVal.items src)[0]?
  let (m, scale) ← Decl.parseDecimal first
  let p := m * 1000 / scale
  guard (0 < p && p < 1000)
  return p.toNat

private def paracolFactor (p : Nat) : String :=
  let digits := toString (p % 1000)
  "0." ++ "".pushn '0' (3 - digits.length) ++ digits

/-- One citation's arguments as written: a star, the optional notes, the keys'
group, and the index past them. -/
private def citeArgs (raws : Array Raw) (start : Nat) : Bool × Array Raw × Nat :=
  let j0 := skipSpaces raws start
  let star := raws[j0]? matches some (.word "*" _) || raws[j0]? matches some (.sym '*' _)
  let j1 := if star then j0 + 1 else start
  let (_, j2) := takeRawOpt raws j1
  let (_, j3) := takeRawOpt raws j2
  let (_, j4) := takeGroups raws j3 1
  (star, raws.extract j1 j4, j4)

/-- biblatex's citation commands on the natbib door. -/
private def biblatexCiteArm (name : String) (pos : Pos) (raws : Array Raw) (start : Nat) :
    M (Option (Array Raw × Nat)) := do
  let authoryear := (← get).bibStyle == some "plainnat"
  -- premise: biblatexSuperciteChecks — without biblatex this arm reads neither command
  if (name == "Cite" || name == "supercite") && !(← get).loads.pkgs.any (·.1 == "biblatex") then
    return none
  let (star, args, k) := citeArgs raws start
  let to (cmd : String) : Option (Array Raw × Nat) := some (#[.ctrl cmd pos] ++ args, k)
  match name with
  | "supercite" =>
    if authoryear then return to "citealp"
    say .W0428 "'\\supercite' sets its citation as '\\cite' does, in brackets on the line, \
      where the style sets it as a superscript" pos (subject := some "citecmd:supercite")
    let keys := (args.filter (· matches .group ..)).back?
    return some (#[.ctrl "cite" pos] ++ keys.toArray, k)
  | "autocite" | "parencite" =>
    return to (if star && authoryear then "citeyearpar" else "citep")
  | "Autocite" | "Parencite" => return to "Citep"
  | "textcite" => return to "citet"
  | "Textcite" => return to "Citet"
  | "Cite" => return to (if authoryear then "Citealp" else "Citep")
  | _ =>
    let note := if name == "footcitetext" then "footnotetext" else "footnote"
    let cmd := if name == "Footcite" || name == "Smartcite" then "Citealp"
      else if name == "footfullcite" then "fullcite" else "citealp"
    return some (#[.ctrl note pos, .group (#[.ctrl cmd pos] ++ args ++ #[.word "." pos]) pos], k)

/-- biblatex's multicite commands: a run of citations, each
with its own notes. -/
private def biblatexMulticiteArm (name : String) (pos : Pos) (raws : Array Raw) (start : Nat) :
    M (Option (Array Raw × Nat)) := do
  let authoryear := (← get).bibStyle == some "plainnat"
  let mut parts : Array (Array Raw) := #[]
  let mut j := start
  for _ in [0:raws.size] do
    let (_, j1) := takeRawOpt raws j
    let (_, j2) := takeRawOpt raws j1
    let (gs, j3) := takeGroups raws j2 1
    if gs.isEmpty then break
    parts := parts.push (raws.extract (skipSpaces raws j) j3)
    j := j3
  if parts.isEmpty then return none
  let textual := name == "textcites" || name == "Textcites"
  let foot := name == "footcites" || name == "smartcites" || name == "Smartcites"
  let up := name.front.isUpper
  let cmdOf (i : Nat) : String :=
    if textual then (if up && i == 0 then "Citet" else "citet")
    else if up && i == 0 then "Citealp" else "citealp"
  let sepBefore (i : Nat) : Array Raw :=
    if textual then
      (if i + 1 == parts.size then #[.space, .word "and" pos, .space] else #[.word "," pos, .space])
    else #[.word (if authoryear then ";" else ",") pos, .space]
  let mut body : Array Raw := #[]
  for (p, i) in parts.zipIdx do
    if i > 0 then body := body ++ sepBefore i
    body := body ++ #[.ctrl (cmdOf i) pos] ++ p
  let bare := (name == "cites" || name == "Cites") && authoryear
  let out : Array Raw :=
    if foot then #[.ctrl "footnote" pos, .group (body.push (.word "." pos)) pos]
    else if textual || bare then body
    else #[.ctrl "citetext" pos, .group body pos]
  return some (out, j)

/-- The mark a blueprint's `\github` or `\dochome` leaves in the preamble, its command's name and
its URL in the groups after it. -/
public def blueprintSiteMark : String := "blueprint site"

/-- Names leanblueprint's dependency graph, which the engine does not draw, at one site asking for
it, the site's particulars its detail. -/
private def blueprintGraph (pos : Pos) (detail : Option String) : M Unit :=
  say .W0434 "leanblueprint's dependency graph is not drawn; the web page names beside each \
statement what it uses and proves" pos
    (help := some "each statement's uses stand as cross-references beside it; \\allow{W0434} \
accepts the loss")
    (subject := some "package:blueprint") (detail := detail) (output := some .html)

/-- A URL's text as hyperref reads it: a TeX special escaped with a backslash is the character, and
a space none, since a URL holds none. -/
private def urlText (raws : Array Raw) : String :=
  raws.foldl (init := "") fun acc r =>
    let piece := match r with
      | .word w _ => w
      | .sym c _ => String.singleton c
      | .ctrl n _ => if ["#", "%", "&", "_", "~", "$"].contains n then n else "\\" ++ n
      | .space | .par _ => ""
      | .group .. | .math .. | .env .. | .verb .. => rawSrcOne r
    acc ++ piece

/-- An option value's URL as hyperref reads it, its one brace group and the specials TeX escapes
undone, a space dropped. -/
private def urlOption (v : String) : String :=
  let (out, _) := (KeyVal.unbrace v).foldl (init := ("", false)) fun (acc, esc) c =>
    if esc then
      if "#%&_~$".contains c then (acc.push c, false)
      else if c == ' ' then (acc ++ "\\", false) else ((acc ++ "\\").push c, false)
    else if c == '\\' then (acc, true)
    else if c == ' ' then (acc, false)
    else (acc.push c, false)
  out

/-- The site mark one declaration leaves for the preamble's reader. -/
private def blueprintSiteRaws (key : String) (url : String) (pos : Pos) : Array Raw :=
  #[.ctrl blueprintSiteMark pos, .group #[.word key pos] pos, .group #[.word url pos] pos]

private def rewriteCtrlLaterNamed (name : String) (pos : Pos) (raws : Array Raw)
    (start : Nat) : M (Option (Array Raw × Nat)) := do
  match name with
  | "addtobeamertemplate" => blockHookArm pos raws start
  | "apptocmd" => standoutFootHookArm pos raws start
  | "setbox" | "sbox" | "savebox" =>
    -- A box assigned to the strut box sets its height and depth anew.
    if raws[skipSpaces raws start]? matches some (.ctrl "strutbox" _) then
      write fun st => { st with strutSkip := none }
    return none
  | "linespread" | "setstretch" =>
    -- setspace's parameterised form is `\linespread` by another name.
    write fun st => { st with strutSkip := none }
    let (args, k) := takeGroups raws start 1
    if args.isEmpty then return none
    if ← paramArgs args then
      unappliedParam name "the leading keeps its value" pos
      return some (#[], k)
    let factor := (rawSrc (args.getD 0 #[])).trimAscii.toString
    unless Decl.wholeValue factor do
      sayOnce ("ctrl:" ++ name) .W0104 s!"'\\{name}' is given a factor this engine cannot read; \
skipped, and the leading keeps its value" pos (help := "give a number, such as \\linespread{1.2}")
      return some (#[], k)
    return some (← setting s!"\\{name}" (.page #[(.leading, factor)]) pos, k)
  | "xspace" =>
    -- xspace: a space unless punctuation follows.
    let punct (c : Char) : Bool :=
      c == '.' || c == ',' || c == '\'' || c == '/' || c == '?' ||
      c == ';' || c == ':' || c == '!' || c == '~' || c == '-' || c == ')'
    let noSpace := match raws[start]? with
      | some (.word w _) => (w.toList.head?.map punct).getD false
      | some (.sym c _) => punct c
      | some .space | some (.par _) => true
      | _ => false
    return some (if noSpace then #[] else #[.ctrl " " pos], start)
  | "autocite" | "Autocite" | "parencite" | "Parencite" | "textcite" | "Textcite" | "Cite"
  | "footcite" | "Footcite" | "smartcite" | "Smartcite" | "footcitetext" | "footfullcite"
  | "supercite" =>
    biblatexCiteArm name pos raws start
  | "cites" | "Cites" | "parencites" | "Parencites" | "textcites" | "Textcites"
  | "autocites" | "Autocites" | "footcites" | "smartcites" | "Smartcites" =>
    biblatexMulticiteArm name pos raws start
  | "fontsize" =>
    -- NFSS records the two dimensions and `\selectfont` commits them.
    write fun st => { st with strutSkip := none }
    let (args, k) := takeGroups raws start 2
    if args.size < 2 then
      say .E0304 "'\\fontsize' needs {size} and {leading} groups" pos
      return some (#[], k)
    let size := rawSrc (args.getD 0 #[])
    let leading := rawSrc (args.getD 1 #[])
    became "\\fontsize" "an affine font size and baseline skip" pos
    return some (#[.ctrl (Marker.fontSizeName size leading) pos], k)
  | "foreignlanguage" =>
    let (_, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 2
    if h : args.size = 2 then
      if ← paramArgs #[args[0]] then
        unappliedParam "foreignlanguage" "its text keeps the language in force" pos
        return some (#[], (takeGroups raws j 1).2)
      let lname := rawSrc args[0]
      let tag := Locale.babelTagOf lname
      if (Locale.forTag tag).isNone then
        say .W0368 s!"no locale for language '{lname}'; English captions \
and patterns stand in" pos
          (help := Locale.shippedHelp)
      became s!"\\foreignlanguage\{{lname}}" s!"the '{tag}' language attribute" pos
      return some (#[.group (#[Raw.ctrl (Marker.name .lang tag) pos] ++ args[1]) pos], k)
    else return none
  | "enquote" =>
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
    let (model, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    if args.isEmpty then return none
    let value := rawSrc (args.getD 0 #[])
    let source := modeledColorSource model value
    match model with
    | some m => became s!"\\color[{m}]\{{value}}" s!"the {source} ink declaration" pos
    | none => became s!"\\color\{{value}}" s!"\\{value}" pos
    return some (#[.ctrl (Marker.name .ink source) pos], skipSpaces raws k)
  | "vskip" =>
    -- Unlike `\vspace`, `\vskip` leaves its own glue as the last skip (`kind = vskip`).
    if (← get).inDef then return none
    let v0 := skipSpaces raws start
    let e := glueEnd raws v0
    let sp := skipSrc (lengthSrc (raws.extract v0 e))
    if e ≤ v0 || (sp.width != "fill" && (Decl.parseGlue sp.width).isNone) then return none
    return some (← setting "\\vskip" (skipNative sp "vskip") pos, e)
  | "varul" =>
    let mut j := skipSpaces raws start
    if let some (.word w _) := raws[j]? then
      if w.startsWith "<" && w.endsWith ">" then
        j := j + 1
    let (_, j1) := takeOpt raws j
    let (_, j2) := takeOpt raws j1
    became "\\varul" "\\underline" pos
    return some (#[.ctrl "underline" pos], j2)
  | "ExplSyntaxOn" =>
    -- expl3 holds no document content: pdfmeta's colour profile properties are read in the
    -- preamble, the rest skipped.
    let mut k := start
    let mut stop := raws.size
    for j in [start:raws.size] do
      k := j + 1
      if let some (.ctrl "ExplSyntaxOff" _) := raws[j]? then
        stop := j
        break
    -- premise: Tests.PrintX4.checks — a description in the body leaves its page as written
    let (out, rest) ← if (← get).inDoc then pure (#[], true)
      else explProfiles (raws.extract start stop) pos
    if rest then
      say .W0106 "code between '\\ExplSyntaxOn' and '\\ExplSyntaxOff' is not supported; skipped" pos
    return some (out, k)
  | "setmathfont" =>
    let (beforeRaws, j) := takeRawOpt raws start
    let (args, k) := takeGroups raws j 1
    let (afterRaws, k) := takeRawOpt raws k
    if ← paramArgs args #[beforeRaws, afterRaws] then
      unappliedParam "setmathfont" "the math face in force stands" pos
      return some (#[], k)
    let (optBefore, optAfter) := (beforeRaws.map rawSrc, afterRaws.map rawSrc)
    let family := rawSrc (args.getD 0 #[])
    let path : Option String :=
      ([optBefore, optAfter].filterMap id).findSome? fun opts =>
        (KeyVal.items opts).findSome? fun kv =>
          match KeyVal.entry kv with
          | ("Path", some v) => some v
          | _ => none
    let dir := (path.map fun d => #[("dir", Decl.quote d)]).getD #[]
    return some (← setting "\\setmathfont" (.fonts (dir.push ("math", Decl.quote family))) pos, k)
  | "def" | "edef" | "gdef" | "xdef" =>
    -- A plain `\def` with undelimited parameters declares exactly what `\define` declares.
    let expanding := name == "edef" || name == "xdef"
    let j := skipSpaces raws start
    let cmd? := match raws[j]? with
      | some (.ctrl c _) => some c
      | _ => none
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
      -- A stretch the next font selection reads sets the strut box again there.
      if cmd == "baselinestretch" then write fun st => { st with strutSkip := none }
      if found && !expanding && arity == some 0 && (← docPreamble) then
        if let (some level, some (.group body _)) := (listLevelOf cmd, raws[k]?) then
          if ← listLevelDef level s!"\\{name}\{\\{cmd}}" body pos then
            return some (#[], k + 1)
      if let some why := macroParams.lookup cmd then
        if found && arity == some 0 then
          nameParam cmd why pos
          return some (#[], k + 1)
      if found && !expanding && arity.isSome then
        let n := arity.getD 0
        let spec := String.ofList (List.replicate n 'm')
        let native := Native.Head.define cmd (signature spec)
        -- premise: ignoredDefinitionChecks — an ignored built-in's refusal is its one accounting
        unless (← get).ignoredDefs.contains cmd do
          write fun st => { st with
            bound := if st.bound.contains cmd then st.bound else st.bound.push cmd }
          became s!"\\{name}\{\\{cmd}}" (native.render ++ " {...}") pos
        write fun st => { st with bodyNext := 1, quietNext := st.templateCode.contains cmd }
        return some (native.raws pos, k)
      else
        let k2 := if found then k + 1 else k
        let demote := styInternal (← get).file name
        if expanding then
          sayOnce ("ctrl:" ++ name) .W0357
            s!"'\\{name}' expands its text where it is defined; this text reaches past what the \
engine expands, so it is skipped" pos
            (help := "an edef expands text, lengths, '\\the', '\\number', '\\strip@pt', \
'\\dimexpr' and the document's macros; \\define \\name(...) {body} declares the rest") demote
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
    let (args, j) := takeGroups raws (skipStar raws start) 1
    let envName := rawSrc (args.getD 0 #[])
    let (count, j) := takeOpt raws j
    let (dflt, jd) := takeRawOpt raws j
    let n := (count.bind String.toNat?).getD 0
    let spec := if dflt.isSome then "o" ++ String.ofList (List.replicate (n - 1) 'm')
      else String.ofList (List.replicate n 'm')
    if ← refusedEnvDef name envName spec false pos then
      return some (#[.group #[] pos], (takeGroups raws jd 2).2)
    if name == "renewenvironment" && count.isNone && dflt.isNone then
      -- premise: captionScopeChecks — the float-core idiom reads as its native kind
      if let some (out, k) ← floatRedef? envName.trimAscii.toString raws jd pos then
        return some (out, k)
    let native := Native.Head.defineEnv envName (signature spec)
    let env := envName.trimAscii.toString
    -- premise: ignoredDefinitionChecks — a refused built-in's refusal is its one accounting
    unless (← get).ignoredDefs.contains (Tcolorbox.bindingName env) ||
        floatRedefEnvs.contains env || env == "abstract" do
      became s!"\\{name}\{{envName}}"
        (native.render ++ (if dflt.isSome then " [default]" else "") ++ " {begin} {end}") pos
    -- The default stays in the walk, rewritten where it stands, its groups no body.
    write fun st => { st with
      bodyNext := 2, envNext := 2, defaultAt := if dflt.isSome then .awaiting else .none }
    unless (← get).inDef do
      write fun st => { st with
        discardEnvs := st.discardEnvs.filter (·.1 != envName.trimAscii.toString) }
    return some (native.raws pos, j)
  | "newtheorem" =>
    let (env, _) := takeGroups raws (skipStar raws start) 1
    unless ← refusedEnvDef name (rawSrc (env.getD 0 #[])) "o" false pos do return none
    return some (#[.group #[] pos], theoremDeclEnd raws name start)
  | "defineenv" =>
    let j := skipSpaces raws start
    let some (.group env _) := raws[j]? | return none
    let stop := defineEnvEnd raws start
    unless ← refusedEnvDef name (rawSrc env) (nativeEnvSpec (rawSrc (raws.extract (j + 1) stop)))
        false pos do
      return none
    return some (#[.group #[] pos], stop)
  | "NewEnviron" | "RenewEnviron" =>
    let (args, j) := takeGroups raws (skipStar raws start) 1
    let envName := rawSrc (args.getD 0 #[])
    let (count, j0) := takeOpt raws j
    let (dflt, j) := takeRawOpt raws j0
    let b := skipSpaces raws j
    let n := (count.bind String.toNat?).getD 0
    let spec := if dflt.isSome then "o" ++ String.ofList (List.replicate (n - 1) 'm')
      else String.ofList (List.replicate n 'm')
    let discards := match raws[b]? with
      | some (.group code _) => (bodySlot? code).isNone && !mentionsBody code.toList
      | _ => false
    if ← refusedEnvDef name envName spec discards pos then
      -- environ's test for a final code reads past the spaces after a definition without one.
      let k := if raws[b]? matches some (.group _ _) then
          match takeRawOpt raws (b + 1) with
          | (some _, k) => k
          | (none, _) => skipSpaces raws (b + 1)
        else j
      return some (#[.group #[] pos], k)
    let native := Native.Head.defineEnv envName (signature spec)
    match raws[b]? with
    | some (.group code _) =>
      let slot := (bodySlot? code).isSome
      if slot || !mentionsBody code.toList then
        let env := envName.trimAscii.toString
        -- environ's definition of a float is never the kernel-core idiom, so it is ignored whole.
        let ignored := (← get).ignoredDefs.contains (Tcolorbox.bindingName env) ||
          floatRedefEnvs.contains env
        unless ignored do
          became s!"\\{name}\{{envName}}" (native.render ++ (if dflt.isSome then " [default]" else "") ++
            (if slot then " {code before \\BODY} {code after it}"
              else " {} {code}, its body discarded")) pos
        write fun st => { st with
          bodyNext := 1, envNext := 1, defaultAt := if dflt.isSome then .awaiting else .none }
        -- premise: ignoredDefinitionChecks — an ignored built-in's definition discards no use
        unless (← get).inDef || ignored do
          write fun st => { st with
            discardEnvs := if slot then st.discardEnvs.filter (·.1 != env)
              else Ir.redeclare st.discardEnvs env spec }
        let mark := if (← get).inDoc then #[] else #[Raw.ctrl (Marker.name .environBody "") pos]
        return some (native.raws pos ++ mark, j0)
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
    -- A TeX conditional left here configures absent machinery and is skipped whole.
    let mut k := start
    for j in [start:raws.size] do
      k := j + 1
      if let some (.ctrl "fi" _) := raws[j]? then break
    sayOnce "ctrl:ifdefined" .W0104
      s!"TeX conditional ('\\{name}' … '\\fi') is not supported; skipped whole" pos
    return some (#[], k)
  | "theme" =>
    -- The native spelling turns the themed mappings on exactly as `\usetheme` does.
    let (args, _) := takeGroups raws start 1
    let tname := (rawSrc (args.getD 0 #[])).trimAscii.toString
    write fun st => { st with themeNamed := true }
    if (Theme.find? tname).isSome then
      write fun st => { st with themed := true, beamerTheme := tname }
    return none
  | "alert" =>
    let j := skipSpaces raws start
    match raws[j]? with
    | some spec@(.word w _) =>
      if (overlayWord? spec).isNone then return ← alertPlain pos raws start
      became s!"\\alert{w}" "a conditional alert style" pos
      return some (#[.ctrl (alertMark (← alertThemed)) pos, spec], j + 1)
    | _ => alertPlain pos raws start
  | "style" =>
    let (args, k) := takeGroups raws start 2
    if args.size != 2 then return none
    return some (#[.ctrl name pos] ++ raws.extract start k, k)
  | "fonts" =>
    -- Counted so a later `\newfontfamily` takes the next slot.
    let (args, _) := takeGroups raws start 1
    for entry in Decl.splitEntries (rawSrc (args.getD 0 #[])) do
      if let some (key, _) := Decl.splitEntry entry then
        if let ["family", n] := key.splitOn "." then
          unless (← get).fontFamilies.contains n do
            write fun st => { st with fontFamilies := st.fontFamilies.push n }
    return none
  | "defbeamertemplate" =>
    let j := skipStar raws start
    let starred := j != skipSpaces raws start
    let (args, j) := takeGroups raws j 2
    let element := (rawSrc (args.getD 0 #[])).trimAscii.toString
    if args.size != 2 || !blockTemplateElement element then return none
    let name := (rawSrc (args.getD 1 #[])).trimAscii.toString
    let (arity, j) := takeOpt raws j
    let (default, j) := takeRawOpt raws j
    let (bodyArgs, k) := takeGroups raws j 1
    if bodyArgs.size != 1 then return none
    let body := BlockTemplate.edged (bodyEdges raws j) (bodyArgs.getD 0 #[])
    let body := match arity.map (·.trimAscii.toString) with
      | some "1" => substArg (default.getD #[]) body.toList #[]
      | _ => body
    if (← get).inDoc then
      sayOnce ("beamer:template:" ++ element) .W0104
        s!"'\\defbeamertemplate\{{element}}' in the document body is skipped: \
only preamble block templates are read" pos
        (help := "define block templates in the preamble")
      return some (#[], k)
    write fun st => { st with
      beamerTemplateDefs := Ir.redeclare st.beamerTemplateDefs (element, name) body }
    if starred then installBlockTemplate element body pos
    became s!"\\defbeamertemplate\{{element}}\{{name}}" "a block template, read where the preamble ends" pos
    return some (#[], k)
  | "newbox" =>
    let j := skipSpaces raws start
    match raws[j]? with
    | some (.ctrl r _) =>
      discard s!"\\newbox\\{r}" "a box register's allocation sets nothing on the page" "newbox" pos
      return some (#[], j + 1)
    | _ => return none
  | "setbeamertemplate" =>
    -- `frame footer` is the one template with a native meaning: the per-frame footer note.
    let (args, j) := takeGroups raws start 1
    let element := (rawSrc (args.getD 0 #[])).trimAscii.toString
    if blockTemplateElement element then
      let (opt, j') := takeOpt raws j
      let (bodyArgs, k) := if opt.isSome then (#[], j') else takeGroups raws j' 1
      if (← get).inDoc then
        sayOnce ("beamer:template:" ++ element) .W0104
          s!"'\\setbeamertemplate\{{element}}' in the document body is skipped: \
only preamble block templates are read" pos
          (help := "set block templates in the preamble")
        return some (#[], k)
      match opt.map (·.trimAscii.toString), bodyArgs[0]? with
      | some name, _ =>
        match (← get).beamerTemplateDefs.find? (·.1 == (element, name)) with
        | some (_, body) =>
          installBlockTemplate element body pos
          -- premise: unreadTemplateChecks — with no document the flush names the template unread
          if (← get).wholeDoc then
            became s!"\\setbeamertemplate\{{element}}[{name}]" "a block template, read where the preamble ends" pos
        | none =>
          write fun st => { st with
            beamerTemplates := st.beamerTemplates.filter (·.1 != element)
            beamerBlockBegin := if element == "block begin" then #[] else st.beamerBlockBegin }
          if name != "default" then
            sayOnce ("beamer:template:" ++ element ++ ":" ++ name) .W0110
              s!"'\\setbeamertemplate\{{element}}[{name}]' names a template the document never \
defines; those blocks keep beamer's default template" pos
      | none, some body =>
        installBlockTemplate element (BlockTemplate.edged (bodyEdges raws j') body) pos
        -- premise: unreadTemplateChecks — with no document the flush names the template unread
        if (← get).wholeDoc then
          became s!"\\setbeamertemplate\{{element}}" "a block template, read where the preamble ends" pos
      | none, none => return none
      return some (#[], k)
    if element == "frame footer" then
      became "\\setbeamertemplate{frame footer}" "\\framefoot{...}" pos
      return some (Native.Head.framefoot.raws pos, j)
    else if let some native := beamerMarkerElement element then
      let (predefined, past) := takeOpt raws j
      if let some name := predefined then
        unreadParam "\\setbeamertemplate" element
          s!"'\\setbeamertemplate\{{element}}[{name.trimAscii.toString}]' predefined template" pos
        return some (#[], predefinedEnd raws past)
      let (bodyArgs, k) := takeGroups raws j 1
      if bodyArgs.size != 1 then return none
      let entries := #[("marker", Native.StyleValue.tex ((bodyArgs.getD 0 #[]).map (rebase (fun _ => pos) true)))]
      became s!"\\setbeamertemplate\{{element}}" (Native.texStyleRender native entries) pos
      return some (Native.texStyle native entries pos, k)
    -- premise: beamerTemplateChecks — footer content reaches the frame furniture
    else if element == "footline" &&
        (← get).wholeDoc && !(← get).inDoc && !(← get).inDef then
      let (rawVariant, _) := takeRawOpt raws j
      let (variant, k) := takeOpt raws j
      if let some name := variant then
        if ← paramArgs #[] #[rawVariant] then
          unappliedParam "setbeamertemplate" "beamer's template stands" pos
          return some (#[], predefinedEnd raws k)
        -- premise: defaultTemplateChecks — an unthemed deck draws each such default already
        if name.trimAscii.toString == "default" && (← get).beamerTheme.isEmpty then
          inertParam "\\setbeamertemplate" element s!"\\setbeamertemplate\{{element}}[default]"
            "beamer's default, which an unthemed deck draws already" pos
          return some (#[], predefinedEnd raws k)
        unreadParam "\\setbeamertemplate" element
          s!"'\\setbeamertemplate\{{element}}[{name.trimAscii.toString}]' predefined template" pos
        return some (#[], predefinedEnd raws k)
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
      let (rawPredefined, _) := takeRawOpt raws j
      let (predefined, j) := takeOpt raws j
      if let some name := predefined then
        if ← paramArgs #[] #[rawPredefined] then
          unappliedParam "setbeamertemplate" "beamer's template stands" pos
          return some (#[], predefinedEnd raws j)
        -- premise: defaultTemplateChecks — an unthemed deck draws each such default already
        if name.trimAscii.toString == "default" && (← get).beamerTheme.isEmpty &&
            defaultTemplates.contains element then
          inertParam "\\setbeamertemplate" element s!"\\setbeamertemplate\{{element}}[default]"
            "beamer's default, which an unthemed deck draws already" pos
          return some (#[], predefinedEnd raws j)
        unreadParam "\\setbeamertemplate" element
          s!"'\\setbeamertemplate\{{element}}[{name.trimAscii.toString}]' predefined template" pos
        return some (#[], predefinedEnd raws j)
      -- A title-page template of the overlay shape is read as the engine's own title page.
      let (bodyArgs, k) := takeGroups raws j 1
      let fonts := (← get).beamerFonts.toList.map fun (n, fields) =>
        (n, beamerTemplateFont n fields pos)
      match TitleTemplate.read fonts (bodyArgs.getD 0 #[]) with
      | some rd@{ mixed := some datum, .. } =>
        -- A datum beside literal text has no slot, so the built-in title page sets every datum.
        let (sfx, msg, help) := TitleTemplate.mixedLoss datum rd.ground.isSome
        sayOnce ("beamer:setbeamertemplate:title page:" ++ sfx) .W0363 msg pos (help := help)
        match rd.ground with
        | some ground => return some (← carry (.palette #[("titlepagebg", ground)]) pos, k)
        | none => return some (#[], k)
      | some rd =>
        let palette : Native.Setting := .palette (TitleTemplate.roles rd)
        -- premise: titleTemplateTextChecks — a body template's ground stands, its slots on no page
        if (← get).inDoc then
          let what := if palette.pairs.isEmpty then "is skipped" else "sets its ground alone"
          sayOnce "beamer:template:title page" .W0104
            s!"'\\setbeamertemplate\{title page}' in the document body {what}: only a preamble \
title-page template sets the title page" pos (help := "set the title-page template in the preamble")
          return some (← carry palette pos, k)
        -- premise: titleTemplateTextChecks — a template no document follows sets no title page
        unless (← get).wholeDoc do
          sayOnce "beamer:template:title page" .W0110
            "the title-page template is not read: no '\\begin{document}' ends a preamble for it; \
the built-in title page stands" pos
          return some (#[], k)
        -- A definition's template stands where its uses do, each walked in its place.
        if (← get).inDef then
          became "\\setbeamertemplate{title page}" "the title page where the definition is used" pos
          return some (← carry palette pos, k)
        -- premise: themeTitleShipChecks — a selected theme font's size reaches the page
        let skips := rd.fonts.map ("beamer:setbeamerfont:" ++ ·)
        write fun st => { st with diags := st.diags.filter fun d =>
          !(d.code == DiagCode.W0104.code && d.subject.any skips.contains) }
        became "\\setbeamertemplate{title page}"
          ((palette.note?.map (· ++ " and ")).getD "" ++ "the title page, one slot per node") pos
        unless rd.unread.isEmpty do
          sayOnce "beamer:setbeamertemplate:title page" .W0110
            s!"not read from the title-page template: \
{String.intercalate ", " rd.unread.toList}; the rest of it stands" pos
        for data in rd.unplaced do
          let (sfx, msg, help) := TitleTemplate.unplacedLoss data
          sayOnce ("beamer:setbeamertemplate:title page:" ++ sfx) .W0363 msg pos (help := help)
        for (construct, datum) in rd.skipped do
          let (sfx, msg) := TitleTemplate.skippedLoss construct datum
          sayOnce ("beamer:setbeamertemplate:title page:" ++ sfx) .W0104 msg pos
        let index := (← get).templates.size
        write fun st => { st with templates := st.templates.push (.titlePage rd st.file pos) }
        return some ((← carry palette pos) ++
          #[.ctrl titlePageMark pos, .group #[.word (toString index) pos] pos], k)
      | none =>
      -- `\setbeamertemplate{title page}` is beamer's spelling of `\renewcommand{\maketitle}`.
      let head := Native.Head.define "maketitle" ""
      became "\\setbeamertemplate{title page}" (head.render ++ " {...}") pos
      write fun st => { st with bodyNext := 1 }
      return some (head.raws pos, j)
    else
      let (rawPredefined, _) := takeRawOpt raws j
      let (predefined, j) := takeOpt raws j
      if let some name := predefined then
        if ← paramArgs #[] #[rawPredefined] then
          unappliedParam "setbeamertemplate" "beamer's template stands" pos
          return some (#[], predefinedEnd raws j)
        -- premise: defaultTemplateChecks — an unthemed deck draws each such default already
        if name.trimAscii.toString == "default" && (← get).beamerTheme.isEmpty &&
            defaultTemplates.contains element then
          inertParam "\\setbeamertemplate" element s!"\\setbeamertemplate\{{element}}[default]"
            "beamer's default, which an unthemed deck draws already" pos
          return some (#[], predefinedEnd raws j)
        unreadParam "\\setbeamertemplate" element
          s!"'\\setbeamertemplate\{{element}}[{name.trimAscii.toString}]' predefined template" pos
        return some (#[], predefinedEnd raws j)
      let (bodyArgs, k) := takeGroups raws j 1
      if ← paramArgs bodyArgs then
        unappliedParam "setbeamertemplate" "beamer's template stands" pos
        return some (#[], k)
      let emptyBody := bodyArgs.size == 1 && (rawSrc (bodyArgs.getD 0 #[])).trimAscii.toString.isEmpty
      -- premise: emptyTemplateMeasuredChecks — each noted template is measured empty, or never drawn
      if emptyBody && element == "navigation symbols" then
        inertParam "\\setbeamertemplate" element s!"\\setbeamertemplate\{{element}}\{}"
          "the engine draws no navigation symbols" pos
      else if emptyBody && emptyTemplates.contains element then
        inertParam "\\setbeamertemplate" element s!"\\setbeamertemplate\{{element}}\{}"
          s!"beamer's default {element} is empty, and the engine draws none" pos
      else if (rawSrc (bodyArgs.getD 0 #[])).trimAscii.toString.isEmpty then
        sayOnce ("param:\\setbeamertemplate:" ++ element) .W0104
          s!"'\\setbeamertemplate\{{element}}' is beamer configuration the engine does not have; \
skipped" pos
          (help := beamerNative.lookup "setbeamertemplate")
      else if insertsOwn element (rawSrc (bodyArgs.getD 0 #[])) then
        sayOnce ("param:\\setbeamertemplate:" ++ element) .W0104
          s!"'\\setbeamertemplate\{{element}}' prints only the {element}, without beamer's \
template around it; the engine's own {element} stands" pos
          (help := beamerNative.lookup "setbeamertemplate")
      else
        say .E0111
          s!"'\\setbeamertemplate\{{element}}' is dropped with its template body, which carries content" pos
          (help := ((beamerNative.lookup "setbeamertemplate").getD "") ++
            "; \\allow{E0111} accepts the loss")
      return some (#[], k)
  | "maketitle" =>
    -- premise: titlePageChecks — under an article's titlepage the title stands above the text
    if (← get).titlePageAsked && !(← get).inDef then
      sayOnce "partial:\\documentclass:titlepage:maketitle" .W0110
        "'\\maketitle' sets the title above the text, where class option 'titlepage' gives it a \
page of its own" pos (help := "\\begin{titlepage}...\\end{titlepage} sets a page of its own")
    return none
  | "setbeamercolor" =>
    -- A later parent declaration changes its children, so nothing is flattened here.
    let j := skipStar raws start
    let (args, k) := takeGroups raws j 2
    if h : args.size = 2 then
      let element := (rawSrc args[0]).trimAscii.toString
      became s!"\\setbeamercolor\{{element}}" "named colour declaration in \\palette" pos
      let marker := if j == skipSpaces raws start then BeamerColor.marker
        else BeamerColor.starMarker
      return some (#[.ctrl marker pos, .group args[0] pos, .group args[1] pos], k)
    else return none
  | "tikz" =>
    -- `\tikz` is the `tikzpicture` with that body.
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
  | "switchcolumn" =>
    -- premise: columnGeometryChecks — the flow consumes the switch as a column boundary
    if (← get).inParacol then return none
    let (_, j) := takeOpt raws start
    let js := skipSpaces raws j
    let starred := raws[js]? matches some (.word "*" _)
    let (_, k) := if starred then takeOpt raws (skipSpaces raws (js + 1)) else (none, j)
    sayOnce "paracol:switch-outside" .W0104
      "'\\switchcolumn' stands outside a supported two-column paracol flow; ignored" pos
    return some (#[], k)
  | "parbox" =>
    -- `\parbox` and `minipage` are the same box, so the width is honoured.
    let (_, j) := takeOpts raws start 3
    let (args, k) := takeGroups raws j 2
    became "\\parbox" "\\begin{minipage}{<width>}...\\end{minipage}" pos
    let widthGroup : Array Raw := #[.group (args[0]?.getD #[]) pos]
    return some (#[.env "minipage" (raws.extract start j ++ widthGroup ++ (args[1]?.getD #[])) pos], k)
  | "multicolumn" =>
    -- premise: multicolumnSpanChecks — the tabular arm sets what this keeps
    if (← get).tableTop || ((← get).defTop && skipSpaces raws 0 + 1 == start) then
      return none
    let (gs, k) := takeGroups raws start 2
    let j := skipSpaces raws k
    match gs, raws[j]? with
    | #[_, _], some (.group _ _) =>
      sayOnce "ctrl:multicolumn:misplaced" .W0337 multicolumnMisplaced pos
        (help := multicolumnMisplacedHelp)
      return some (#[], j)
    | _, _ => return none
  | _ =>
    -- `\begin{document}` runs `\normalsize`, so a preamble size command sets nothing kept.
    if (Ir.sizeScale.lookup name).isSome && (← docPreamble) then
      write fun st => { st with strutSkip := none }
      discard s!"\\{name}" "'\\begin{document}' runs '\\normalsize', which sets the size again"
        ("size:" ++ name) pos
      return some (#[], start)
    return none

private def rewriteCtrlLater (name : String) (pos : Pos) (raws : Array Raw)
    (start : Nat) : M (Option (Array Raw × Nat)) := do
  if let some result ← styOptionsRequest name pos raws start then return some result
  rewriteCtrlLaterNamed name pos raws start

/-- The dispatcher's silence guard: a consumed construct must have been paid for
by a diagnostic or a state write since `s0`. -/
private def account (name : String) (pos : Pos) (s0 : St) : M Unit := fun st =>
  if st.diags.size > s0.diags.size ∨ st.writes > s0.writes then ((), st)
  else if st.warned.contains ("silent:" ++ name) then
    ((), { st with writes := s0.writes + 1 })
  else
    ((), { st with
      warned := st.warned.push ("silent:" ++ name)
      diags := s0.diags.push (atSource st pos (Diag.of .W0387
        s!"'\\{name}' was read and had no effect" (some ⟨st.file, pos⟩)
        (help := "\\allow{W0387} accepts the skip")
        (subject := some ("ctrl:" ++ name)))) })

/-- The mark before a deck's `\appendix` under appendixnumberbeamer, where the
frame count starts over. -/
public def frameRestartMark : String := "appendix restart"

/-- The mark a cancel package load leaves in the preamble,
its option list in the group after it. -/
public def cancelOptionsMark : String := "cancel options"

/-- babel's language options beyond those whose locale ships, which a class option offers it. -/
private def babelLanguageNames : List String :=
  Locale.babelNames.map (·.1) ++
    ["spanish", "italian", "portuguese", "brazilian", "dutch", "polish", "russian", "swedish",
     "danish", "norsk", "nynorsk", "finnish", "catalan", "czech", "greek", "turkish", "ukrainian",
     "hungarian", "latin", "romanian", "croatian", "slovak", "slovene", "estonian", "icelandic",
     "irish", "welsh", "basque", "galician", "bulgarian", "serbian", "hebrew", "indonesian"]

/-- Whether package `p` declares option `o`, so takes it from the class's options as LaTeX offers
them. -/
public def packageTakes (p o : String) : Bool :=
  let spelled := optionSpelling o
  ((packageOptionNatives.lookup p).any (·.any (·.1 == spelled))) ||
    ((packageOptionsInert.lookup p).any (·.any (·.1 == spelled))) ||
    (p == "babel" && (KeyVal.entry o).2.isNone && babelLanguageNames.contains (KeyVal.entry o).1)

/-- The packages a preamble loads from index `start` on, in order. -/
private def preamblePackages (raws : Array Raw) (start : Nat) : Array String := Id.run do
  let mut out : Array String := #[]
  for i in [start:raws.size] do
    match raws[i]? with
    | some (.ctrl "usepackage" _) | some (.ctrl "RequirePackage" _) =>
      let (_, j) := takeOpt raws (i + 1)
      let (args, _) := takeGroups raws j 1
      for p in (rawSrc (args.getD 0 #[])).splitOn "," do
        let p := p.trimAscii.toString
        unless p.isEmpty || out.contains p do out := out.push p
    | _ => pure ()
  return out

/-- The class options a loaded package takes and the class leaves to it: every one but the draft and
final modes, which the class reads too. -/
private def offeredOptions (raws : Array Raw) (start : Nat) (opts : List String) : List String :=
  let pkgs := preamblePackages raws start
  opts.filter fun o =>
    let k := (KeyVal.entry o).1
    k != "draft" && k != "final" && pkgs.any (packageTakes · o)

/-- The options of a package the loading branch does not read: each a native declaration, machinery
the engine already answers, or a setting nothing reads. -/
private def packageOptions (name p : String) (opts : List String) (pos : Pos)
    (shown : String → String := id) : M (Array Raw) := do
  let mut out : Array Raw := #[]
  for o in opts do
    let spelled := optionSpelling o
    let key := (KeyVal.entry o).1
    let what := s!"\\{name}[{shown o}]\{{p}}"
    if p == "fontenc" && opts.getLast? == some o && glyphEncodings.contains spelled then
      unreadParam s!"usepackage:{p}" key s!"'fontenc' main encoding '{o}', which sets Latin input \
in its own script's glyphs," pos
    else if let some native := (packageOptionNatives.lookup p).bind (·.lookup spelled) then
      -- setspace's spacings set the strut box again as the package loads.
      if p == "setspace" then write fun st => { st with strutSkip := none }
      out := out ++ (← setting what native pos (subject := some (paramSubject s!"usepackage:{p}" key)))
    else if let some why := (packageOptionsInert.lookup p).bind fun rows =>
        (rows.lookup spelled).orElse fun _ =>
          if (KeyVal.entry o).2.isSome then rows.lookup (key ++ "=*") else none then
      inertParam s!"usepackage:{p}" key what why pos
    else unless key.isEmpty do
      unreadParam s!"usepackage:{p}" key s!"'{p}' option '{o}'" pos
  return out

/-- One package interpreted in the loading call's declared order. -/
private def rewritePackageBody (name p : String) (opt : Option String) (optRaws : Array Raw)
    (pos : Pos) : M (Array Raw) := do
  let mut out : Array Raw := #[]
  let own := (KeyVal.items (opt.getD "")).toList
  let offered := (← get).globalOffered.toList.filter fun o =>
    packageTakes p o && !own.any fun g => (KeyVal.entry g).1 == (KeyVal.entry o).1
  let given := offered ++ own
  if p == "geometry" then
    out := out ++ (← geometry optRaws pos)
  else if p == "crop" then
    out := out ++ (← crop (opt.getD "") pos)
  else if p == "colorspace" then
    colorspaceOptions (opt.getD "") pos
  else if p == "beamerposter" then
    out := out ++ (← beamerposter (opt.getD "") pos)
  else if p == "parskip" then
    -- The package sets `\parskip` to half a line plus 2pt, or to its `skip` as `\setlength` reads
    -- it, and drops the indent.
    -- No class option is offered to parskip but `indent`, so its own options hold its `skip`.
    let skip := ((Entries.read .keyval optRaws).filterMap fun e =>
      if e.key == "skip" then e.value else none).back?
    let read ← match skip with
      | some v => doorValue? (v.map (rebase (fun _ => pos) true))
      | none => pure none
    match skip, read with
    | some v, some src =>
      out := out ++ (← setLength "parskip" src s!"\\usepackage[skip={rawSrc v}]\{parskip}" pos)
    | _, _ =>
      out := out ++ (← setting "\\usepackage{parskip}" (.page #[(.parskip, "0.6em plus 2pt")]) pos)
      if let some v := skip then out := out ++ (← unreadableLength "parskip" (rawSrc v) pos)
    out := out ++ (← packageOptions name p (given.filter fun o => (KeyVal.entry o).1 != "skip") pos)
  else if p == "amsthm" then
    -- amsthm's documented default style is plain.
    let native := Native.Head.theoremStyle "plain"
    became "\\usepackage{amsthm}" native.render pos
    out := out ++ native.raws pos
    out := out ++ (← packageOptions name p given pos)
  else if (p == "caption" || p == "subcaption") && opt.isSome then
    -- The package options are `\captionsetup` keys, judged at that one site.
    let native := Native.Head.captionsetup none (opt.getD "")
    became s!"\\usepackage[{opt.getD ""}]\{{p}}" native.render pos
    out := out ++ native.raws pos
  else if p == "babel" then
    -- babel's `main` key, else its last language option, is the main one, which becomes metadata.
    let names := given.filter fun o => (KeyVal.entry o).2.isNone
    let declared := (given.filterMap fun o => match KeyVal.entry o with
      | ("main", some v) => some v
      | _ => none).getLast?
    let main? := declared.orElse fun _ => names.getLast?
    -- A further language is one the body may select, read where it does.
    for o in names do
      let k := (KeyVal.entry o).1
      if main? != some k then
        if (Locale.forTag (Locale.babelTagOf k)).isSome then
          inertParam "usepackage:babel" k s!"\\{name}[{k}]\{babel}"
            "the body may select the language, whose locale the engine ships" pos
        else
          inertParam "usepackage:babel" k s!"\\{name}[{k}]\{babel}"
            "the body may select the language, and where it does that site names the locale it lacks" pos
    out := out ++ (← packageOptions name p (given.filter fun o =>
      match KeyVal.entry o with
      | ("main", some _) => false
      | (_, none) => false
      | _ => true) pos)
    match main? with
    | some main =>
      let tag := Locale.babelTagOf main
      write fun st => { st with babelMain := some main }
      if (← get).biblatexLoaded then natbibDefer #[.set .mainlang main] pos
      if (Locale.forTag tag).isSome then
        write fun st => { st with mainLang := tag }
        out := out ++ (← setting s!"\\usepackage[{main}]\{babel}" (.pdfmeta #[(.language, Decl.quote tag)]) pos)
      else
        sayOnce ("param:usepackage:babel:" ++ main) .W0368 s!"no locale for language '{main}'; \
English captions and patterns stand in" pos
          (help := Locale.shippedHelp)
    | none =>
      discard s!"\\{name}\{{p}}" "the engine does this itself" s!"{name}:{p}" pos
  else if p == "natbib" then
    out := out ++ (← natbibLoad name (opt.getD "") pos)
  else if p == "biblatex" then
    biblatexLoad name (opt.getD "") pos
  else if let some spec := fontPackages.lookup p then
    -- carlito's `sfdefault` promotes its sans face to the body slot; every other option is named.
    let opts := (KeyVal.items (opt.getD "")).toList
    let sfdefault := p == "carlito" && opts.contains "sfdefault"
    let spec := if sfdefault then spec.push ("body", "Carlito") else spec
    let dropped := opts.filter (· != "sfdefault")
    for o in dropped do
      unreadParam s!"usepackage:{p}" (KeyVal.entry o).1 s!"'{p}' option '{o}'" pos
    out := out ++ (← setting s!"\\usepackage\{{p}}" (.fonts (spec.map fun (k, f) => (k, Decl.quote f))) pos)
  else if p == "lineno" && opt.isSome then
    out := out ++ (← linenoLoad (opt.getD "") pos)
  else if p == "cancel" then
    -- The package's options are the marks' own settings, carried to the elaborator's preamble.
    let opts := (KeyVal.items (opt.getD "")).toList
    let (_, unknown) := Math.CancelSpec.ofOptions opts
    for o in unknown do
      unreadParam "usepackage:cancel" (KeyVal.entry o).1 s!"'cancel' option '{o}'" pos
    became s!"\\usepackage\{cancel}"
      "the cancel marks, drawn from the math font's own rule constants" pos
    out := (out.push (.ctrl cancelOptionsMark pos)).push
      (.group (if opts.isEmpty then #[] else #[.word (String.intercalate "," opts) pos]) pos)
  else if p == "animate" then
    -- premise: animatedGraphicsChecks — local posters select distinct shipped images
    let opts := (opt.getD "").trimAscii.toString
    if opts.isEmpty then
      discard s!"\\{name}\{{p}}"
        "whole multipage animations are read at each '\\animategraphics' command"
        s!"{name}:{p}" pos
    else
      for o in KeyVal.items opts do
        sayOnce ("param:usepackage:animate:" ++ (KeyVal.entry o).1) .W0110
          s!"'animate' package option '{o}' is not applied" pos
          (help := "put poster and size options on each '\\animategraphics'; playback settings remain unsupported")
  else if p == "markdown" then
    -- premise: markdownInputChecks — the driver reads native fragments
    -- premise: markdownHybridChecks — the driver reads citations and hybrid where the package does
    let others := (MarkdownOptions.read (opt.getD "")).others
    if others.isEmpty then
      discard s!"\\{name}\{{p}}"
        "native Markdown fragments are read at each '\\markdownInput' command"
        s!"{name}:{p}" pos
    else
      for o in others do
        sayOnce ("param:usepackage:markdown:" ++ (KeyVal.entry o).1) .W0110
          s!"'markdown' package option '{o}' is not applied; \
the Markdown document dialect reads only 'citations' and 'hybrid'" pos
          (help := "remove the package options")
  else if p == "unicode-math" && opt.isSome then
    out := out ++ (← unicodeMathOptions
      s!"\\{name}[{opt.getD ""}]\{unicode-math}" (opt.getD "") pos)
  else if p == "hyperref" && opt.isSome then
    -- hyperref's package options are `\hypersetup`'s keys.
    let r ← hyperrefKeys optRaws pos
    if r.metadata.isEmpty && r.words.isEmpty && !r.linked then
      discard s!"\\{name}\{{p}}" "the engine does this itself" s!"{name}:{p}" pos
    else
      out := out ++ (← hyperrefLowered s!"\\usepackage[{opt.getD ""}]\{hyperref}"
        s!"{name}:{p}" r pos)
  else if p == "ulem" then
    if given.contains "normalem" then
      discard s!"\\{name}[normalem]\{{p}}"
        "strikeout is native and normal emphasis remains in force"
        s!"{name}:{p}:normalem" pos
      out := out ++ (← packageOptions name p (given.filter (· != "normalem")) pos)
    else
      say .W0103 "package 'ulem' without only the 'normalem' option changes \\emph; skipped"
        pos (help := "use \\usepackage[normalem]{ulem} for native \\sout")
        (refused := some p)
  -- premise: tableFaceOrderChecks — the face before or after the load ships identical pages
  else if p == "booktabs" && (← get).facesDeclared.contains
      (if (← get).deck then "sans" else "body") then
    -- booktabs fixes its rule weights in the font current where it loads.
    let (face, cmd) := if (← get).deck then ("sans", "\\setsansfont")
      else ("main", "\\setmainfont")
    say .W0398 s!"'\\{name}\{booktabs}' follows the {face} face's declaration; \
its rule paddings are measured in Latin Modern" pos
      (help := some s!"load booktabs before '{cmd}', where LaTeX measures them in Latin Modern too")
      (subject := some "package:booktabs")
    out := out ++ (← packageOptions name p given pos)
  else if p == "blueprint" then
    -- Its options draw its web page's graph and proof buttons, and `link` its names' links.
    let opts := (KeyVal.items (opt.getD "")).map KeyVal.entry
    let showmore := opts.any (·.1 == "showmore")
    blueprintGraph pos (if showmore then
      some "'showmore' asks for buttons showing or hiding every proof, which are not drawn either"
      else none)
    let link := opts.findSome? fun (k, v) => if k == "link" then v.map urlOption else none
    out := blueprintSiteRaws "package" "" pos ++
      (match link with
       | some l => blueprintSiteRaws "link" l pos
       | none => #[])
    out := out ++ (← packageOptions name p (given.filter fun o =>
      !["showmore", "link"].contains (KeyVal.entry o).1) pos)
  else if p == "inputenc" && Encoding.declaresNonUtf8 (opt.getD "") then
    -- premise: inputDecodingChecks — the driver's one note names each governed file
    recordInputenc (opt.getD "")
  else if nativePackages.contains p then
    if p == "inputenc" then recordInputenc (opt.getD "")
    discard s!"\\{name}\{{p}}" "the engine does this itself" s!"{name}:{p}" pos
    -- microtype's `disable=ifdraft` disables its features when `draft` stands before it, the class's included.
    let classDraft := ((← get).loads.cls.map fun (_, os) => os.any (optionSpelling · == "draft")).getD false
    let read := if p == "microtype" then
        (given.foldl (init := (classDraft, #[])) fun (draft, acc) o =>
          let sp := optionSpelling o
          if sp == "draft" then (true, acc.push (o, o))
          else if sp == "disable=ifdraft" && draft then (draft, acc.push ("disable", o))
          else (draft, acc.push (o, o))).2.toList
      else given.map fun o => (o, o)
    out := out ++ (← packageOptions name p (read.map (·.1)) pos
      (shown := fun o => ((read.find? (·.1 == o)).map (·.2)).getD o))
  else if boundaryPkgs.contains p && (← get).boundaryOpen then
    -- A picture package's load belongs to the boundary standalone.
    became s!"\\{name}\{{p}}"
      "the boundary standalone's preamble; each picture outside the \
rendered subset is drawn whole at the boundary" pos
  else if let some (slot, _, nm) := themeSlotOfPackage? p then
    -- A `beamerthemeX` package is `\usetheme{X}`.
    if slot == "usetheme" then
      let nm := themeAlias nm
      let native := Native.Head.theme nm
      became s!"\\{name}\{{p}}" native.render pos
      write fun st => { st with themeNamed := true }
      if (Theme.find? nm).isSome then
        write fun st => { st with themed := true }
      out := out ++ native.raws pos ++ (← themeOptions s!"\\{name}\{{p}}" s!"\\{name}\{{p}}" nm (opt.getD "") pos)
    else
      -- The four sub-theme slots have no bundle of their own here.
      sayOnce ("beamer:" ++ slot) .W0104
        s!"'\\{slot}' is beamer configuration the engine does not have; skipped" pos
        (help := (beamerNative.lookup slot).getD
          "a theme is a token bundle here: \\theme selects one, and \\palette \
and \\tokens declare the design directly")
  else
    say .W0103 s!"package '{p}' is not supported; skipped" pos
      (refused := some p)
  return out

/-- Admits a native package before installing its defaults. -/
private def rewritePackage (name p : String) (opt : Option String) (optRaws : Array Raw)
    (pos : Pos) : M (Array Raw) := do
  if nativePackages.contains p then
    let passedItems := (← get).loads.rewritePassed.toList.flatMap fun (q, os) =>
      if q == p then os.toList else []
    let passed := passedItems.map (·.1)
    let some options ← admitPackage p (PackageImports.literalOptions (opt.getD "")) passed pos
      | return #[]
    let opt := if passed.isEmpty then opt else some (String.intercalate "," options)
    -- The passed options before the load's own, as `options` spells them.
    let optRaws := if passed.isEmpty then optRaws else
      (passedItems.map (·.2) ++ ((Entries.read .keyval optRaws).map (·.item)).toList).foldl
        (init := #[]) fun acc item => if acc.isEmpty then item else (acc.push (.word "," pos)) ++ item
    rewritePackageBody name p opt optRaws pos
  else
    rewritePackageBody name p opt optRaws pos

private theorem rewritePackage_compatible_exact (name p : String) (opt : Option String)
    (optRaws : Array Raw) (pos : Pos) (st : St) (first : List String)
    (native : nativePackages.contains p = true)
    (loaded : st.loads.imports.lookup p = some first)
    (compatible : ∀ o ∈ PackageImports.literalOptions (opt.getD ""),
      o ∈ first ++ (st.loads.rewritePassed.toList.flatMap
        (fun (q, os) => if q == p then os.toList else [])).map (·.1)) :
    rewritePackage name p opt optRaws pos st = (#[], { st with writes := st.writes + 1 }) := by
  simp only [rewritePackage, native, ↓reduceIte, bind, StateT.bind,
    get, getThe, MonadStateOf.get, StateT.get, pure]
  rw [admitPackage_compatible_exact _ _ _ _ _ _ loaded compatible]
  rfl

/-- The external-package refusal's whole record, before the
source index adds its trigger. -/
public def packageRefusal (file : String) (pos : Pos) (p : String) : Diag :=
  Diag.of .W0103 s!"package '{p}' is not supported; skipped"
    (some ⟨file, pos⟩) (refused := some p)

private theorem atSource_package_exact (st : St) (pos : Pos) (p : String) :
    atSource st pos (packageRefusal st.file pos p) =
      st.sourceTriggers.attribute (packageRefusal st.file pos p) := by
  simp [atSource, SourceTriggers.atSource, SourceTriggers.attribute,
    packageRefusal, Diag.of_record_exact]

private theorem rewritePackage_external_exact (name p : String)
    (opt : Option String) (optRaws : Array Raw) (pos : Pos) (st : St)
    (hn : nativePackages.contains p = false)
    (hb : (boundaryPkgs.contains p && st.boundaryOpen) = false)
    (ht : themeSlotOfPackage? p = none) :
    rewritePackage name p opt optRaws pos st =
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

/-- The package-loading arm's loop, judging each name of one
operand in order. -/
private def rewritePackages (name : String) (pkgs : List String)
    (opt : Option String) (optRaws : Array Raw) (pos : Pos) : M (Array Raw) := do
  let mut out : Array Raw := #[]
  for p in pkgs do
    out := out ++ (← rewritePackage name p opt optRaws pos)
  return out

private theorem rewritePackages_external_exact (name : String)
    (pkgs : List String) (opt : Option String) (optRaws : Array Raw) (pos : Pos) (st : St)
    (hn : ∀ p ∈ pkgs, nativePackages.contains p = false)
    (hb : ∀ p ∈ pkgs, (boundaryPkgs.contains p && st.boundaryOpen) = false)
    (ht : ∀ p ∈ pkgs, themeSlotOfPackage? p = none) :
    rewritePackages name pkgs opt optRaws pos st =
      (#[], { st with diags := st.diags ++
        (pkgs.map fun p => atSource st pos (packageRefusal st.file pos p)).toArray }) := by
  have loop :
      ∀ (xs : List String) (out : Array Raw) (s : St),
        (∀ p ∈ xs, nativePackages.contains p = false) →
        (∀ p ∈ xs, (boundaryPkgs.contains p && s.boundaryOpen) = false) →
        (∀ p ∈ xs, themeSlotOfPackage? p = none) →
        ((forIn xs out fun p acc => do
          let repl ← rewritePackage name p opt optRaws pos
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
        rewritePackage_external_exact name p opt optRaws pos s
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

/-- Named arms after the dispatcher's state-dependent guards. -/
private def rewriteCtrlNamed (name : String) (pos : Pos) (raws : Array Raw)
    (start : Nat) : M (Option (Array Raw × Nat)) := do
  match name with
  | "documentclass" =>
    let (opt, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    let cls := rawSrc (args.getD 0 #[])
    -- A package takes the class options it declares, and the class reads the rest.
    let offered := offeredOptions raws k (KeyVal.items (opt.getD "")).toList
    unless offered.isEmpty do write fun st => { st with globalOffered := offered.toArray }
    let keptItems := (KeyVal.items (opt.getD "")).toList.filter (!offered.contains ·)
    -- The class's `\normalsize` sets the strut box at its `\baselineskip` as the class loads.
    let strut := (classNormalPt cls keptItems).map classNormalSkip
    write fun st => { st with strutSkip := strut }
    if cls == "article" && asksTitlePage keptItems then
      write fun st => { st with titlePageAsked := true }
    if presentationClasses.contains cls then
      write fun st => { st with deck := true }
    let native := if articleClasses.contains cls then "article"
      else if resumeClasses.contains cls then "resume"
      else if cls == "beamer" then "slides" else cls
    let flow := ((Ir.DocClass.ofString? native).map (·.record.model == .flow)).getD true
    write fun st => { st with
      measureKnown := !flow, flowPage := flow,
      titlepageReset := !(KeyVal.items (opt.getD "")).any fun o =>
        KeyVal.entry o matches ("twoside", none) | ("twoside", some "true") }
    if articleClasses.contains cls || resumeClasses.contains cls then
      let native0 := if resumeClasses.contains cls then "resume" else "article"
      -- A title-page option passed to the class is its own; report.cls and book.cls default to
      -- `titlepage`, where the abstract is no quotation.
      let titleOpts := ["titlepage", "notitlepage"]
      let passed := (← get).loads.rewriteClassPassed.toList.flatMap fun (name, options) =>
        if name == cls then options.toList.filter titleOpts.contains else []
      let given := (KeyVal.items (opt.getD "")).any titleOpts.contains || !passed.isEmpty
      let extra := passed ++ (if titlepageClasses.contains cls && !given then ["titlepage"] else [])
      let opt := if extra.isEmpty then opt else some (",".intercalate (opt.toList ++ extra))
      -- KOMA's `parskip` is read here.
      let kept := (keptItems ++ extra).filter fun kv => (KeyVal.entry kv).1 != "parskip"
      -- A class's `\parskip` is zero unless KOMA's `parskip=` asks for a skip.
      let komaSkip := (KeyVal.items (opt.getD "")).findSome? fun kv =>
        match KeyVal.entry kv with
        | ("parskip", some v) =>
          if v.startsWith "full" then some "1.2em plus 0.24em"
          else if v.startsWith "half" then some "0.6em plus 0.12em"
          else if v == "false" || v == "never" then some "0pt"
          else some "0.6em plus 0.12em"
        | ("parskip", none) => some "1.2em plus 0.24em"
        | _ => none
      let cls0 := Native.Head.documentclass kept.toArray native0
      let page : Native.Setting := .page #[(.parskip, komaSkip.getD "0pt")]
      became s!"\\documentclass\{{cls}}" (cls0.render ++ (page.note?.getD "")) pos
      return some (cls0.raws pos ++ (← carry page pos), k)
    else if cls == "beamer" then
      let declaration := Native.Head.documentclass (if opt.isSome then keptItems.toArray else #[])
        "slides"
      became "\\documentclass{beamer}" declaration.render pos
      let passed := (← get).loads.rewriteClassPassed.toList.flatMap fun (name, options) =>
        if name == cls then options.toList else []
      let packages := classPackages cls (passed ++ PackageImports.literalOptions (opt.getD ""))
      let dependencies ← rewritePackages "RequirePackage" packages none #[] pos
      return some (declaration.raws pos ++ dependencies, k)
    else
      -- The options passed to a class before it loads are its own, before its written ones.
      let passed := (← get).loads.rewriteClassPassed.toList.flatMap fun (name, options) =>
        if name == cls then options.toList.filter (!keptItems.contains ·) else []
      if offered.isEmpty && passed.isEmpty then return none
      let kept := passed ++ keptItems
      let native := Native.Head.documentclass kept.toArray cls
      became s!"\\documentclass[{opt.getD ""}]\{{cls}}" native.render pos
      return some (native.raws pos, k)
  | "babelfont" | "setmainfont" | "setsansfont" | "setmonofont"
  | "newfontfamily" | "setfontfamily" | "renewfontfamily" | "providefontfamily"
  | "newfontface" | "setfontface" | "renewfontface" | "providefontface" =>
    -- `\babelfont` binds a font per language, which is dropped by name (W0369).
    let declared : Option String :=
      if name.endsWith "fontfamily" || name.endsWith "fontface" then
        match raws[skipSpaces raws start]? with
        | some (.ctrl c _) => some c
        | some (.group g _) => match g.toList.filter (· != .space) with
          | [.ctrl c _] => some c
          | _ => none
        | _ => none
      else none
    if (name.endsWith "fontfamily" || name.endsWith "fontface") && declared.isNone then return none
    let start := if declared.isSome then skipSpaces raws start + 1 else start
    let (langRaws, j0) := if name == "babelfont" then takeRawOpt raws start else (none, start)
    let (slotArgs, j) := if name == "babelfont" then takeGroups raws j0 1 else (#[], start)
    let (beforeRaws, j) := takeRawOpt raws j
    let (args, k) := takeGroups raws j 1
    let (afterRaws, k) := takeRawOpt raws k
    if ← paramArgs (slotArgs ++ args) #[langRaws, beforeRaws, afterRaws] then
      unappliedParam name "the face in force stands" pos
      return some (#[], k)
    let (langOpt, optBefore, optAfter) :=
      (langRaws.map rawSrc, beforeRaws.map rawSrc, afterRaws.map rawSrc)
    let st0 ← get
    let defined := match declared with
      | some c => st0.bound.contains c || st0.fontFamilies.contains c
      | none => false
    if let some c := declared then
      write fun st => { st with bound := if st.bound.contains c then st.bound else st.bound.push c }
    -- The provide forms define the command only where it is undefined.
    if name.startsWith "provide" && defined then
      let c := declared.getD ""
      discard s!"\\{name}\\{c}" s!"'\\{c}' is already defined, and the provide form keeps it"
        s!"{name}:{c}" pos
      return some (#[], k)
    -- premise: bodyFamilyChecks — a body declaration declares no family
    if (← get).inDoc then
      if let some c := declared then
        sayOnce ("ctrl:" ++ name) .W0340
          (Diag.bodyDeclaration name ++ s!", and '\\{c}' selects no family") pos
          (help := Diag.declareInPreamble)
        return some ((Native.Head.define c "").raws pos ++ #[.space, Raw.group #[] pos], k)
    let slot := match name, declared with
      | _, some c => "family." ++ c
      | "babelfont", _ => match rawSrc (slotArgs.getD 0 #[]) with
        | "rm" => "body" | "sf" => "sans" | "tt" => "mono" | s => s
      | "setmainfont", _ => "body" | "setsansfont", _ => "sans" | _, _ => "mono"
    let family := rawSrc (args.getD 0 #[])
    -- Only fontspec features that name fonts are kept; shaping features are dropped.
    let feature (k : String) : Option String :=
      ([optBefore, optAfter].filterMap id).findSome? fun opts =>
        (KeyVal.items opts).findSome? fun kv =>
          match KeyVal.entry kv with
          | (key, some v) => if key == k then some v else none
          | (_, none) => none
    let mut parts : Array (String × String) :=
      ((feature "Path").map fun d => #[("dir", Decl.quote d)]).getD #[] |>.push (slot, Decl.quote family)
    if name.endsWith "fontface" then
      for variant in ["bold", "italic", "bolditalic"] do
        parts := parts.push (s!"{slot}.{variant}", Decl.quote family)
    for (opt, variant) in [("UprightFont", "upright"), ("BoldFont", "bold"),
        ("ItalicFont", "italic"), ("BoldItalicFont", "bolditalic")] do
      if let some f := feature opt then
        -- fontspec's `*` stands for the family name.
        let f := if f.startsWith "*" then family ++ (f.drop 1).toString else f
        parts := parts.push (s!"{slot}.{variant}", Decl.quote f)
    for opts in [optBefore, optAfter].filterMap id do
      for kv in KeyVal.items opts do
        if let ("FontFace", some v) := KeyVal.entry kv then
          if let some part := ← fontFacePart family slot v pos then
            parts := parts.push part
    if name == "babelfont" then
      if let some l := langOpt then
        say .W0369 s!"'\\babelfont[{l}]' binds a font per language; one \
face serves every language, so the binding is dropped" pos
          (help := "\\fonts{ body = \"...\" } names the face every language uses")
        return some (#[], k)
    let fonts ← setting s!"\\{name}" (.fonts parts) pos
    write fun st => { st with facesDeclared := st.facesDeclared.push slot }
    match declared with
    | none => return some (fonts, k)
    | some c =>
      -- The command selects its family's slot as a declaration scoping the rest of its group.
      let st ← get
      let slot := Ir.familySlotBase + ((st.fontFamilies.findIdx? (· == c)).getD st.fontFamilies.size)
      unless st.fontFamilies.contains c do
        write fun st => { st with fontFamilies := st.fontFamilies.push c }
      let switch := (Native.Head.define c "").raws pos ++
        #[.space, Raw.group #[Raw.ctrl (Marker.name .family (toString slot)) pos] pos]
      return some (fonts ++ switch, k)
  | "definespotcolor" => defineSpotColor raws start pos
  | "pdfvariable" | "pdfpageattr" =>
    let some k := pageAttrEnd raws (start - 1) | return none
    let st ← get
    let look (n : String) : Option (Array Raw) := match st.binds[n]? with
      | some (some v) => if v.arity == 0 then some v.raws else none
      | _ => none
    let some (text, keep) := pageAttrText look (raws.extract (start - 1) k) | return none
    pageAttrBoxes text keep s!"\\{name} pageattr" pos
    return some (#[], k)
  | "setlength" =>
    let (args, k) := takeGroups raws start 2
    if h : args.size = 2 then
      if ← paramArgs args then
        unappliedParam "setlength" "the length keeps its value" pos
        return some (#[], k)
      -- e-TeX's `\dimexpr` division rounds where the native language truncates, so it is refused.
      if (args[1].any fun r => match r with | .ctrl "dimexpr" _ => true | _ => false)
          && (lengthSrc args[1]).toList.contains '/' then
        say .E0375 "'\\dimexpr' division rounds to nearest; this engine's length \
arithmetic truncates toward zero as TeX's '\\divide' does" pos
          (help := "divide outside '\\dimexpr': '(\\a - \\b) / 2' truncates as TeX does")
        return some (#[], k)
      match paramName args[0] with
      | some n =>
        let target := (rawSrc args[0]).trimAscii.toString
        -- premise: capitalRegisterChecks — a template register read is refused by name
        if (← get).allocated.contains n then
          discard s!"\\setlength\{{target}}" "a register only the block templates assign and read"
            s!"setlength:{n}" pos
          return some (#[], k)
        return some (← assignLength n args[1] s!"\\setlength\{{target}}" pos (noted := true), k)
      | none => return none
    else return none
  | "addtolength" =>
    -- `\addtolength` sums the held value and the operand where both are known.
    let (args, k) := takeGroups raws start 2
    if h : args.size = 2 then
      if ← paramArgs args then
        unappliedParam "addtolength" "the length keeps its value" pos
        return some (#[], k)
      let some n := ctrlName args[0] | return none
      let st ← get
      -- premise: registerArithChecks — a length this rewrite set holds its recorded value
      match (st.lens.find? (·.1 == n)).map (·.2),
          lenOperand st.lens (args[1].toList.filter (!· matches .space)) with
      | some p, some v =>
        -- premise: composedLengthChecks — a readable sum is the declaration's value
        let expr := s!"({p}) + {v}"
        if Decl.readsAsLengthExpr expr then
          return some (← setLength n expr s!"\\addtolength\{\\{n}}" pos, k)
        sayOnce ("length:" ++ n) .W0107
          s!"'\\addtolength' on a value the length grammar cannot compose ('{expr}'): \
skipped, and the length keeps its value" pos
          (demote := styInternal (← get).file name)
        return some (#[], k)
      | _, _ =>
        -- In a definition's body the command stands, for the use to read.
        if (← get).inDef then return none
        return some (← unreadableLength n
          s!"\\{n} + {(rawSrc args[1]).trimAscii.toString}" pos, k)
    else return none
  | "advance" | "multiply" | "divide" =>
    -- TeX's register arithmetic is named and skipped whole, its `by` and value included.
    let j0 := skipSpaces raws start
    match raws[j0]? with
    | some (.ctrl _ _) =>
      let j1 := skipSpaces raws (j0 + 1)
      let j2 := match raws[j1]? with
        | some (.word "by" _) => skipSpaces raws (j1 + 1)
        | _ => j1
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
      let tgt := match raws[j0]? with
        | some (.ctrl t _) => t
        | _ => ""
      let st ← get
      let opnd := (raws.extract j2 k).toList.filter (!· matches .space)
      let value := if name == "advance" then lenOperand st.lens opnd
        else match opnd with
          | [.word w _] => w.toNat?.map toString
          | _ => none
      -- premise: registerArithChecks — a length this rewrite set holds its recorded value
      let expr? := match (st.lens.find? (·.1 == tgt)).map (·.2), value with
        | some p, some v => some (if name == "advance" then s!"({p}) + {v}"
            else if name == "multiply" then s!"{v} * ({p})" else s!"({p}) / {v}")
        | _, _ => none
      match expr? with
      | some expr =>
        if Decl.readsAsLengthExpr expr then
          return some (← setLength tgt expr s!"\\{name}\\{tgt}" pos, k)
        sayOnce ("length:" ++ tgt) .W0107
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
    -- One arm for the whole definer family; only `provide` keeps an existing definition.
    let xparse := name.endsWith "DocumentCommand"
    let start := skipStar raws start
    let (nameArgs, j) := takeGroups raws start 1
    let some cmd := ctrlName (nameArgs.getD 0 #[]) | return none
    -- A stretch the next font selection reads sets the strut box again there.
    if cmd == "baselinestretch" then write fun st => { st with strutSkip := none }
    let provide := Definer.provides name
    let st ← get
    -- premise: Tests.xparseProvideChecks — provision keeps existing meanings
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
    if let some why := macroParams.lookup cmd then
      if !xparse then
        let (_, j) := takeOpt raws j
        let (_, j) := takeOpt raws j
        let (_, k) := takeGroups raws j 1
        nameParam cmd why pos
        return some (#[], k)
    -- premise: biblatexPunctChecks — the delimiters read set the citations biber sets
    if !xparse && st.biblatexLoaded && biblatexMacros.contains cmd then
      let (_, j) := takeOpt raws j
      let (_, j) := takeOpt raws j
      let (args, k) := takeGroups raws j 1
      return some (← biblatexMacroDef name cmd (args.getD 0 #[]) pos, k)
    if !xparse && cmd == "sectionlinesformat" then
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
    -- A body that is one `\@startsection` call is read as `\style` over the heading.
    let js := skipSpaces raws j
    if let some (.group sbody _) := raws[js]? then
      if let some out ← startSection? cmd sbody pos then
        return some (out, js + 1)
      if let some level := listLevelOf cmd then
        if !xparse && (← docPreamble) then
          if ← listLevelDef level s!"\\{name}\{\\{cmd}}" sbody pos then
            return some (#[], js + 1)
    -- A `\renewcommand\normalsize` opening with `\@setfontsize` declares the body size and leading.
    if !xparse && cmd == "normalsize" then
      if let some (.group sbody _) := raws[js]? then
        let b := skipSpaces sbody 0
        if let some (.ctrl "@setfontsize" _) := sbody[b]? then
          let (fsArgs, afterFs) := takeGroups sbody (b + 1) 3
          if h : fsArgs.size ≥ 3 then
            if let (some sz, some ld) := (ptMacroArg fsArgs[1], ptMacroArg fsArgs[2]) then
              if sz > 0 && ld > 0 then
                let skips ← sizeSkips sbody afterFs pos
                let page : Native.Setting :=
                  .page #[(.fontsize, s!"{milliStr sz}pt"), (.baselineskip, s!"{milliStr ld}pt")]
                let tokens : Native.Setting := .tokens skips
                write fun st => { st with listiKept := !resetsListi sbody }
                became "\\renewcommand{\\normalsize}"
                  ((page.note?.getD "") ++ (tokens.note?.getD "")) pos
                return some ((← carry page pos) ++ (← carry tokens pos), js + 1)
    let native := Native.Head.define cmd spec
    -- premise: ignoredDefinitionChecks — an ignored built-in's refusal is its one accounting
    unless st.ignoredDefs.contains cmd do
      write fun st => { st with
        bound := if st.bound.contains cmd then st.bound else st.bound.push cmd }
      became s!"\\{name}\{\\{cmd}}" (native.render ++ " {...}") pos
    write fun st => { st with bodyNext := 1, quietNext := st.templateCode.contains cmd }
    return some (native.raws pos, j)
  | _ => rewriteCtrlLater name pos raws start

private def lowerBeamerFont (c : CtrlCall) : M (Array Raw) := do
  let pos := c.pos
  let starred := (c.given 0).isSome
  let element := (c.src 1).trimAscii.toString
  let source := c.arg 2
  let stored := (← get).beamerFonts.toList.lookup element |>.getD
    (themeBlockFont (← get).beamerTheme element pos)
  let previous := if starred then [] else stored
  let fields := beamerFontUpdate previous source
  unless element == "normal text" do
    write fun st => { st with
      beamerFonts := Ir.redeclare st.beamerFonts element fields
      beamerCaptures := st.beamerCaptures + 1 }
  match beamerFontElements.lookup element with
  | none =>
    if element == "normal text" then
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
    return #[]
  | some (target, styleKey) =>
    let updates := beamerFontUpdate [] source
    for (key, value) in updates do
      if key == "parent" then
        sayOnce ("beamer:setbeamerfont:" ++ element ++ ":" ++ key) .W0104
          (if target.endsWith "block" then
            s!"'\\setbeamerfont\{{element}}' names its parents with '{key}'; the \
engine's alerted and example block titles inherit the plain block title's font, and nothing \
else, so only declared commands are taken"
          else s!"'\\setbeamerfont\{{element}}' inherits with '{key}'; the engine has \
no font inheritance, so only declared commands are taken") pos
          (help := beamerNative.lookup "setbeamerfont")
      else if key == "size*" && (rawGroups value).size != 2 then
        sayOnce ("beamer:setbeamerfont:" ++ element ++ ":" ++ key) .W0104
          s!"'\\setbeamerfont\{{element}}' needs two braced dimensions for 'size*'; \
its value is skipped" pos
          (help := "write size*={font size}{baseline distance}")
      else if !beamerFontKeys.contains (beamerFontAxis key) then
        sayOnce ("beamer:setbeamerfont:" ++ element ++ ":" ++ key) .W0104
          s!"'\\setbeamerfont\{{element}}' key '{key}' is not a beamer font key; \
its value is skipped" pos
          (help := beamerNative.lookup "setbeamerfont")
    -- premise: beamerTemplateChecks — an empty declared field clears that field
    if starred || updates.any (fun e => beamerFontKeys.contains (beamerFontAxis e.1)) then
      -- premise: beamerTemplateChecks — no native style escapes its scope
      let written := s!"\\setbeamerfont{if starred then "*" else ""}\{{element}}"
      if !(← get).inDoc && ((← get).inGroup || !(← get).beamerScopes.isEmpty) then
        became written "local font fields" pos
        return #[]
      let cmds := beamerFontCommands (blockTitleFields element fields pos) pos
      let alerted := "block title alerted"
      let seed := themeBlockFont (← get).beamerTheme alerted pos
      let own := if target == "block" && !seed.isEmpty &&
          ((← get).beamerFonts.toList.lookup alerted).isNone then
        #[("alertblock", #[("font", Native.StyleValue.tex (beamerFontCommands seed pos))])] else #[]
      unless own.isEmpty do
        write fun st => { st with beamerFonts := st.beamerFonts.push (alerted, seed) }
      let styles := #[(target, #[(styleKey, Native.StyleValue.tex cmds)])] ++ own
      became written (" ".intercalate (styles.toList.map fun (el, es) => Native.texStyleRender el es)) pos
      return styles.foldl (init := #[]) fun out (el, es) =>
        let style := Native.texStyle el es pos
        out ++ style
    else return #[]

private def lowerSetList (c : CtrlCall) : M (Array Raw) := do
  let pos := c.pos
  let star := (c.given 0).isSome
  let scope := ((c.optSrc 1).getD "").trimAscii.toString
  let what := s!"\\setlist{if star then "*" else ""}{bracketed scope}"
  let (kinds, levels) := setlistScope scope
  let kindsIn : List (Option String) :=
    if kinds.isEmpty then [none] else (kinds.filter setlistKinds.contains).map some
  let levelsIn : List (Option Nat) :=
    if levels.isEmpty then [none] else (levels.filter fun l => 2 ≤ l && l ≤ 4).map some
  let scopes := kindsIn.flatMap fun kd => levelsIn.map fun l => (kd, l)
  -- The vertical keys' scopes are enumitem's own, each kind and level its element.
  let vKindsIn : List (Option String) :=
    if kinds.isEmpty then [none] else (kinds.filter Ir.listSetKinds.contains).map some
  let vLevelsIn : List (Option Nat) :=
    if levels.isEmpty then [none] else (levels.filter fun l => 1 ≤ l && l ≤ 4).map some
  let vScopes := vKindsIn.flatMap fun kd => vLevelsIn.map fun l => (kd, l)
  let items := Entries.read .keyval (c.arg 2)
  let mut vertical : Array (String × String) := #[]
  let mut styled : Array Entries.Entry := #[]
  for e in items do
    match ← listSpacingEntries what "\\setlist" e pos with
    | some vs => for (key, v) in vs do vertical := Ir.redeclare vertical key v
    | none => styled := styled.push e
  -- The parts of the scope no element styles, each with what its keys would need.
  let listHelp := "\\style{element}{ indent = ..., gap = ... } styles the lists the engine draws"
  let firstHelp := "\\setlist[itemize]{...} styles every level of a kind, \\setlist[itemize,2]{...} \
a deeper level apart"
  let unstyled : List (String × String × String) :=
    (kinds.filter (!setlistKinds.contains ·)).map (fun kd =>
        (kd, s!"'{what}' for '{kd}' lists", listHelp)) ++
      levels.filterMap fun l =>
        if l == 1 then some ("1", s!"'{what}', a first level alone,", firstHelp)
        else if l == 0 || 4 < l then some (toString l, s!"'{what}' at level {l}",
          "lists nest four levels")
        else none
  let vUnstyled : List (String × String × String) :=
    (kinds.filter (!Ir.listSetKinds.contains ·)).map (fun kd =>
        (kd, s!"'{what}' for '{kd}' lists", "a list's spacing reads itemize, enumerate and \
description scopes")) ++
      levels.filterMap fun l =>
        if l == 0 || 4 < l then some (toString l, s!"'{what}' at level {l}", "lists nest four levels")
        else none
  let mut entries : Array (String × Native.StyleValue) := #[]
  for e in styled do
    let key := e.key
    if scopes.isEmpty then
      unreadParam "\\setlist" key s!"'{what}' key '{key}'" pos
        (help := ((unstyled.head?.map (·.2.2)).getD listHelp))
      continue
    match e.value with
    | some value =>
      let v := rawSrc value
      if let some native := setlistLengthKeys.lookup key then
        if v.contains '*' then
          unreadParam "\\setlist" key s!"'{what}' key '{key}={v}'" pos
            (help := "the widest label is not measured; give the margin a length")
        else entries := Ir.redeclare entries native (.text (lengthOfTeX v))
      else if key == "label" then
        let written := (KeyVal.rawEntry e.src).2.getD ""
        if written.contains '*' then
          let part := s!"'{what}' key 'label={written}', a label counting its items,"
          unreadParam "\\setlist" "label" part pos
            (help := "a declared marker is the same on every item; the list keeps its numbering")
        else entries := Ir.redeclare entries "marker" (.tex (value.map (rebase (fun _ => pos) true)))
      else unreadParam "\\setlist" key s!"'{what}' key '{key}'" pos
    | none =>
      unreadParam "\\setlist" key s!"'{what}' key '{key}'" pos
  if vScopes.isEmpty then
    for (key, _) in vertical do
      unreadParam "\\setlist" key s!"'{what}' key '{key}'" pos
        (help := ((vUnstyled.head?.map (·.2.2)).getD listHelp))
  -- A scope part no element styles is named once, its keys standing for the parts styled.
  unless scopes.isEmpty || styled.isEmpty do
    for (name, part, help) in unstyled do
      unreadParam "\\setlist" name part pos (help := help)
  unless vScopes.isEmpty || vertical.isEmpty do
    for (name, part, help) in vUnstyled do
      unreadParam "\\setlist" name part pos (help := help)
  for sc in scopes do
    write fun st =>
      let old := ((st.setlists.find? (·.1 == sc)).map (·.2)).getD #[]
      let new := if star then entries.foldl (fun a e => Ir.redeclare a e.1 e.2) old else entries
      { st with setlists := Ir.redeclare st.setlists sc new }
  -- A scope's vertical keys replace the ones it held, as enumitem's `\\setlist` replaces every key.
  let mut spaced : Array (String × Array (String × String)) := #[]
  unless star && vertical.isEmpty do
    for sc in vScopes do
      let old := (((← get).listSpacings.find? (·.1 == sc)).map (·.2)).getD #[]
      let new := if star then vertical.foldl (fun a e => Ir.redeclare a e.1 e.2) old
        else vertical
      write fun st => { st with listSpacings := Ir.redeclare st.listSpacings sc new }
      let cleared := (old.filter fun e => !new.any (·.1 == e.1)).map fun e => (e.1, "none")
      unless new.isEmpty && cleared.isEmpty do
        spaced := spaced.push (Ir.listSetElement sc, new ++ cleared)
  let stored := (← get).setlists
  let spacings := (← get).listSpacings
  -- A kind's level is its own element once any scope declares through it.
  let declaredLevels (kind : String) : List Nat := [2, 3, 4].filter fun l =>
    stored.any (fun (sc, _) => sc == (some kind, some l) || sc == (none, some l)) ||
      spacings.any (·.1 == (some kind, some l))
  let styledTouched : List (String × Option Nat) := if styled.isEmpty then [] else
    scopes.flatMap fun (kd, l) =>
      (match kd with | some k => [k] | none => setlistKinds).flatMap fun k =>
        match l with
        | some n => [(k, some n)]
        | none => (k, none) :: (declaredLevels k).map fun n => (k, some n)
  -- A level element a spacing creates takes its kind's label and margin with it.
  let spacedTouched : List (String × Option Nat) := vScopes.filterMap fun
    | (some k, some n) =>
      if setlistKinds.contains k && 2 ≤ n && n ≤ 4 &&
          spaced.any (·.1 == setlistElement k (some n)) then some (k, some n)
      else none
    | _ => none
  -- Each element's entries, the kind's style keys and the scope's spacing in one declaration.
  let mut records : Array (String × Array (String × Native.StyleValue)) := #[]
  let touched := styledTouched ++ spacedTouched
  for (kind, level) in touched do
    let entriesAt := setlistRecord stored kind level
    unless entriesAt.isEmpty do
      records := Ir.redeclare records (setlistElement kind level) entriesAt
  for (el, es) in spaced do
    let held := ((records.find? (·.1 == el)).map (·.2)).getD #[]
    records := Ir.redeclare records el (held ++ es.map fun (k, v) => (k, .text v))
  if records.isEmpty then return #[]
  became what (String.join (records.toList.map fun (el, es) => Native.texStyleRender el es)) pos
  return records.foldl (init := #[]) fun out (el, es) =>
    let style := Native.texStyle el es pos
    out ++ style

/-- A registered control's lowering over its arguments. -/
private def lowerCall (c : CtrlCall) : Lowering → M (Array Raw)
  | .packages =>
    rewritePackages c.name ((c.src 1).splitOn "," |>.map (·.trimAscii.toString)) (c.optSrc 0)
      ((c.given 0).getD #[]) c.pos
  | .passOptions => do
    let options := (PackageImports.literalOptions (c.src 0)).toArray
    -- Each option keeps its raws beside its literal spelling, so a package reads its TeX.
    let items := (Entries.read .keyval (c.arg 0)).filterMap fun e =>
      (PackageImports.literalOptions e.src).head?.map (·, e.item)
    let packages := optionItems (c.src 1)
    write fun st => { st with loads := if c.name == "PassOptionsToClass" then
      { st.loads with
        rewriteClassPassed := st.loads.rewriteClassPassed ++ packages.map (·, options) }
      else { st.loads with rewritePassed := st.loads.rewritePassed ++ packages.map (·, items) } }
    discard s!"\\{c.name}\{...}\{...}" "load options are recorded" c.name c.pos
    return #[]
  | .defineColor => do
    let n := c.src 0
    let modeled := modeledColorSource (some (c.src 1)) (c.src 2)
    unless nativeName n && (modeled.isEmpty || Decl.wholeValue modeled) do
      say .W0102 s!"'\\definecolor\{{n}}' gives a name or a value no palette entry spells; \
the colour is not defined" c.pos (help := "name the colour with ASCII letters, digits, '.' or '_'")
      return #[]
    became s!"\\definecolor\{{n}}" (Native.Setting.palette #[(n, modeled)]).render c.pos
    carry (.palette #[(n, Decl.xcolorDefinitionPrefix ++ modeled)]) c.pos
  | .colorLet => do
    -- xcolor's `.` names the current colour, black in the preamble.
    let src := if (c.src 1).trimAscii.toString == "." then "#000000" else c.src 1
    unless nativeName (c.src 0) && (src.isEmpty || Decl.wholeValue src) do
      say .W0102 s!"'\\colorlet\{{c.src 0}}' gives a name or a colour no palette entry \
spells; the colour is not defined" c.pos (help := "name the colour with ASCII letters, digits, '.' or '_'")
      return #[]
    became "\\colorlet" (Native.Setting.palette #[(c.src 0, src)]).render c.pos
    carry (.palette #[(c.src 0, Decl.xcolorDefinitionPrefix ++ src)]) c.pos
  | .pageColor => pageColor (modeledColorSource (c.optSrc 0) (c.src 1)) c.pos
  | .geometry =>
    -- The command forms take the same keys the package options carry.
    geometry (c.arg 0) c.pos s!"\\{c.name}"
  | .crop =>
    -- A bare `\crop` is `[cam,noaxes]`, the command's own default argument.
    crop ((c.optSrc 0).getD "cam,noaxes") c.pos "\\crop" "crop"
  | .microtypeSetup => do
    -- microtype's `protrusion`, `expansion` and `activate` reach the native gates.
    let mut keys : Array (Native.PageKey × String) := #[]
    let mut dropped : Array String := #[]
    for e in KeyVal.items (c.src 0) do
      let (key, v) := KeyVal.entry e
      let v := v.getD ""
      let native : List Native.PageKey := if key == "activate" then [.protrusion, .expansion]
        else if key == "protrusion" then [.protrusion]
        else if key == "expansion" then [.expansion]
        else []
      if native.isEmpty then
        if !key.isEmpty then dropped := dropped.push key
      else
        match v with
        | "" | "true" | "compatibility" | "nocompatibility" =>
          keys := keys ++ (native.map (·, "on")).toArray
        | "false" => keys := keys ++ (native.map (·, "off")).toArray
        | _ => dropped := dropped.push key
    for k in dropped do
      unreadParam "microtypesetup" (KeyVal.entry k).1 s!"microtype key '{k}'" c.pos
    if keys.isEmpty then return #[]
    setting "\\microtypesetup" (.page keys) c.pos
  | .documentMetadata => documentMetadata (c.src 0) c.pos
  | .defineColorspace => do
    say .W0104 s!"'\\definecolorspace\{{c.src 1}}' declares a DeviceN or \
ICC-based colour space; the engine paints each ink in its own separation; skipped" c.pos
      (help := "declare each ink with \\definespotcolor")
    return #[]
  | .addToHook => do
    let hook := c.src 0
    let pos := c.pos
    if hook == "shipout/background" || hook == "shipout/foreground" then
      let st ← get
      let look (n : String) : Option (Array Raw) := match st.binds[n]? with
        | some (some v) => if v.arity == 0 then some v.raws else none
        | _ => none
      let lengths := (Array.range c.start).filterMap fun i => match c.raws[i]? with
        | some (Raw.ctrl "newlength" _) => (takeGroups c.raws (i + 1) 1).1[0]?.bind ctrlName
        | _ => none
      match shipoutRules look lengths (c.arg 2) with
      | some rules =>
        let key : Native.PageKey := if hook == "shipout/foreground" then .frontRule else .rule
        let entries := rules.map fun (x, y, w, h, ink) =>
          (key, Decl.quote s!"{x}; {y}; {w}; {h}; {ink}")
        if entries.isEmpty then
          discard s!"\\AddToHook\{{hook}}" "the hook draws no rule" s!"AddToHook:{hook}" pos
        return (← setting s!"\\AddToHook\{{hook}}" (.page entries) pos)
      | none => pure ()
    if hook == "shipout/before" then
      let st ← get
      let look (n : String) : Option (Array Raw) := match st.binds[n]? with
        | some (some v) => if v.arity == 0 then some v.raws else none
        | _ => none
      if let some (text, keep) := pageAttrText look (c.arg 2) then
        pageAttrBoxes text keep s!"\\AddToHook\{{hook}}" pos
        return #[]
    addToHook pos
    return #[]
  | .counter => do
    let st ← get
    let cmd := c.raws.extract (c.start - 1) c.stop
    let cmd := if st.file == st.docFile then cmd
      else #[Raw.env (Parse.inputEnv st.file) cmd c.pos]
    write fun st => { st with preCounters := st.preCounters ++ cmd }
    return #[]
  | .newLength => do
    -- `\newlength{\x}` allocates a length register at 0pt.
    let n := (ctrlName (c.arg 0)).getD ""
    setLength n "0pt" s!"\\newlength\{\\{n}}" c.pos
  | .newDimen => do
    -- `\newdimen\x` allocates a register only block templates read, so it is no native token.
    let n := (ctrlName (c.arg 0)).getD ""
    write fun st => { st with
      allocated := if st.allocated.contains n then st.allocated else st.allocated.push n }
    discard s!"\\newdimen\\{n}" "a register only the block templates assign and read" "newdimen" c.pos
    return #[]
  | .mathOperator => do
    -- `\DeclareMathOperator{\f}{name}` is a definition whose body is `\operatorname{name}`.
    let cmd := (ctrlName (c.arg 1)).getD ""
    became s!"\\DeclareMathOperator\{\\{cmd}}"
      s!"\\define \\{cmd}() \{\\operatorname\{...}}" c.pos
    return (Native.Head.define cmd "").raws c.pos |>.push
      (.group #[.ctrl "operatorname" c.pos, .group (c.arg 2) c.pos] c.pos)
  | .hyperSetup => do
    hyperrefLowered "\\hypersetup" "hypersetup" (← hyperrefKeys (c.arg 0) c.pos) c.pos
  | .runningField => do
    let src := trimBlank (c.arg 0)
    let name := c.name
    let slot := if name.startsWith "i" || name.startsWith "l" then 0
      else if name.startsWith "c" then 1 else 2
    write fun st =>
      let st := if st.head.isEmpty && st.foot.isEmpty then { st with runPos := c.pos } else st
      if name.endsWith "head" then
        { st with head := Ir.redeclare st.head slot src }
      else
        { st with foot := Ir.redeclare st.foot slot src }
    return #[]
  | .fancyField => do
    -- fancyhdr's `[places]`: one page sequence, so even and odd collapse onto the slot letter.
    let src := trimBlank (c.arg 1)
    let mut slots : Array Nat := #[]
    let mut evenOdd := false
    for e in KeyVal.items ((c.optSrc 0).getD "LCR") do
      for ch in e.toList do
        let ch := ch.toUpper
        if ch == 'L' && !slots.contains 0 then slots := slots.push 0
        else if ch == 'C' && !slots.contains 1 then slots := slots.push 1
        else if ch == 'R' && !slots.contains 2 then slots := slots.push 2
        else if ch == 'E' || ch == 'O' then evenOdd := true
    if evenOdd then
      sayOnce "fancyhdr:evenodd" .N0102
        "even and odd pages are one sequence here; the field applies to every page" c.pos
    let toHead := c.name != "fancyfoot"
    let toFoot := c.name != "fancyhead"
    write fun st =>
      let st := if st.head.isEmpty && st.foot.isEmpty then { st with runPos := c.pos } else st
      let put (parts : Array (Nat × Array Raw)) : Array (Nat × Array Raw) :=
        slots.foldl (init := parts) fun parts slot =>
          let parts := parts.filter (·.1 != slot)
          if src.isEmpty then parts else parts.push (slot, src)
      { st with
        head := if toHead then put st.head else st.head
        foot := if toFoot then put st.foot else st.foot }
    return #[]
  | .clearPageStyles => do
    -- scrlayer-scrpage's field reset clears every gathered head and foot field.
    write fun st => { st with head := #[], foot := #[] }
    became "\\clearpairofpagestyles" "no running fields; fields declared after apply" c.pos
    return #[]
  | .pageStyle => do
    let v := (c.src 0).trimAscii.toString
    match v with
    | "fancy" | "scrheadings" =>
      discard s!"\\pagestyle\{{v}}" "declared running fields apply by themselves"
        s!"pagestyle:{v}" c.pos
      return #[]
    | "plain" =>
      -- article's initial style is the centred page number in the foot.
      setting "\\pagestyle{plain}" (.page #[(.numbers, "on")]) c.pos
    | "empty" =>
      write fun st => { st with head := #[], foot := #[] }
      let page : Native.Setting := .page #[(.numbers, "off")]
      became "\\pagestyle{empty}" s!"{page.note?.getD ""}, and no running fields" c.pos
      carry page c.pos
    | _ =>
      sayOnce "ctrl:pagestyle" .W0104
        s!"'\\pagestyle\{{v}}' names running furniture the engine does not model; ignored" c.pos
        (help := "plain, empty, and fancy are modelled; \\runninghead / \\runningfoot \
declare the furniture directly")
      return #[]
  | .thisPageStyle => do
    -- Only the opening page can be meant from the preamble or the document's first line.
    if c.src 0 == "empty" then
      write fun st => { st with runFrom := 2 }
      became "\\thispagestyle{empty}" "\\runninghead[from = 2]{...}" c.pos
    return #[]
  | .addBibResource => do
    -- biblatex's `\addbibresource`: a `.bib` file `\printbibliography` later prints.
    let src := (c.src 1).trimAscii.toString
    let val (key : String) : Option String :=
      (KeyVal.items ((c.optSrc 0).getD "")).findSome? fun o =>
        match KeyVal.entry o with
        | (k, some v) => if k == key then some v else none
        | _ => none
    let remote := val "location" == some "remote"
    let format := (val "datatype").filter (· != "bibtex")
    if remote || format.isSome then
      let what := if remote then "a remote resource" else s!"a '{format.getD ""}' resource"
      say .W0104 s!"'\\addbibresource' names {what} '{src}'; the engine reads local \
.bib files only, so it is skipped" c.pos
        (help := "save the entries as a .bib file beside the document and name it")
        (subject := some "addbibresource")
      return #[]
    let src := if src.endsWith ".bib" then (src.dropEnd 4).toString else src
    unless (← get).bibResources.contains src do
      write fun st => { st with bibResources := st.bibResources.push src }
    became "\\addbibresource" s!"\\bibliography\{{src}}, at \\printbibliography" c.pos
    return #[]
  | .bibResources => do
    -- Under biblatex a preamble `\bibliography{refs}` adds the resource `refs.bib`.
    for src in KeyVal.items (c.src 0) do
      let src := if src.endsWith ".bib" then (src.dropEnd 4).toString else src
      unless src.isEmpty || (← get).bibResources.contains src do
        write fun st => { st with bibResources := st.bibResources.push src }
    became "\\bibliography" "biblatex's \\addbibresource, at \\printbibliography" c.pos
    return #[]
  | .natbibStyle =>
    if c.name == "bibpunct" then
      natbibStyle c.name (c.given 0) ((List.range 6).toArray.map fun i => c.arg (i + 1)) c.pos
    else natbibStyle c.name none #[c.arg 0] c.pos
  | .bibliographyStyle => do
    became "\\bibliographystyle" "read at \\begin{document}, as natbib reads the .aux" c.pos
    write fun st => { st with deferred := st.deferred.push (.beginDocument, st.file, c.pos,
      #[.ctrl "bibliographystyle" c.pos, .group (c.arg 0) c.pos]) }
    return #[]
  | .printBibliography => do
    if let some o := c.optSrc 0 then
      unless o.trimAscii.toString.isEmpty do
        say .W0101 s!"\\printbibliography options without a native equivalent \
were dropped: {o}" c.pos
    let srcs := (← get).bibResources
    if srcs.isEmpty then
      discard "\\printbibliography" "no \\addbibresource declared a file"
        "printbibliography" c.pos
      return #[]
    became "\\printbibliography"
      s!"biblatex's reference list of '{"', '".intercalate srcs.toList}'" c.pos
    return (Native.Head.bibliography (← get).bibStyle srcs).raws c.pos
  | .crefRange => do
    -- A starred range sets both halves unlinked, as hyperref's starred references do.
    let starred := (c.given 0).isSome
    let star : Array Raw := if starred then #[.word "*" c.pos] else #[]
    became s!"\\{c.name}{if starred then "*" else ""}" "the range pair: plural name, both numbers"
      c.pos
    let kind : Marker.Kind := if c.name == "Crefrange" then .crefRangeUp else .crefRange
    return #[.ctrl (Marker.name kind "") c.pos] ++ star ++ #[.group (c.arg 1) c.pos,
      .ctrl "labelcref" c.pos] ++ star ++ #[.group (c.arg 2) c.pos]
  | .fontSeries => do
    -- The series' weight half rides its marker; its width half has no engine axis.
    let code := (c.src 0).trimAscii.toString
    match Ir.Weight.parseSeries code with
    | some (w, width) =>
      -- premise: compatMarkerChecks — a top-level discard leaves the Doc without it
      if ← docPreamble then
        discard s!"\\fontseries\{{code}}" "'\\begin{document}' selects the normal series"
          s!"fontseries:{code}" c.pos
        return #[]
      if !width.isEmpty then
        sayOnce ("ctrl:fontseries:" ++ width) .W0104
          s!"'\\fontseries\{{code}}' also asks for the '{width}' width; \
the engine has no width axis, so only the weight is honoured" c.pos
      became s!"\\fontseries\{{code}}" s!"the {w.series} series" c.pos
      return #[.ctrl (Marker.name .series w.series) c.pos]
    | none =>
      sayOnce "ctrl:fontseries" .W0104
        s!"'\\fontseries\{{code}}' names no NFSS series; \
the weight in force stands" c.pos
      return #[]
  | .lineNumbers => lineNumbers c.name (c.optSrc 1) c.pos
  | .selectLanguage => do
    let lname := c.src 0
    -- premise: compatMarkerChecks — a top-level discard leaves the Doc without it
    if ← docPreamble then
      discard s!"\\selectlanguage\{{lname}}" "'\\begin{document}' selects the main language"
        s!"selectlanguage:{lname}" c.pos
      return #[]
    let tag := Locale.babelTagOf lname
    if (Locale.forTag tag).isNone then
      say .W0368 s!"no locale for language '{lname}'; English captions \
and patterns stand in" c.pos
        (help := Locale.shippedHelp)
    -- Only a switch in the body moves the language `\enquote` reads its quotes through.
    if (← get).inDoc then
      write fun st => { st with mainLang := tag }
    became s!"\\selectlanguage\{{lname}}" s!"the '{tag}' language attribute" c.pos
    return #[.ctrl (Marker.name .lang tag) c.pos]
  | .vspace => do
    -- The star's zero rule goes before the space, keeping it at a page's top.
    let native := skipNative (skipSrc (lengthSrc (c.arg 2)))
    if (c.given 0).isSome then
      became "\\vspace*" s!"a page-top anchor, then {native.note?.getD "nothing"}" c.pos
      return #[.ctrl vspaceAnchorMark c.pos] ++ (← carry native c.pos)
    setting "\\vspace" native c.pos
  | .pageBreak => do
    -- Every `\pagebreak` is taken whole; the demand level is not weighed.
    if (c.given 0).isSome then
      say .N0102 "'\\pagebreak' demand levels are ignored: the break is taken" c.pos
    return #[.ctrl "pagebreak" c.pos]
  | .komaFont => do
    let pos := c.pos
    let element := c.src 0
    if element == "disposition" then
      -- KOMA's `disposition` is the base font of every sectioning level at once.
      let native := "\\style{section}{ font = {...} }, per heading level"
      became "\\setkomafont{disposition}" native pos
      let mut out : Array Raw := #[]
      for lvl in ["section", "subsection", "subsubsection"] do
        out := out ++ Native.texStyle lvl #[("font", .tex (c.arg 1))] pos
      return out
    else if Ir.styleableElements.contains element then
      -- The font spec travels as a group, so its own idioms are still rewritten.
      let native := s!"\\style\{{element}}"
      became s!"\\setkomafont\{{element}}" (native ++ "{ font = {...} }") pos
      return Native.texStyle element #[("font", .tex (c.arg 1))] pos
    else
      say .W0111 s!"'\\setkomafont\{{element}}' names no styleable element; ignored" pos
        (help := "\\style{element}{ font = {...} } styles the elements the engine draws")
      return #[]
  | .sectionSkips => do
    let opt := c.optSrc 0
    let element := c.src 1
    let mut keys : Array (String × String) := #[]
    for e in KeyVal.items (opt.getD "") do
      match KeyVal.entry e with
      | ("beforeskip", some v) => keys := keys.push ("before", lengthOfTeX v)
      | ("afterskip", some v) => keys := keys.push ("after", lengthOfTeX v)
      | _ => pure ()
    if !Ir.styleableElements.contains element then
      say .W0111 s!"'\\RedeclareSectionCommand\{{element}}' names no styleable element; \
ignored" c.pos
        (help := "\\style{element}{ before = ..., after = ... } spaces the elements \
the engine draws")
      return #[]
    if keys.isEmpty then
      let dropped := (opt.getD "").trimAscii.toString
      unless dropped.isEmpty do
        say .W0101 s!"'\\RedeclareSectionCommand\{{element}}' entries without a \
native equivalent were dropped: {dropped}" c.pos
      return #[]
    setting s!"\\RedeclareSectionCommand\{{element}}" (.style element keys) c.pos
  | .setList => lowerSetList c
  | .sectionLines => sectionRule (c.src 1) c.pos
  | .uniMathSetup => unicodeMathOptions s!"\\unimathsetup\{{c.src 0}}" (c.src 0) c.pos
  | .unreadKeys => do
    for e in KeyVal.items (c.src 0) do
      let key := (KeyVal.entry e).1
      unless key.isEmpty do
        unreadParam s!"\\{c.name}" key s!"'\\{c.name}' key '{key}'" c.pos
    return #[]
  | .newCounter => do
    let counter := (c.src 0).trimAscii.toString
    -- premise: counterReadChecks — a counter's uses name what they lose
    if (← get).countersRead.contains counter then
      discard s!"\\newcounter\{{counter}}"
        "the engine does not model counters, and each use names what it loses"
        ("newcounter:" ++ counter) c.pos
    else
      sayOnce ("param:\\newcounter:" ++ counter) .W0104
        s!"counter '{counter}' is allocated, but nothing in the document reads it; \
'\\newcounter' changes nothing" c.pos (help := "use the counter where it should count, or drop it")
    return #[]
  | .ensureMath => return #[.ctrl c.name c.pos] ++ c.raws.extract c.start c.stop
  | .box => do
    -- An hbox's geometry is not modelled, so its drop is named once and its content stays.
    if c.args.any (·.isSome) then
      sayOnce ("ctrl:" ++ c.name) .W0104
        s!"'\\{c.name}' width and alignment are dropped; its content is kept" c.pos
        (help := "\\hfill spaces content apart; \\allow{W0104} accepts the drop")
    became s!"\\{c.name}" "its content" c.pos
    return #[]
  | .beamerFont => lowerBeamerFont c
  | .columnRatio => do
    let src := c.src 0
    if let some ratio := paracolRatio? src then
      write fun st => { st with paracolRatio := ratio }
    else
      sayOnce "paracol:ratio" .W0104
        s!"cannot read two-column ratio '{src}'; the previous ratio stands" c.pos
        (help := "write one fraction between zero and one, like \\columnratio{0.35}")
    if (c.given 1).isSome then
      sayOnce "paracol:right-ratio" .W0104
        "'\\columnratio{...}[...]' declares a paired-page ratio; the same-page ratio is used" c.pos
    became "\\columnratio" "the widths of the next two-column flow" c.pos
    return #[]
  | .useTheme => do
    let pos := c.pos
    let tname := themeAlias (c.src 1).trimAscii.toString
    let mut reseated : Array (String × Array (String × Native.StyleValue)) := #[]
    for (element, target, styleKey) in beamerFontElements do
      let seed := themeBlockFont tname element pos
      let some stored := (← get).beamerFonts.toList.lookup element | continue
      if seed.isEmpty then continue
      let fields := themeOver stored seed
      write fun st => { st with
        beamerFonts := Ir.redeclare st.beamerFonts element fields }
      reseated := reseated.push (target,
        #[(styleKey, .tex (beamerFontCommands (blockTitleFields element fields pos) pos))])
    let theme := Native.Head.theme tname
    became "\\usetheme" (" ".intercalate
      (theme.render :: reseated.toList.map fun (el, es) => Native.texStyleRender el es)) pos
    write fun st => { st with themeNamed := true }
    if (Theme.find? tname).isSome then
      write fun st => { st with themed := true, beamerTheme := tname }
    let options ← themeOptions "\\usetheme" s!"\\usetheme\{{tname}}" tname ((c.optSrc 0).getD "") pos
    let styles := reseated.foldl (init := #[]) fun out (el, es) =>
      let style := Native.texStyle el es pos
      out ++ style
    return theme.raws pos ++ styles ++ options
  | .molochSet => molochOptions s!"\\{c.name}" (c.src 0) c.pos
  | .titleGraphic => do
    if (c.src 0).trimAscii.toString.isEmpty then
      sayOnce "beamer:titlegraphic" .W0104
        "'\\titlegraphic{}' clears beamer configuration the engine does not have; skipped" c.pos
    else
      say .E0112
        "'\\titlegraphic' declares title-page content the engine does not place; the content is dropped" c.pos
        (help := "\\logo places an image on running pages; \\allow{E0112} accepts the loss")
    return #[]
  | .fontTheme => do
    -- `professionalfonts` asks for the engine's only behaviour, so it is agreement.
    if (c.src 1).trimAscii.toString == "professionalfonts" then
      discard "\\usefonttheme{professionalfonts}"
        "the engine always uses the declared fonts" "usefonttheme" c.pos
    else
      sayOnce "beamer:usefonttheme" .W0104
        "'\\usefonttheme' is beamer configuration the engine does not have; skipped" c.pos
        (help := beamerNative.lookup "usefonttheme")
    return #[]
  | .beamerOption => do
    -- `hide notes` asks for what `\note` already is here.
    if (c.src 1).trimAscii.toString == "hide notes" then
      discard "\\setbeameroption{hide notes}"
        "notes never enter the delivered pages" "setbeameroption" c.pos
    else
      sayOnce "beamer:setbeameroption" .W0104
        "'\\setbeameroption' is beamer configuration the engine does not have; skipped" c.pos
        (help := "a theme is a token bundle here: \\theme selects one, and \\palette \
and \\tokens declare the design directly")
    return #[]
  | .beamerCovered => do
    let pos := c.pos
    let src := (c.src 0).trimAscii.toString
    -- beamerbaseoverlay.sty: `invisible` hides, `transparent` keeps 15% unless given a share.
    let pct? : Option Nat := match KeyVal.entry src with
      | ("invisible", none) => some 0
      | ("transparent", none) => some Ir.transparentShare
      | ("transparent", some v) => v.toNat?
      | ("dynamic", none) => some Ir.dynamicShare
      | ("highly dynamic", none) => some Ir.highlyDynamicShare
      | _ => none
    match pct? with
    | some n =>
      let native : Native.Setting := .palette #[("covered", s!"{min n 99}\\%")]
      if 99 < n then
        sayOnce ("param:setbeamercovered:" ++ src) .W0109
          s!"'\\setbeamercovered\{{src}}' asks for undimmed covered content; it covers at the \
largest share the engine sets" pos
          (help := "\\palette{ covered = <n>% } sets the covered share") (detail := some "99%")
      else if src.startsWith "dynamic" || src.startsWith "highly dynamic" then
        sayOnce ("param:setbeamercovered:" ++ src) .W0109
          s!"'\\setbeamercovered\{{src}}' fades each step by its distance; every pending step \
covers at its next steps' share" pos
          (help := "\\palette{ covered = <n>% } sets the covered share") (detail := some s!"{n}%")
      else became "\\setbeamercovered" native.render pos
      carry native pos
    | none =>
      sayOnce ("param:setbeamercovered:" ++ src) .W0104
        s!"'\\setbeamercovered\{{src}}' is not modelled; covered content keeps the share in force, \
hidden unless one is declared" pos
        (help := "\\palette{ covered = <n>% } sets the covered share; 'invisible', 'transparent' \
and 'transparent=<n>' are understood")
      return #[]
  | .inputEncoding => do
    -- A file reads in one encoding, so a switch to the encoding in force changes nothing.
    let arg := (c.src 0).trimAscii.toString
    if Encoding.sameEncoding arg ((← get).inputenc.getD "utf8") then
      -- premise: inputDecodingChecks — a switch to the encoding in force ships the page without it
      discard s!"\\inputencoding\{{arg}}" "the file already reads in that encoding"
        ("inputencoding:" ++ arg) c.pos
    else
      sayOnce ("inputencoding:" ++ arg) .W0104
        s!"'\\inputencoding\{{arg}}' is not applied: each file reads in one encoding throughout"
        c.pos (help := s!"save the file in one encoding, UTF-8 best, and delete \
'\\inputencoding\{{arg}}'")
    return #[]
  | .komaOptions => do
    let entries := (KeyVal.items (c.src 0)).toList
    if entries.any fun e => (KeyVal.entry e).1 == "fontsize" then
      write fun st => { st with strutSkip := none }
    let satisfied (e : String) : Bool :=
      match KeyVal.entry e with
      | (key, some v) => (key == "headsepline" || key == "footsepline")
          && (v == "false" || v == "off" || v == "no")
      | _ => false
    let dropped := entries.filter (!satisfied ·)
    if dropped.isEmpty then
      unless entries.isEmpty do
        discard "\\KOMAoptions" "no head or foot separation rule is drawn" "KOMAoptions" c.pos
    else
      for e in dropped do
        unreadParam "KOMAoptions" (KeyVal.entry e).1 s!"'\\KOMAoptions' entry '{e}'" c.pos
    return #[]
  | .graphColor => do
    -- leanblueprint's `\graphcolor{type}{colour}{description}` colours the dependency graph.
    blueprintGraph c.pos (some s!"'\\graphcolor\{{(c.src 0).trimAscii.toString}}' colours \
that graph")
    return #[]
  | .blueprintSite => do
    -- leanblueprint's `\home` links nothing; `\github` and `\dochome` root the web page's links.
    if c.name == "home" then
      discard "\\home" "the web blueprint links nothing to the project's home page" "home" c.pos
      return #[]
    return blueprintSiteRaws c.name (urlText (c.arg 0)) c.pos

/-- Whether a lowered control is left, as written, to elaboration where it stands. -/
private def CtrlLeave.holds (st : St) (args : Array (Option (Array Raw))) : CtrlLeave → Bool
  -- premise: ctrlLeaveChecks — each leave keeps its control as written where its condition holds
  | .inDef => st.inDef
  | .inBody => st.inDoc
  | .inSeam => st.seam
  -- premise: counterChecks — a preamble counter numbers the body as at its start
  | .outsidePreamble => !(docPreamble st).1
  | .without pkg => !st.loads.pkgs.any (·.1 == pkg)
  | .notCtrl i => (args[i]?.join.bind ctrlName).isNone

/-- Whether a row's control is left, as written, to elaboration where it stands. -/
private def ctrlLeft (st : St) (row : CtrlRow) (args : Array (Option (Array Raw))) : Bool :=
  match row.action with
  | .lower _ gates => gates.leaves.any (·.holds st args)
  | .tokens .. | .native _ | .skip _ | .refuse .. | .discard .. | .inert => false

/-- The arguments a signature reads as brace groups, those that stand. -/
private def braceArgs (sig : List ArgKind) (args : Array (Option (Array Raw))) : Array (Array Raw) :=
  ((sig.zip args.toList).filterMap fun (k, a) => if k == .opt || k == .star then none else a).toArray

/-- A row's action where its control stands: its emission, with its report and writes. -/
private def ctrlRowRun (row : CtrlRow) (c : CtrlCall) : M (Array Raw) := do
  let pos := c.pos
  match row.action with
  | .tokens toks note =>
    if let some native := note then became s!"\\{row.name}" native pos
    return toks.toArray.map (rebase (fun _ => pos) true)
  | .native src =>
    -- setspace's spacings set the strut box again where they stand.
    if (packageOptionNatives.lookup "setspace").any (·.any (·.1 == row.name)) then
      write fun st => { st with strutSkip := none }
    setting s!"\\{row.name}" src pos
  | .skip amount =>
    -- premise: kernelLengthChecks — a declared skip amount ships at its command
    let native := match (← get).lens.find? (·.1 == amount) with
      | some (_, v) => skipNative { width := v }
      | none => skipNative { width := (kernelSkip amount).getD "" }
    setting s!"\\{row.name}" native pos
  | .refuse code .ctrl msg help =>
    sayOnce ("ctrl:" ++ row.name) code msg pos (help := help)
    return #[]
  | .refuse code .beamer msg help =>
    sayOnce ("beamer:" ++ row.name) code msg pos (help := help)
    return #[]
  | .refuse code .each msg help =>
    say code msg pos (help := help)
    return #[]
  | .discard why key =>
    discard s!"\\{row.name}" why key pos
    return #[]
  | .inert => return #[]
  | .lower l gates =>
    if let some stands := gates.paramStands then
      if ← paramArgs (braceArgs row.sig c.args) then
        unappliedParam row.name stands pos
        return #[]
    if let some help := gates.bodyHelp then
      -- premise: ctrlGateChecks — a declaration in the body leaves none of its arguments' ink
      if (← get).inDoc then
        sayOnce ("ctrl:" ++ row.name) .W0340
          (Diag.bodyDeclaration row.name) pos (help := help)
        return #[]
    lowerCall c l

/-- The rewrite of the control sequence `name` given what follows it: the
replacement and how many elements it consumed, or `none`. -/
private def rewriteCtrl (name : String) (pos : Pos) (raws : Array Raw) (start : Nat) :
    M (Option (Array Raw × Nat)) := fun s0 =>
  match rewriteCtrlAt name pos raws start s0 with
  | (none, s1) => (none, s1)
  | (some (repl, k), s1) =>
    (some (repl, k - start), if repl.isEmpty then (account name pos s0 s1).2 else s1)
where
  rewriteCtrlAt (name : String) (pos : Pos) (raws : Array Raw) (start : Nat) :
      M (Option (Array Raw × Nat)) := do
  -- premise: beamerTemplateChecks — flat preamble group pairs restore captures
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
  -- premise: biblatexChecks — authoryear `\cite` sets bare as lualatex and biber do
  if name == "cite" && (← get).bibStyle == some "plainnat" then
    return some (#[.ctrl "citealp" pos], start)
  -- premise: numberingChecks — the appendix numbers from 1 only with the package
  if name == "appendix" && (← get).loads.pkgs.any (·.1 == "appendixnumberbeamer") then
    return some (#[.ctrl frameRestartMark pos, .ctrl name pos], start)
  if let some row := ctrlRow? name then
    let some (args, k) := argsRead raws #[] row.sig start | return none
    if ctrlLeft (← get) row args then return none
    return some (← ctrlRowRun row ⟨name, pos, args, raws, start, k⟩, k)
  if let some (value, e) := plainAssign? name raws start then
    return some (← assignLength name value s!"\\{name}" pos, e)
  if let some settings := listSettings? (← get) name then
    let mut out : Array Raw := #[]
    for (n, v) in settings do
      out := out ++ (← assignLength n v s!"\\setlength\{\\{n}}" pos)
    return some (out, start)
  rewriteCtrlNamed name pos raws start

/-- A control word consumed with an empty replacement is paid for: the
diagnostics grew or a state write happened. -/
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

/-- A two-column paracol body split by its top-level switching commands. -/
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
      let (spanning, k) := if starred then takeRawOpt body afterStar else (none, k0)
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
        let kept := text.map (rebase (fun _ => spos) true)
        if current == 0 then left := left ++ kept else right := right ++ kept
      i := k
    | some r =>
      if current == 0 then left := left.push r else right := right.push r
      i := i + 1
  return (left, right)

/-- One paracol environment as the columns model, or its
content in order under one refusal. -/
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
  let width (p : Nat) : Raw :=
    .group #[.word s!"{paracolFactor p} * (linewidth - columnsep)" pos] pos
  became "\\begin{paracol}{2}...\\switchcolumn..."
    "\\begin{columns} with two independent column flows" pos
  return .env "columns"
    (#[.env "column" (#[width ratio] ++ left) pos,
      .env "column" (#[width (1000 - ratio)] ++ right) pos] ++ restores) pos

/-- beamer's command form of a column: at the top level of a
`{columns}` body, `\column{width}` starts a column running
to the next `\column` or the body's end. -/
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
      -- The environment form closes an open command-form column too.
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

/-- Every `{columns}` body's implicit column boundaries made explicit, whole
tree, before the rewrite walk. -/
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

/-- One level's group primitives paired into the brace groups they delimit; an
unpartnered one stands as written. -/
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

/-- Every matched group primitive made the brace group it is, whole tree, except
at the preamble's top level. -/
-- conserves: none — a pair's two words become the group they delimit
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

/-- One token of a delimited parameter text or of a use's
input, as TeX matches them. -/
private inductive DelimAtom where
  | ch (c : Char)
  | cs (name : String)
  | sp
  | other
  deriving BEq

/-- A use's input flattened to atoms, up to the paragraph's end. -/
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

/-- A refused delimited definition's parameter text: its literal run, then each
parameter's delimiter; `none` otherwise. -/
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

/-- The raws of `xs` from atom `a` up to atom `b`, a word split where an atom
boundary falls inside it. -/
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
parameter text reads; `none` when the input does not match. -/
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

/-- The command a definer standing at `i` names. -/
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

/-- The delimited signatures in force, with the global
writes that outlive a scope. -/
private structure DelimState where
  sigs : Array (String × DelimShape) := #[]
  globals : Array (String × Option DelimShape) := #[]

private def setDelimSig (sigs : Array (String × DelimShape))
    (n : String) (shape : Option DelimShape) : Array (String × DelimShape) :=
  let kept := sigs.filter (·.1 != n)
  match shape with
  | some sh => kept.push (n, sh)
  | none => kept

/-- The signatures in force after the definer at `i`. -/
private def sigsAfter (st : DelimState) (xs : Array Raw) (i : Nat) (d n : String) :
    DelimState :=
  let shape := if d == "def" || d == "gdef" then
      let params := ((xs.extract (i + 2) xs.size).toList.takeWhile
        fun r => !(r matches .group _ _)).toArray
      delimShape params
    else none
  { sigs := setDelimSig st.sigs n shape
    globals := if definesGlobally xs i d then st.globals.push (n, shape) else st.globals }

/-- The outer locals restored, replaying only the global
writes made since the scope opened. -/
private def delimClose (saved current : DelimState) : DelimState :=
  let writes := current.globals.extract saved.globals.size current.globals.size
  { current with
    sigs := writes.foldl (fun sigs (n, shape) => setDelimSig sigs n shape) saved.sigs }

mutual

/-- Every use of a refused delimited definition spelled as its braced call,
whole tree, in document order. -/
-- conserves: none — a use's delimiters are syntax, not text
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
    let (_, k, _) := takeHookArgs xs (i + 1)
    delimCallsList sigs xs ((out.push (.ctrl "apptocmd" pos)) ++ xs.extract (i + 1) k)
      rest (i + 1) (k - (i + 1))
  | .ctrl d p :: rest, i, 0 =>
    match (if Definer.redefiners.contains d then definedCmd xs i else none) with
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

/-- Delimited calls recovered in execution order: preamble,
replayed hooks, then body. -/
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

/-- Whether a raw is glue a row of boxes can hold between
two boxes: a space or a fill. -/
private def rowGlue : Raw → Bool
  | .space => true
  | .ctrl "hfill" _ => true
  | .ctrl "hfil" _ => true
  | _ => false

/-- A minipage's width group, its content, its `[pos]` bracket, and whether a
`[height]` or `[inner-pos]` follows; `none` without a width. -/
private def boxParts (body : Array Raw) : Option (Raw × Array Raw × Array Raw × Bool) :=
  let (_, k1) := takeOpts body 0 1
  let (more, k) := takeOpts body k1 2
  let k := skipSpaces body k
  match body[k]? with
  | some (.group g gp) => some (.group g gp, body.extract (k + 1) body.size, body.extract 0 k1, more)
  | _ => none

/-- Whether a paragraph ends at `i`, past spaces. -/
private def endsPara (rs : Array Raw) (i : Nat) : Bool :=
  match rs[skipSpaces rs i]? with
  | none | some (.par _) => true
  | _ => false

/-- Whether a paragraph opens at `i`. -/
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

/-- The minipage body a group holds, when the group is one
minipage box alone. -/
private def soleMinipage (g : Array Raw) : Option (Array Raw) :=
  let a := skipSpaces g 0
  match g[a]? with
  | some (.env "minipage" mb _) =>
    if skipSpaces g (a + 1) == g.size then some mb else none
  | _ => none

/-- A box at `i` that a row can hold: a bare
`\begin{minipage}`, or one inside a link wrapper. -/
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

/-- The mark of a linked row candidate, kept beside the original calls until
elaboration resolves the link names. -/
public def linkedBoxRowMark : String := " linked box row"

/-- Each run of minipages at one level separated by glue
holding a fill, as one `{columns}` row. -/
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
          match (rs[i]? : Option Raw) with
          | none => break
          | some r =>
            out := out.push r
            i := i + 1
  return (out, rows)

/-- One level of rows, formed and noted as translations onto
the columns model. -/
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

/-- beamer's `\begin{columns}[t]` alignment carried onto
every column that declares none. -/
private def columnsRowPos (body : Array Raw) : Array Raw := Id.run do
  let (o, _) := takeOpt body 0
  let some opts := o | return body
  let some letter := (KeyVal.items opts).find? (["t", "c", "b", "T"].contains ·) | return body
  let withPos (r : Raw) : Raw :=
    if let .env "column" cb cp := r then
      if cb[skipSpaces cb 0]? matches some (.sym '[' _) then r
      else .env "column" (#[.sym '[' cp, .word letter cp, .sym ']' cp] ++ cb) cp
    else r
  return body.map withPos

mutual

/-- The pass setting side-by-side boxes in one row, whole
tree, after the idiom rewrite. -/
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

/-- A completion with no pending declaration or hook interpreter. -/
private def QuietTail (st : St) : Prop :=
  st.head = #[] ∧ st.foot = #[] ∧ st.runFrom ≤ 1 ∧
    st.listResets = #[] ∧ st.listDefs = #[] ∧
    st.deferred = #[] ∧ st.beamerFootline = none ∧ st.beamerTemplates = #[]

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
  | nil => intro _ st h _; exact h
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
    (subject refused detail : Option String) (output : Option Diag.Output) (st : St)
    (h : TailDiag d st) :
    TailDiag d (say code msg pos help demote subject refused output detail st).2 :=
  ⟨h.1, Array.mem_push.mpr (Or.inl h.2)⟩

private theorem sayOnce_minipage_tailDiag (d : Diag) (code : DiagCode)
    (msg : String) (pos : Pos) (help : Option String) (demote : Bool)
    (st : St) (h : TailDiag d st) :
    TailDiag d (sayOnce "env:minipage-row-options" code msg pos help demote none st).2 := by
  unfold sayOnce
  apply state_bind_inv (TailDiag d) _ _ st h
  intro observed s hs
  dsimp only
  split <;> apply state_bind_inv (TailDiag d)
  all_goals
    first
    | exact hs
    | intro _ s' hs'; exact say_tailDiag d _ _ _ _ _ _ _ _ _ _ hs'

private theorem boxRowEmit_tailDiag (rs : Array Raw) (d : Diag) (st : St)
    (h : TailDiag d st) : TailDiag d (boxRowEmit rs st).2 := by
  unfold boxRowEmit
  generalize boxRows rs = result
  rcases result with ⟨out, rows⟩
  apply state_bind_inv (TailDiag d)
  · apply state_array_forIn_inv (TailDiag d) _ rows () st h
    intro entry _ _ s hs
    rcases entry with ⟨p, opts, pic⟩
    cases pic <;> dsimp only
    all_goals
      apply state_bind_inv (TailDiag d)
      · exact say_tailDiag d _ _ _ _ _ _ _ _ _ _ hs
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

/-- The raw itself when it is an overlay spec token, by shape alone. -/
private def specRaw? : Raw → Option Raw
  | r@(.word w _) =>
    if w.startsWith "<" && w.endsWith ">" && w.length ≥ 3 then some r else none
  | _ => none

/-- The specification word standing at `i`, if one does. -/
private def specWordAt (raws : Array Raw) (i : Nat) : Option String :=
  (raws[i]?.bind specRaw?).bind fun r =>
    match r with
    | .word w _ => some w
    | _ => none

/-- The beamer modes whose overlay count decides what a presentation shows. -/
private def presentationModes : List String := ["presentation", "beamer", "all"]

/-- Whether a specification declares that the presentation
has no slides here. -/
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

/-- An `{overprint}` body split into its content before the first item and the
items, each an `\onslide` spec with its content. -/
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

/-- Whether the step model can number an item's specification. -/
private def specNumbered : Raw → Bool
  | .word w _ => (Ir.overlayRange w).isSome
  | _ => false

/-- n-way alternation as nested binary alternation: item one
against all the rest. -/
private def overprintAlt (p : Pos) (tail : Array Raw) : List (Raw × Array Raw) → Array Raw
  | [] => tail
  | (sp, content) :: rest =>
    #[.ctrl "alt" p, sp, .group content p, .group (overprintAlt p tail rest) p]

/-- The items that can be alternatives, in body order. -/
private def overprintNumbered (items : Array (Raw × Array Raw)) :
    Array (Raw × Array Raw) :=
  items.filter fun it => specNumbered it.1

/-- The items whose spec the step model cannot number, in body order. -/
private def overprintLoose (items : Array (Raw × Array Raw)) :
    Array (Raw × Array Raw) :=
  items.filter fun it => !specNumbered it.1

/-- An `{overprint}` as alternation with the count of unnumberable items, or
`none` for a body read as no alternation. -/
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
      -- Last item outermost: beamer's overprint gives priority to the item written last.
      for r in overprintAlt p tail numbered.toList.reverse do
        out := out.push r
      return out.push (.par p), loose.size)

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

/-- Every `{overprint}` in a raw sequence spliced into its alternation. -/
private def overprintList : List Raw → Array Raw → Nat → M (Array Raw)
  | [], out, _ => pure out
  | _ :: rest, out, skip + 1 => overprintList rest out skip
  | .ctrl "apptocmd" pos :: rest, out, 0 => do
    let args := rest.toArray
    let (_, k, _) := takeHookArgs args 0
    overprintList rest ((out.push (.ctrl "apptocmd" pos)) ++ args.extract 0 k) k
  | r :: rest, out, 0 => do
    let rs ← overprintRaw r
    overprintList rest (out ++ rs) 0
termination_by structural l _ _ => l

/-- Descends into a group or environment, so an overprint
nested anywhere is found. -/
private def overprintRaw : Raw → M (Array Raw)
  | .group body p => do return #[.group (← overprintList body.toList #[] 0) p]
  | .env "overprint" body p => do
    let body' ← overprintList body.toList #[] 0
    match overprintPlan body' p with
    | some (repl, loose) =>
      became "\\begin{overprint}" "\\alt alternation, one item per overlay" p
      -- An unnumberable spec is named once for the document (W0105).
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

/-- The alternation this pass writes, under a name no document can define. -/
private def altHead : String := overlayNativeName "alt"

/-- An `\only` this pass reads: beamer's, unless the document defines the
name itself. -/
private def onlyHead (userOnly : Bool) (c : String) : Bool :=
  c == overlayNativeName "only" || (!userOnly && c == "only")

/-- An alternation the readings read: this pass's own, and `\alt` unless the
document defines it. -/
private def isAltHead (userAlt : Bool) (c : String) : Bool :=
  c == altHead || (!userAlt && c == "alt")

/-- The command a definer's next tokens name, past a star and spaces. -/
private def definedName : List Raw → Option String
  | .space :: rest => definedName rest
  | .word "*" _ :: rest => definedName rest
  | .ctrl n _ :: _ => some n
  | .group g _ :: _ =>
    match g.toList.filter (· != .space) with
    | [.ctrl n _] => some n
    | _ => none
  | _ => none

mutual

/-- Does the document define the command `n`, anywhere it writes it? -/
private def definesList (n : String) : List Raw → Bool
  | [] => false
  | .ctrl d _ :: rest =>
    (Definer.nameDefiners.contains d && definedName rest == some n) || definesList n rest
  | r :: rest => definesRaw n r || definesList n rest
termination_by structural l => l

private def definesRaw (n : String) : Raw → Bool
  | .group g _ => definesList n g.toList
  | .env _ g _ => definesList n g.toList
  | .math _ g _ => definesList n g.toList
  | .word .. | .space | .par _ | .ctrl .. | .sym .. | .verb .. => false
termination_by structural r => r

end

/-- Which of `\only` and `\alt` the document defines itself. -/
private structure ReadCx where
  userOnly : Bool
  userAlt : Bool

/-- The environments whose bodies this pass leaves to their reader. -/
private def pictureBodies : List String := pictureEnvs ++ ["tikzcd", "picture", "pgfpicture"]

/-- `\only<s>{arg}` as `\alt<s>{arg}{}`. -/
private def onlyAlt (p : Pos) (sel : Raw) (arg : Array Raw) (q : Pos) : Array Raw :=
  #[.ctrl altHead p, sel, .group arg q, .group #[] q]

/-- `\only<s>` of a control word, the groups after it in both alternatives. -/
private def onlyCtrl (p : Pos) (sel : Raw) (n : String) (q : Pos) (groups : Array Raw) :
    Array Raw :=
  #[.ctrl altHead p, sel, .group (#[.ctrl n q] ++ groups) q, .group groups q]

/-- An `\only` head whose selector the step model numbers. -/
private def onlyNumbered (userOnly : Bool) (c : String) : Raw → Bool
  | .word w _ => onlyHead userOnly c && (Ir.overlayRange w).isSome
  | _ => false

mutual

/-- Every numbered `\only` as its alternation, inside a formula only where
`math` is set. -/
-- conserves: none — a surface boundary walk; no IR content has been elaborated.
private def onlyAltList (userOnly math : Bool) : List Raw → Array Raw → Nat → Array Raw
  | [], out, _ => out
  | _ :: rest, out, skip + 1 => onlyAltList userOnly math rest out skip
  | .ctrl "apptocmd" pos :: rest, out, 0 =>
    -- Overlay bodies inside a patch or callback are not live material.
    let args := rest.toArray
    let (_, k, _) := takeHookArgs args 0
    onlyAltList userOnly math rest ((out.push (.ctrl "apptocmd" pos)) ++ args.extract 0 k) k
  | .ctrl c p :: sel :: .ctrl n q :: .group a qa :: .group b qb :: rest, out, 0 =>
    if onlyNumbered userOnly c sel then
      let alt := onlyCtrl p sel n q
        #[.group (onlyAltList userOnly math a.toList #[] 0) qa,
          .group (onlyAltList userOnly math b.toList #[] 0) qb]
      onlyAltList userOnly math rest (out ++ alt) 0
    else onlyAltList userOnly math (sel :: .ctrl n q :: .group a qa :: .group b qb :: rest)
      (out.push (.ctrl c p)) 0
  | .ctrl c p :: sel :: .ctrl n q :: .group a qa :: rest, out, 0 =>
    if onlyNumbered userOnly c sel then
      let alt := onlyCtrl p sel n q #[.group (onlyAltList userOnly math a.toList #[] 0) qa]
      onlyAltList userOnly math rest (out ++ alt) 0
    else onlyAltList userOnly math (sel :: .ctrl n q :: .group a qa :: rest)
      (out.push (.ctrl c p)) 0
  | .ctrl c p :: sel :: .space :: .ctrl n q :: .group a qa :: .group b qb :: rest, out, 0 =>
    if onlyNumbered userOnly c sel then
      let alt := onlyCtrl p sel n q
        #[.group (onlyAltList userOnly math a.toList #[] 0) qa,
          .group (onlyAltList userOnly math b.toList #[] 0) qb]
      onlyAltList userOnly math rest (out ++ alt) 0
    else onlyAltList userOnly math
      (sel :: .space :: .ctrl n q :: .group a qa :: .group b qb :: rest) (out.push (.ctrl c p)) 0
  | .ctrl c p :: sel :: .space :: .ctrl n q :: .group a qa :: rest, out, 0 =>
    if onlyNumbered userOnly c sel then
      let alt := onlyCtrl p sel n q #[.group (onlyAltList userOnly math a.toList #[] 0) qa]
      onlyAltList userOnly math rest (out ++ alt) 0
    else onlyAltList userOnly math (sel :: .space :: .ctrl n q :: .group a qa :: rest)
      (out.push (.ctrl c p)) 0
  -- The empty word a selector moved to the head leaves behind.
  | .ctrl c p :: sel :: .word "" q :: .space :: arg :: rest, out, 0 =>
    if onlyNumbered userOnly c sel then
      match onlyArg userOnly math p sel arg with
      | some rs => onlyAltList userOnly math rest (out ++ rs) 0
      | none => onlyAltList userOnly math (sel :: .word "" q :: .space :: arg :: rest)
          (out.push (.ctrl c p)) 0
    else onlyAltList userOnly math (sel :: .word "" q :: .space :: arg :: rest)
      (out.push (.ctrl c p)) 0
  | .ctrl c p :: sel :: .word "" q :: arg :: rest, out, 0 =>
    if onlyNumbered userOnly c sel then
      match onlyArg userOnly math p sel arg with
      | some rs => onlyAltList userOnly math rest (out ++ rs) 0
      | none => onlyAltList userOnly math (sel :: .word "" q :: arg :: rest)
          (out.push (.ctrl c p)) 0
    else onlyAltList userOnly math (sel :: .word "" q :: arg :: rest) (out.push (.ctrl c p)) 0
  | .ctrl c p :: sel :: .space :: arg :: rest, out, 0 =>
    if onlyNumbered userOnly c sel then
      match onlyArg userOnly math p sel arg with
      | some rs => onlyAltList userOnly math rest (out ++ rs) 0
      | none => onlyAltList userOnly math (sel :: .space :: arg :: rest) (out.push (.ctrl c p)) 0
    else onlyAltList userOnly math (sel :: .space :: arg :: rest) (out.push (.ctrl c p)) 0
  | .ctrl c p :: sel :: arg :: rest, out, 0 =>
    if onlyNumbered userOnly c sel then
      match onlyArg userOnly math p sel arg with
      | some rs => onlyAltList userOnly math rest (out ++ rs) 0
      | none => onlyAltList userOnly math (sel :: arg :: rest) (out.push (.ctrl c p)) 0
    else onlyAltList userOnly math (sel :: arg :: rest) (out.push (.ctrl c p)) 0
  | r :: rest, out, 0 => onlyAltList userOnly math rest (out.push (onlyAltRaw userOnly math r)) 0
termination_by structural l _ _ => l

/-- The alternation of `\only<s>` over its undelimited argument: a group, a
word's first character, a control word, a character or a whole formula. -/
private def onlyArg (userOnly math : Bool) (p : Pos) (sel : Raw) : Raw → Option (Array Raw)
  | .group g q => some (onlyAlt p sel (onlyAltList userOnly math g.toList #[] 0) q)
  | .word w q =>
    match w.toList with
    | _ :: tail@(_ :: _) =>
      some #[.ctrl altHead p, sel, .group #[.word w q] q,
        .group #[.word (String.ofList tail) { q with col := q.col + 1 }] q]
    | [c] => some (onlyAlt p sel #[.word (String.singleton c) q] q)
    | [] => none
  | .ctrl n q => some (onlyAlt p sel #[.ctrl n q] q)
  | .sym c q => some (onlyAlt p sel #[.sym c q] q)
  | .math d body q => some (onlyAlt p sel #[.math d body q] q)
  | .space | .par _ | .env .. | .verb .. => none

private def onlyAltRaw (userOnly math : Bool) : Raw → Raw
  | .group body p => .group (onlyAltList userOnly math body.toList #[] 0) p
  | .env n body p =>
    if pictureBodies.contains n || (!math && mathEnvs.contains n) then .env n body p
    else .env n (onlyAltList userOnly math body.toList #[] 0) p
  | .math d body p =>
    if math then .math d (onlyAltList userOnly math body.toList #[] 0) p else .math d body p
  | .word w p => .word w p
  | .space => .space
  | .par p => .par p
  | .ctrl n p => .ctrl n p
  | .sym c p => .sym c p
  | .verb env s p => .verb env s p

end

/-- The commands a copy per reading would count twice. -/
private def readingCounts : List String :=
  ["label", "tag", "footnote", "footnotemark", "footnotetext", "pause", "frametitle",
   "framesubtitle", "titlepage", "maketitle", "part", "chapter", "section", "subsection",
   "subsubsection", "paragraph", "note"]

/-- The definitions, assignments and switches a paragraph's reading cannot
hold: a copy would repeat them, or its group end their reach. -/
private def readingDeclarations : List String :=
  Definer.nameDefiners ++ Ir.sizeScale.map (·.1) ++
    Definer.names (fun r => (r.defines == .environment && r.family == .latex) ||
      r.family == .amsmath) ++
    ["newcounter", "newlength",
     "setlength", "addtolength", "setcounter", "addtocounter", "stepcounter", "refstepcounter",
     "newif", "newtheorem", "newcolumntype", "definecolor", "colorlet",
     "setbeamercolor", "setbeamertemplate", "setbeamerfont", "usebeamercolor", "usebeamerfont",
     "usebeamertemplate", "setbeamercovered", "selectlanguage", "linespread", "selectfont",
     "fontsize", "centering", "raggedleft", "raggedright", "RaggedLeft", "RaggedRight",
     "bfseries", "mdseries", "itshape", "slshape", "upshape", "scshape", "rmfamily",
     "sffamily", "ttfamily", "normalfont", "em", "bf", "it", "sl", "sc", "rm", "sf", "tt",
     "color", "normalcolor"]

/-- The overlay commands the math parser cannot read. -/
private def formulaOverlays : List String :=
  ["uncover", "visible", "invisible", "onslide", "only", "alt"]

/-- An overlay selector word, `<2>`. -/
private def selectorWord (w : String) : Bool := w.startsWith "<" && w.endsWith ">"

/-- The unnumbered math environments a formula's readings may copy. -/
private def readableMathEnvs : List String :=
  ["equation*", "displaymath", "align*", "gather*"]

/-- The environments a paragraph's readings may copy. -/
private def readingEnvs : List String :=
  listEnvs ++ tableEnvs ++ readableMathEnvs ++
    ["center", "flushleft", "flushright", "quote", "quotation", "verse", "minipage", "block",
     "alertblock", "exampleblock", "columns", "column"]

/-- The environments whose bodies are a flow of paragraphs, with the argument
groups each opens on. -/
private def flowEnvArgs : List (String × Nat) :=
  [("document", 0), ("frame", 2), ("block", 1), ("alertblock", 1), ("exampleblock", 1),
   ("center", 0), ("flushleft", 0), ("flushright", 0), ("quote", 0), ("quotation", 0),
   ("verse", 0), ("minipage", 1), ("column", 1), ("theorem", 0), ("lemma", 0),
   ("corollary", 0), ("proposition", 0), ("definition", 0), ("definitions", 0),
   ("example", 0), ("examples", 0), ("fact", 0), ("proof", 0), ("remark", 0)]

/-- A selector's numbered steps: none where the step model cannot number it. -/
private def altSpecOf : Raw → Option Ir.OverlaySpec
  | .word w _ => Ir.overlayRange w
  | _ => none

private def altSelects (sel : Raw) (k : Nat) : Bool :=
  (altSpecOf sel).any (·.selects k)

/-- Is a reading blank space and empty groups alone? -/
private def readingEmpty (r : Array Raw) : Bool :=
  r.all fun x => x matches .space || x matches .par _ || x matches .group #[] _

mutual

/-- Every alternation's selector in `l`, nested ones included; none where one
is unnumbered or `l` holds what a reading cannot copy. -/
private def altSpecs (cx : ReadCx) (formula : Bool) : List Raw → Option (List Ir.OverlaySpec)
  | [] => some []
  | .ctrl n _ :: rest =>
    if isAltHead cx.userAlt n then specsAfterAlt cx formula rest
    else if readingCounts.contains n || (formula && formulaOverlays.contains n) ||
      (!formula && readingDeclarations.contains n) then none
    else altSpecs cx formula rest
  | r :: rest => do
    let sr ← altSpecsRaw cx formula r
    let rs ← altSpecs cx formula rest
    pure (sr ++ rs)
termination_by structural l => l

private def specsAfterAlt (cx : ReadCx) (formula : Bool) :
    List Raw → Option (List Ir.OverlaySpec)
  | sel :: rest => (altSpecOf sel).bind fun s => specsAltA cx formula s rest
  | [] => none
termination_by structural l => l

private def specsAltA (cx : ReadCx) (formula : Bool) (s : Ir.OverlaySpec) :
    List Raw → Option (List Ir.OverlaySpec)
  | .space :: .group g _ :: rest => specsAltB cx formula s (altSpecs cx formula g.toList) rest
  | .group g _ :: rest => specsAltB cx formula s (altSpecs cx formula g.toList) rest
  | _ => none
termination_by structural l => l

private def specsAltB (cx : ReadCx) (formula : Bool) (s : Ir.OverlaySpec)
    (sa : Option (List Ir.OverlaySpec)) : List Raw → Option (List Ir.OverlaySpec)
  | .space :: .group g _ :: rest | .group g _ :: rest => do
    let a ← sa
    let b ← altSpecs cx formula g.toList
    let r ← altSpecs cx formula rest
    pure (s :: a ++ b ++ r)
  | _ => none
termination_by structural l => l

private def altSpecsRaw (cx : ReadCx) (formula : Bool) : Raw → Option (List Ir.OverlaySpec)
  | .group g _ => altSpecs cx formula g.toList
  | .env n g _ =>
    if pictureBodies.contains n || (!formula && !readingEnvs.contains n) then none
    else altSpecs cx (formula || mathEnvs.contains n) g.toList
  | .math _ g _ => altSpecs cx true g.toList
  | .ctrl n _ =>
    if isAltHead cx.userAlt n || readingCounts.contains n ||
      (formula && formulaOverlays.contains n) || (!formula && readingDeclarations.contains n)
    then none else some []
  -- A selector no alternation took is a command's no formula reading sets.
  | .word w _ => if formula && selectorWord w then none else some []
  | .space | .par _ | .sym .. | .verb .. => some []
termination_by structural r => r

end

mutual

/-- `l`'s tokens at step `k`, each alternation as the alternative shown, in text an
empty group for nothing; with `k` none, the handout, an alternation showing the
other of a blank alternative and otherwise step 1's. -/
-- conserves: none — a surface boundary walk; no IR content has been elaborated.
private def readTokens (cx : ReadCx) (math : Bool) (k : Option Nat) :
    List Raw → Array Raw → Array Raw
  | [], out => out
  | .ctrl n p :: rest, out =>
    if isAltHead cx.userAlt n then readAfterAlt cx math k p n rest out
    else readTokens cx math k rest (out.push (.ctrl n p))
  | r :: rest, out => readTokens cx math k rest (out.push (readRaw cx math k r))
termination_by structural l _ => l

/-- A shape that is no alternation keeps its tokens unread. -/
private def readAfterAlt (cx : ReadCx) (math : Bool) (k : Option Nat) (p : Pos) (n : String) :
    List Raw → Array Raw → Array Raw
  | sel :: rest, out => readAltA cx math k p n sel rest out
  | [], out => out.push (.ctrl n p)
termination_by structural l _ => l

private def readAltA (cx : ReadCx) (math : Bool) (k : Option Nat) (p : Pos) (n : String)
    (sel : Raw) : List Raw → Array Raw → Array Raw
  | .space :: .group g _ :: rest, out =>
    readAltB cx math k p n sel (readTokens cx math k g.toList #[]) rest out
  | .group g _ :: rest, out => readAltB cx math k p n sel (readTokens cx math k g.toList #[]) rest out
  | rest, out => (out.push (.ctrl n p)).push sel ++ rest.toArray
termination_by structural l _ => l

private def readAltB (cx : ReadCx) (math : Bool) (k : Option Nat) (p : Pos) (n : String)
    (sel : Raw) (ra : Array Raw) : List Raw → Array Raw → Array Raw
  | .space :: .group g _ :: rest, out | .group g _ :: rest, out =>
    let rb := readTokens cx math k g.toList #[]
    let shown := match k with
      | some k => if altSelects sel k then ra else rb
      | none =>
        if readingEmpty rb then ra else if readingEmpty ra then rb
        else if altSelects sel 1 then ra else rb
    let shown := if !math && shown.isEmpty then #[.group #[] p] else shown
    readTokens cx math k rest (out ++ shown)
  | rest, out => (out.push (.ctrl n p)).push sel ++ ra ++ rest.toArray
termination_by structural l _ => l

private def readRaw (cx : ReadCx) (math : Bool) (k : Option Nat) : Raw → Raw
  | .group g p => .group (readTokens cx math k g.toList #[]) p
  | .env n g p =>
    if pictureBodies.contains n then .env n g p
    else .env n (readTokens cx (math || mathEnvs.contains n) k g.toList #[]) p
  | .math d g p => .math d (readTokens cx true k g.toList #[]) p
  | .word w p => .word w p
  | .space => .space
  | .par p => .par p
  | .ctrl n p => .ctrl n p
  | .sym c p => .sym c p
  | .verb env s p => .verb env s p
termination_by structural r => r

end

/-- The steps at which a reading may change: step 1, every range's first
step and the step after every range's last. -/
private def readingBreaks (specs : List Ir.OverlaySpec) : List Nat :=
  let points := specs.flatMap fun s => s.ranges.flatMap fun (a, b) =>
    max a 1 :: (b.map (· + 1)).toList
  ((1 :: points).eraseDups.toArray.qsort (· < ·)).toList

/-- The selector word naming `segs`. -/
private def segmentsWord (segs : List (Nat × Option Nat)) (p : Pos) : Raw :=
  .word ("<" ++ ",".intercalate (segs.map fun (a, b) => match b with
    | none => s!"{a}-"
    | some b => if a == b then s!"{a}" else s!"{a}-{b}") ++ ">") p

/-- Each reading's steps: from its break up to the next, the last open. -/
private def readingSegments : List (Nat × Array Raw) → List ((Nat × Option Nat) × Array Raw)
  | [] => []
  | [(a, r)] => [((a, none), r)]
  | (a, r) :: (b, rb) :: rest => ((a, some (b - 1)), r) :: readingSegments ((b, rb) :: rest)

/-- The distinct readings with the steps each shows on, in order of first showing. -/
private def distinctReadings (segs : List ((Nat × Option Nat) × Array Raw)) :
    Array (Array Raw × List (Nat × Option Nat)) := Id.run do
  let mut out : Array (Array Raw × List (Nat × Option Nat)) := #[]
  for (sg, r) in segs do
    match out.findIdx? (·.1 == r) with
    | some i => out := out.modify i fun (r', ss) => (r', ss ++ [sg])
    | none => out := out.push (r, [sg])
  return out

/-- Readings chained as alternations, each under the selector of its own
steps, the last standing where no selector reached. -/
private def nestReadings (p : Pos) : List (Array Raw × List (Nat × Option Nat)) → Array Raw
  | [] => #[]
  | [(r, _)] => r
  | (r, ss) :: rest =>
    #[.ctrl altHead p, segmentsWord ss p, .group r p, .group (nestReadings p rest) p]

/-- The distinct readings through step `most` as one chain, each under a
closed selector of its steps, and `past` where none reaches. -/
private def readingChain (p : Pos) (most : Nat) (readings : List (Nat × Array Raw))
    (past : Array Raw) : Array Raw :=
  let segs := (readingSegments readings).filterMap fun ((a, b), r) =>
    if a ≤ most then some ((a, some (min (b.getD most) most)), r) else none
  nestReadings p ((distinctReadings segs).toList ++ [(past, [])])

/-- The chain under an alternation no step selects, whose other group is the
handout a rendering with no snap state shows; the chain alone where step 1
reads as the handout. -/
private def handoutChain (p : Pos) (handout first : Array Raw) (chain : Array Raw) : Array Raw :=
  if handout == first then chain
  else #[.ctrl altHead p, .word "<0>" p, .group handout p, .group chain p]

/-- A unit's readings at each break through `most`, past it, and under the
handout. -/
private structure Readings where
  most : Nat
  steps : List (Nat × Array Raw)
  past : Array Raw
  handout : Array Raw

/-- `body`'s readings, each set by `shape`; none where it holds no numbered
alternation or what a reading cannot copy. -/
private def readingsOf (cx : ReadCx) (formula : Bool) (body : Array Raw)
    (shape : Array Raw → Array Raw) : Option Readings :=
  match altSpecs cx formula body.toList with
  | some specs@(_ :: _) =>
    let most := specs.foldl (fun m s => max m s.maxStep) 1
    let read (k : Option Nat) := shape (readTokens cx formula k body.toList #[])
    some { most, steps := ((readingBreaks specs).filter (· ≤ most)).map fun k => (k, read (some k)),
           past := read (some (most + 1)), handout := read none }
  | some [] | none => none

private def readingsChain (p : Pos) (rd : Readings) : Array Raw :=
  handoutChain p rd.handout ((rd.steps.head?.map (·.2)).getD #[])
    (readingChain p rd.most rd.steps rd.past)

/-- A formula as its readings' alternation, or as written where they cannot
be read. -/
private def formulaReadings (cx : ReadCx) (wrap : Array Raw → Raw) (body : Array Raw)
    (orig : Raw) (p : Pos) : Array Raw :=
  match readingsOf cx true (onlyAltList cx.userOnly true body.toList #[] 0) fun r => #[wrap r] with
  | some rd => readingsChain p rd
  | none => #[orig]

mutual

/-- Every formula of `l` with its `\only` as alternations. -/
-- conserves: none — a surface boundary walk; no IR content has been elaborated.
private def formulaOnlyList (cx : ReadCx) : List Raw → Array Raw → Array Raw
  | [], out => out
  | r :: rest, out => formulaOnlyList cx rest (out.push (formulaOnlyRaw cx r))

private def formulaOnlyRaw (cx : ReadCx) : Raw → Raw
  | .math d g p => .math d (onlyAltList cx.userOnly true g.toList #[] 0) p
  | .env n g p =>
    if pictureBodies.contains n then .env n g p
    else if mathEnvs.contains n then .env n (onlyAltList cx.userOnly true g.toList #[] 0) p
    else .env n (formulaOnlyList cx g.toList #[]) p
  | .group g p => .group (formulaOnlyList cx g.toList #[]) p
  | .word w p => .word w p
  | .space => .space
  | .par p => .par p
  | .ctrl n p => .ctrl n p
  | .sym c p => .sym c p
  | .verb env s p => .verb env s p

end

private def trimReading (r : Array Raw) : Array Raw :=
  let blank (x : Raw) : Bool := x matches .space || x matches .par _
  let r := r.extract (r.findIdx? (!blank ·) |>.getD r.size) r.size
  match (List.range r.size).reverse.find? fun i => (r[i]?.map (!blank ·)).getD false with
  | some i => r.extract 0 (i + 1)
  | none => #[]

/-- A unit's readings, its formulas' `\only` included. -/
private def unitReadings (cx : ReadCx) (raws : Array Raw) : Option Readings :=
  readingsOf cx false (formulaOnlyList cx raws.toList #[]) trimReading

/-- Does a group hold a paragraph break, a display or an environment? -/
private def holdsBlock (g : Array Raw) : Bool :=
  g.any fun r => match r with
    | .par _ => true
    | .math d _ _ => d
    | .env .. => true
    | .word .. | .space | .ctrl .. | .sym .. | .group .. | .verb .. => false

/-- A token that splits environment `n`'s structure: a list's item, or a
table's cell, row or rule. -/
private def splitsAt (n : String) : Raw → Bool
  | .ctrl c _ => (listEnvs.contains n && c == "item") ||
      (tableEnvs.contains n && ["\\", "tabularnewline", "hline", "cline", "toprule",
        "midrule", "bottomrule", "cmidrule", "addlinespace"].contains c)
  | .sym c _ => tableEnvs.contains n && c == '&'
  | .group .. | .env .. | .math .. | .word .. | .space | .par _ | .verb .. => false

/-- The two groups of each alternation standing directly in `l`. -/
private def topAlts (cx : ReadCx) : List Raw → List (Array Raw × Array Raw)
  | [] => []
  | .ctrl n _ :: _ :: .group a _ :: .group b _ :: rest =>
    if isAltHead cx.userAlt n then (a, b) :: topAlts cx rest else topAlts cx rest
  | .ctrl n _ :: _ :: .space :: .group a _ :: .space :: .group b _ :: rest =>
    if isAltHead cx.userAlt n then (a, b) :: topAlts cx rest else topAlts cx rest
  | _ :: rest => topAlts cx rest

/-- Is `l` alternations and blank space alone? -/
private def onlyAlts (cx : ReadCx) : List Raw → Bool
  | [] => true
  | .space :: rest => onlyAlts cx rest
  | .ctrl n _ :: _ :: .group _ _ :: .group _ _ :: rest => isAltHead cx.userAlt n && onlyAlts cx rest
  | .ctrl n _ :: _ :: .space :: .group _ _ :: .space :: .group _ _ :: rest =>
    isAltHead cx.userAlt n && onlyAlts cx rest
  | _ :: _ => false

mutual

/-- Does `l` hold a list or table an alternation splits at an item, a cell, a
row, a rule or a block? -/
private def splitsList (cx : ReadCx) : List Raw → Bool
  | [] => false
  | r :: rest => splitsRaw cx r || splitsList cx rest

private def splitsRaw (cx : ReadCx) : Raw → Bool
  | .env n g _ =>
    if !readingEnvs.contains n || mathEnvs.contains n then false
    else
      ((listEnvs.contains n || tableEnvs.contains n) &&
        (topAlts cx g.toList).any fun (a, b) =>
          a.any (splitsAt n) || b.any (splitsAt n) || holdsBlock a || holdsBlock b) ||
      splitsList cx g.toList
  | .group g _ => splitsList cx g.toList
  | .math .. | .word .. | .space | .par _ | .ctrl .. | .sym .. | .verb .. => false

end

/-- A display formula holding an alternation it can read. -/
private def displayAlts (cx : ReadCx) : Raw → Bool
  | .math true g _ | .env _ g _ =>
    (altSpecs cx true (onlyAltList cx.userOnly true g.toList #[] 0).toList).any (!·.isEmpty)
  | .math false .. | .group .. | .word .. | .space | .par _ | .ctrl .. | .sym .. | .verb .. =>
    false

/-- Is a paragraph read per step: an alternation in it holds a block, splits a
list or table, or stands in a display — unless it is alternations alone,
each with content on both sides? -/
private def unitTrigger (cx : ReadCx) (run : Array Raw) : Bool :=
  let alts := topAlts cx run.toList
  let whole := onlyAlts cx run.toList && alts.all fun (a, b) => !readingEmpty a && !readingEmpty b
  (!whole && alts.any (fun (a, b) => holdsBlock a || holdsBlock b)) ||
    splitsList cx run.toList ||
    run.any (fun r => match r with
      | .env n _ _ => readableMathEnvs.contains n && displayAlts cx r
      | .math true .. => displayAlts cx r
      | .math false .. | .group .. | .word .. | .space | .par _ | .ctrl .. | .sym .. | .verb .. =>
        false)

/-- Is a paragraph alternations alone, one of them blank on some step? -/
private def emptyRun (cx : ReadCx) (run : Array Raw) : Bool :=
  onlyAlts cx run.toList &&
    (topAlts cx run.toList).any fun (a, b) => readingEmpty a || readingEmpty b

/-- A paragraph of a flow: its raws, each read alone, and the blank line after
it. -/
private structure ReadRun where
  orig : Array Raw := #[]
  done : Array Raw := #[]
  sep : Option Raw := none

/-- Runs `i` through `j`, joined by the blank lines between them. -/
private def runsRaws (runs : Array ReadRun) (i j : Nat) : Array Raw := Id.run do
  let mut out : Array Raw := #[]
  for (r, k) in runs.zipIdx do
    if i ≤ k && k ≤ j then
      out := out ++ r.orig
      if k < j then
        if let some s := r.sep then out := out.push s
  return out

/-- Does a unit read as nothing on some step its own selectors reach? -/
private def someEmpty (rd : Option Readings) : Bool :=
  rd.any fun r => r.steps.any fun (_, x) => readingEmpty x

private def blankRun (r : ReadRun) : Bool := r.orig.all (· matches .space)

/-- The alignment, size and face switches a unit may open on. -/
private def leadDeclarations : List String :=
  ["centering", "raggedleft", "raggedright", "RaggedLeft", "RaggedRight", "bfseries",
   "mdseries", "itshape", "slshape", "upshape", "scshape", "rmfamily", "sffamily", "ttfamily",
   "normalfont", "em", "bf", "it", "sl", "sc", "rm", "sf", "tt", "normalcolor"] ++
    Ir.sizeScale.map (·.1)

/-- How many raws a paragraph opens on are switches, colours and blank
space. -/
private def leadCount : List Raw → Nat
  | .space :: rest => leadCount rest + 1
  | .ctrl "color" _ :: .group _ _ :: rest => leadCount rest + 2
  | .ctrl n _ :: rest => if leadDeclarations.contains n then leadCount rest + 1 else 0
  | _ => 0

/-- A unit's opening switches, which stand before its readings, and the
rest. -/
private def unitParts (raws : Array Raw) : Array Raw × Array Raw :=
  let n := leadCount raws.toList
  (raws.extract 0 n, raws.extract n raws.size)

/-- The flow's units as run ranges: each run read per step, and an edge run
some step reads as nothing, widened over its neighbours until none does. -/
private def planUnits (cx : ReadCx) (runs : Array ReadRun) : Array (Nat × Nat) := Id.run do
  let n := runs.size
  let real := (List.range n).filter fun i => (runs[i]?.map (!blankRun ·)).getD false
  let firstReal := real.head?.getD 0
  let lastReal := real.getLast?.getD 0
  let mut segs : Array (Nat × Nat) := #[]
  let mut next := 0
  for (r, i) in runs.zipIdx do
    let strong := unitTrigger cx r.orig
    let edge := i == firstReal || i == lastReal
    if i < next || blankRun r || !(strong || (edge && emptyRun cx (unitParts r.orig).2)) then
      continue
    let mut j := i
    let mut rd := unitReadings cx (unitParts (runsRaws runs i i)).2
    if rd.isNone then continue
    if i == firstReal then
      for _ in [0:n] do
        if !someEmpty rd || j ≥ lastReal then break
        let wider := unitReadings cx (unitParts (runsRaws runs i (j + 1))).2
        if wider.isNone then break
        j := j + 1
        rd := wider
    let mut k := i
    if j ≥ lastReal then
      for _ in [0:n] do
        if !someEmpty rd || k ≤ max next firstReal then break
        let wider := unitReadings cx (unitParts (runsRaws runs (k - 1) j)).2
        if wider.isNone then break
        k := k - 1
        rd := wider
    if !strong && (someEmpty rd || (k == i && j == i)) then continue
    segs := segs.push (k, j)
    next := j + 1
  return segs

private def rawPos? : Raw → Option Pos
  | .word _ p | .par p | .ctrl _ p | .sym _ p | .group _ p | .math _ _ p | .env _ _ p
  | .verb _ _ p => some p
  | .space => none

/-- A flow of paragraphs, its units read per step, every other raw alone. -/
private def assembleFlow (cx : ReadCx) (runs : Array ReadRun) : Array Raw := Id.run do
  let segs := planUnits cx runs
  let mut out : Array Raw := #[]
  for (r, i) in runs.zipIdx do
    match segs.find? fun (k, j) => k ≤ i && i ≤ j with
    | some (k, j) =>
      if i == k then
        let (lead, raws) := unitParts (runsRaws runs k j)
        let p := (raws.findSome? rawPos?).getD {}
        let block (x : Array Raw) : Array Raw := if readingEmpty x then #[] else x.push (.par p)
        match unitReadings cx raws with
        | some rd =>
          let steps := rd.steps.map fun (k, x) => (k, block x)
          let blocked : Readings :=
            { most := rd.most, steps := steps, past := block rd.past, handout := block rd.handout }
          let chain := readingsChain p blocked
          out := out ++ lead ++ chain
        | none =>
          for (d, m) in runs.zipIdx do
            if k ≤ m && m ≤ j then
              out := out ++ d.done
              if m < j then
                if let some s := d.sep then out := out.push s
      if i == j then
        if let some s := r.sep then out := out.push s
    | none =>
      out := out ++ r.done
      if let some s := r.sep then out := out.push s
  return out

/-- Is a flow's opening raw one of its environment's arguments, with the state
after it? -/
private def leadStep (groups : Nat) (bracket : Bool) : Raw → Bool × Nat × Bool
  | .space => (true, groups, bracket)
  | .ctrl n _ =>
    if !bracket && (n == "frametitle" || n == "framesubtitle") then (true, 1, false)
    else (bracket, groups, bracket)
  | .sym '[' _ => (true, groups, true)
  | .sym ']' _ => (bracket, groups, false)
  | .word w _ => (bracket || (w.startsWith "<" && w.endsWith ">"), groups, bracket)
  | .group .. =>
    if bracket then (true, groups, bracket)
    else if groups > 0 then (true, groups - 1, false) else (false, groups, bracket)
  | .sym .. | .par _ | .math .. | .env .. | .verb .. => (bracket, groups, bracket)

mutual

/-- A list that is no flow of paragraphs, each raw read alone. -/
-- conserves: none — a surface boundary walk; no IR content has been elaborated.
private def readList (cx : ReadCx) : List Raw → Array Raw → Array Raw
  | [], out => out
  | r :: rest, out =>
    let rs := readRawAlone cx r
    readList cx rest (out ++ rs)

/-- A flow's arguments, then its runs split at blank lines. -/
private def flowRuns (cx : ReadCx) (lead : Bool) (groups : Nat) (bracket : Bool) :
    List Raw → Array Raw → Array ReadRun → ReadRun → Array Raw × Array ReadRun
  | [], pre, runs, cur => (pre, runs.push cur)
  | r :: rest, pre, runs, cur =>
    let (arg, groups', bracket') := leadStep groups bracket r
    if lead && arg then
      let rs := readRawAlone cx r
      flowRuns cx true groups' bracket' rest (pre ++ rs) runs cur
    else
      match r with
      | .par p => flowRuns cx false 0 false rest pre (runs.push { cur with sep := some (.par p) }) {}
      | .word .. | .space | .ctrl .. | .sym .. | .group .. | .math .. | .env .. | .verb .. =>
        let rs := readRawAlone cx r
        flowRuns cx false 0 false rest pre runs { cur with orig := cur.orig.push r, done := cur.done ++ rs }

/-- One raw read alone: a formula by its readings, a flow by its runs. -/
private def readRawAlone (cx : ReadCx) : Raw → Array Raw
  | .math d body p => formulaReadings cx (fun b => .math d b p) body (.math d body p) p
  | .env n body p =>
    if pictureBodies.contains n then #[.env n body p]
    else if readableMathEnvs.contains n then
      formulaReadings cx (fun b => .env n b p) body (.env n body p) p
    else if mathEnvs.contains n then #[.env n body p]
    else match flowEnvArgs.lookup n with
      | some groups =>
        let (pre, runs) := flowRuns cx true groups false body.toList #[] #[] {}
        #[.env n (pre ++ assembleFlow cx runs) p]
      | none => #[.env n (readList cx body.toList #[]) p]
  | .group body p => #[.group (readList cx body.toList #[]) p]
  | .word w p => #[.word w p]
  | .space => #[.space]
  | .par p => #[.par p]
  | .ctrl n p => #[.ctrl n p]
  | .sym c p => #[.sym c p]
  | .verb env s p => #[.verb env s p]

end

private def onlyAlternationsIn (cx : ReadCx) (raws : Array Raw) : Array Raw :=
  readList cx (onlyAltList cx.userOnly false raws.toList #[] 0).toList #[]

private def readCxOf (raws : Array Raw) : ReadCx :=
  { userOnly := definesList "only" raws.toList, userAlt := definesList "alt" raws.toList }

/-- `\only<s>{x}` as beamer's `\alt<s>{x}{}`, and every alternation read per
step where its node alone cannot be exact. -/
public def onlyAlternations (raws : Array Raw) : Array Raw :=
  onlyAlternationsIn (readCxOf raws) raws

/-- A scope's trailing length metadata, unforgeable because it holds a space. -/
public def lengthRestoreKeys? (name : String) : Option (Array String) :=
  let mark := "length restore "
  if name.startsWith mark then
    some ((name.drop mark.length).toString.splitOn ",").toArray
  else none

/-- The assignments to restore at a group's close, carried as names. -/
private def restoreLengths (keys : Array String) (p : Pos) : Array Raw :=
  if keys.isEmpty then #[]
  else #[.ctrl ("length restore " ++ String.intercalate "," keys.toList) p]

/-- Names an abstract an article's titlepage would set on a page of its own. -/
private def abstractUnderTitlePage (pos : Pos) : M Unit := do
  -- premise: titlePageChecks — under an article's titlepage the abstract stands in the text
  if (← get).titlePageAsked && !(← get).inDef then
    sayOnce "partial:\\documentclass:titlepage:abstract" .W0110
      "the abstract is set in the text, where class option 'titlepage' gives it a page of its own"
      pos (help := "\\begin{titlepage}...\\end{titlepage} sets a page of its own")

mutual

/-- Pushes one raw's rewrite, keeping a rewritten environment's group apart from
the output before it. -/
private def pushRewritten (out : Array Raw) (r r' : Raw) : Array Raw :=
  match r, r' with
  | .env _ _ p, .group _ _ =>
    if Parse.endsInArgument out then (out.push (.env Parse.scopeEnv #[] p)).push r'
    else out.push r'
  | _, _ => out.push r'

/-- The rewrite walk over `raws` from index `i`; `skip` counts elements a
rewrite already consumed. -/
-- conserves: none — the rewrite walk's job is replacement
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
    -- Pictures may leave through the TeX boundary, so native markers keep their source here.
    let rewritten : Option (Array Raw × Nat) ← if inPicture then do
        if overlayName name == "alert" &&
            (raws[skipSpaces raws (i + 1)]?.bind overlayWord?).isNone then
          pure ((← alertPlain pos raws (i + 1) (picture := true)).map fun (repl, j) =>
            (repl, j - (i + 1)))
        else pure none
      else rewriteCtrl (overlayName name) pos raws (i + 1)
    match rewritten with
    | some (repl, consumed) => rewriteList inBody raws (out ++ repl) rest (i + 1) consumed
    | none =>
      let name := if inPicture || overlayName name == "item" then overlayName name else name
      rewriteList inBody raws (out.push (.ctrl name pos)) rest (i + 1) 0
  -- `#k` is the native parameter `\ak`; outside a body `#` is literal.
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
    rewriteList inBody raws (pushRewritten out r (← rewriteRaw inBody (argGroupAt out) r)) rest
      (i + 1) 0

/-- Descends into a group or environment; `arg` when the group is a control word's argument. -/
private def rewriteRaw (inBody : Bool) (arg : Bool) : Raw → M Raw
  | .group body p => withGroupScope arg fun inDefault outer => do
    if (← get).inPicture then
      return .group (← rewriteList inBody body #[] body.toList 0 0) p
    -- A group is a macro body when a definition announced one.
    let saved := if inDefault then 0 else outer
    let savedDef := (← get).inDef
    let savedGroup := (← get).inGroup
    let savedLens := (← get).lens
    let savedLengths := (← get).localLengths
    let savedTop := (← get).tableTop
    let savedDefTop := (← get).defTop
    let savedBound := (← get).bound
    let savedCaptures := (← get).beamerCaptures
    let envBody := saved > 0 && (← get).envNext > 0
    let (savedEnvCode, savedEnvNext) := ((← get).envCode, (← get).envNext)
    -- premise: templateCodeChecks — a template macro names its losses at its use
    let quiet := saved > 0 && (← get).quietNext
    let (said, warned) := ((← get).diags.size, (← get).warned)
    write fun st => { st with bodyNext := 0, inDef := st.inDef || saved > 0, inGroup := true,
                              tableTop := false, defTop := saved > 0, localLengths := #[]
                              quietNext := false, envCode := st.envCode || envBody, envNext := 0 }
    let body' ← rewriteList (inBody || saved > 0) body #[] body.toList 0 0
    if quiet then
      write fun st => { st with diags := st.diags.extract 0 said, warned := warned }
    let restores := restoreLengths (← get).localLengths p
    -- A group's assignments end with it.
    write fun st => { st with bodyNext := if inDefault then outer else saved - 1, inDef := savedDef,
                              inGroup := savedGroup, envCode := savedEnvCode,
                              envNext := if envBody then savedEnvNext - 1 else savedEnvNext,
                              lens := savedLens, localLengths := savedLengths,
                              tableTop := savedTop, defTop := savedDefTop,
                              bound := if saved > 0 then savedBound else st.bound }
    -- premise: beamerTemplateChecks — a consumed local font declaration leaves no preamble content
    if (← get).wholeDoc && !(← get).inDoc && !savedDef && saved == 0 &&
        (← get).beamerCaptures > savedCaptures && !body.all (· == .space) &&
        restores.isEmpty && body'.all (· == .space) then
      return .space
    return .group (body' ++ restores) p
  | .env n body p => do
    match Parse.inputEnvFile? n with
    | some f =>
      let saved := (← get).file
      write fun st => { st with file := f }
      let body' ← rewriteList inBody body #[] body.toList 0 0
      write fun st => { st with file := saved }
      return .env n body' p
    | none => withScope do
      if n == "abstract" then abstractUnderTitlePage p
      if mathEnvs.contains n then
        return .env n body p
      -- premise: pictureBoundaryChecks — requests retain TeX commands
      else if (← get).inPicture || pictureEnvs.contains n then
        let saved := (← get).inPicture
        write fun st => { st with inPicture := true }
        let body' ← rewriteList inBody body #[] body.toList 0 0
        write fun st => { st with inPicture := saved }
        return .env n body' p
      else if n == "otherlanguage" || n == "otherlanguage*" then
        let held ← paramArgs (takeGroups body 0 1).1
        let savedTop := (← get).tableTop
        let savedDefTop := (← get).defTop
        write fun st => { st with tableTop := false, defTop := false }
        let body' ← rewriteList inBody body #[] body.toList 0 0
        write fun st => { st with tableTop := savedTop, defTop := savedDefTop }
        let (langArg, j) := takeGroups body' 0 1
        if held then
          unappliedParam s!"begin\{{n}}" "its text keeps the language in force" p
          return .group (body'.extract j body'.size) p
        let lname := rawSrc (langArg.getD 0 #[])
        let tag := Locale.babelTagOf lname
        if (Locale.forTag tag).isNone then
          say .W0368 s!"no locale for language '{lname}'; English captions \
and patterns stand in" p
            (help := Locale.shippedHelp)
        became s!"\\begin\{{n}}\{{lname}}" s!"the '{tag}' language attribute" p
        return .group (#[Raw.ctrl (Marker.name .lang tag) p] ++ body'.extract j body'.size) p
      else if n == "document" then
        rewriteDocumentBody (rewriteList inBody body #[] body.toList 0 0) p
      else if n == "frame" then
        -- A frame's `<spec>`, `[opts]` and `{title}` arrive at the head of its body, spec first.
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
        -- article.cls's `titlepage` opens a fresh unstyled page and resets the page to one.
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
      -- premise: environScopeChecks — only a name nothing defines registers a body definition
      else if let some (spec, discards) := ((← get).refusedEnvs.find? (·.1 == n)).map (·.2) then
        -- An unapplied body definition's use sets its arguments and body plainly, or nothing.
        if discards then return .group #[] p
        sayOnce ("env:" ++ n) .W0302 s!"unknown environment '\{{n}}'; its body is kept" p
          (help := bodyEnvDefHelp)
        let body' ← rewriteList inBody body #[] body.toList 0 0
        let (args, k) := plainArgs spec body'
        return .group (args ++ body'.extract k body'.size) p
      else if let some spec := ((← get).discardEnvs.find? (·.1 == n)).map (·.2) then
        -- environ's discarding environment keeps only the arguments its signature reads.
        let k := spec.foldl (fun k c =>
          if c == 'o' then (takeOpt body k).2 else (takeGroups body k 1).2) 0
        return .env n (body.extract 0 k) p
      else
        -- An environment is a group, so a length set inside it ends with it.
        let st0 ← get
        write fun st => { st with inList := st.inList || listEnvs.contains n,
                                  tableTop := tableEnvs.contains n, defTop := false,
                                  inParacol := n == "paracol", localLengths := #[] }
        let body' ← rewriteList inBody body #[] body.toList 0 0
        let body' ← if listEnvs.contains n then listOptions n body' p else pure body'
        let restores := restoreLengths (← get).localLengths p
        write fun st => { st with lens := st0.lens, localLengths := st0.localLengths,
                                  inList := st0.inList,
                                  tableTop := st0.tableTop, defTop := st0.defTop,
                                  inParacol := st0.inParacol }
        if n == "paracol" then
          paracolEnv st0.paracolRatio body' p restores
        else return .env n (body' ++ restores) p
  | .sym '[' p => do
    if (← get).defaultAt == .awaiting then
      write fun st => { st with defaultAt := .inside st.inDef, inDef := true }
    pure (.sym '[' p)
  | .sym ']' p => do
    if let .inside outerDef := (← get).defaultAt then
      write fun st => { st with defaultAt := .none, inDef := outerDef }
    pure (.sym ']' p)
  | r => pure r

end

private theorem rewriteCtrlAt_named_scope (name : String) (pos : Pos)
    (raws : Array Raw) (start : Nat) (s : St)
    (hd : (s.wholeDoc && s.deck && !s.inDoc && !s.inDef) = false)
    (hl : St.inList s = false)
    (hCite : (name == "cite") = false)
    (hAppendix : (name == "appendix") = false)
    (hAssign : plainAssign? name raws start = none)
    (hRow : ctrlRow? name = none) :
    rewriteCtrl.rewriteCtrlAt name pos raws start s =
      rewriteCtrlNamed name pos raws start s := by
  have hSettings : listSettings? s name = none := by
    simp [listSettings?, hl]
  simp only [rewriteCtrl.rewriteCtrlAt]
  simp [bind, StateT.bind, pure, get, getThe, MonadStateOf.get,
    StateT.get, hd, hCite, hAppendix, hAssign, hSettings, hRow]

/-- A name's bytes, the order the control table is sorted in. -/
public def nameKey (n : String) : List Nat := n.toByteArray.data.toList.map UInt8.toNat

/-- Whether each name's bytes sort strictly before the next one's. -/
public def bytesAscending : List String → Bool
  | a :: b :: rest => decide (nameKey a < nameKey b) && bytesAscending (b :: rest)
  | _ => true

/-- The table's names stand in strictly ascending byte order; none is `\cite` or `\appendix`, which
a body's dispatch reads before the table, or the walk's own `\define` head; and none is spelled as a
saved overlay-native name. -/
public def CtrlRowsSound : Prop :=
  bytesAscending (ctrlRows.map (·.name)) = true ∧
    ∀ row ∈ ctrlRows, row.name ∉ ["cite", "appendix", "define"] ∧
      ¬ ("overlay native ".toByteArray.data.toList <+: row.name.toByteArray.data.toList)

private theorem ascending_pairwise : ∀ names : List String, bytesAscending names = true →
    names.Pairwise (fun a b => nameKey a < nameKey b)
  | [], _ => .nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [bytesAscending, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := ascending_pairwise (b :: rest) h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact List.lt_trans h.1 ((List.pairwise_cons.mp ih).1 c hc)

private theorem ctrlRows_nodup (hsound : CtrlRowsSound) : (ctrlRows.map (·.name)).Nodup := by
  unfold List.Nodup
  refine (ascending_pairwise _ hsound.1).imp fun {a b} h he => ?_
  subst he
  exact List.lt_irrefl _ h

private theorem find_row_exact (rows : List CtrlRow) (row : CtrlRow) (h : row ∈ rows)
    (hnd : (rows.map (·.name)).Nodup) : rows.find? (·.name == row.name) = some row := by
  induction rows with
  | nil => simp at h
  | cons r rs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have hne : (r.name == row.name) = false := by
        rw [beq_eq_false_iff_ne]
        intro he
        exact hnd.1 (he ▸ List.mem_map_of_mem h)
      rw [List.find?_cons, hne]
      exact ih h hnd.2

private theorem overlayName_unsaved (n : String)
    (h : ¬ ("overlay native ".toByteArray.data.toList <+: n.toByteArray.data.toList)) :
    overlayName n = n := by
  unfold overlayName
  split
  · rename_i hs
    rw [String.startsWith_string_iff] at hs
    obtain ⟨u, hu⟩ := hs
    have hn : n = "overlay native " ++ String.ofList u := by
      apply String.ext
      rw [← hu]
      simp [String.toList_append]
    exact absurd ⟨(String.ofList u).toByteArray.data.toList, by
      rw [hn, String.toByteArray_append, ByteArray.toList_data_append]⟩ h
  · rfl

private theorem ctrlRow_names (hsound : CtrlRowsSound) (row : CtrlRow) (hrow : row ∈ ctrlRows) :
    ctrlRow? row.name = some row ∧ (row.name == "cite") = false ∧
      (row.name == "appendix") = false ∧ row.name ≠ "define" ∧ overlayName row.name = row.name := by
  obtain ⟨hnames, hsaved⟩ := hsound.2 row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnames
  exact ⟨find_row_exact ctrlRows row hrow (ctrlRows_nodup hsound), beq_false_of_ne hnames.1,
    beq_false_of_ne hnames.2.1, hnames.2.2, overlayName_unsaved row.name hsaved⟩

/-- Whether a row's action emits nothing, its report its whole effect. -/
@[expose] public def CtrlAction.silent : CtrlAction → Bool
  | .refuse .. | .discard .. | .inert => true
  | .tokens .. | .native .. | .skip _ | .lower .. => false

/-- Whether a row's action may read its arguments. -/
@[expose] public def CtrlAction.reads : CtrlAction → Bool
  | .lower .. => true
  | .tokens .. | .native .. | .skip _ | .refuse .. | .discard .. | .inert => false

private theorem ctrlRowRun_silent (row : CtrlRow) (c : CtrlCall) (s : St)
    (h : row.action.silent = true) : (ctrlRowRun row c s).1 = #[] := by
  rcases row with ⟨name, sig, action⟩
  cases action with
  | refuse code key msg help =>
    cases key <;> rfl
  | discard why key => rfl
  | inert => rfl
  | tokens toks note => simp [CtrlAction.silent] at h
  | native src => simp [CtrlAction.silent] at h
  | skip amount => simp [CtrlAction.silent] at h
  | lower l gates => simp [CtrlAction.silent] at h

private theorem ctrlRowRun_fixed (row : CtrlRow) (c c' : CtrlCall) (h : row.action.reads = false)
    (hpos : c.pos = c'.pos) : ctrlRowRun row c = ctrlRowRun row c' := by
  rcases c with ⟨n, p, a, r, i, j⟩
  rcases c' with ⟨n', p', a', r', i', j'⟩
  simp only at hpos
  subst hpos
  rcases row with ⟨name, sig, action⟩
  cases action
  case refuse code key msg help => cases key <;> rfl
  all_goals first | rfl | simp [CtrlAction.reads] at h

private theorem ctrlLeft_fixed (row : CtrlRow) (s : St) (args : Array (Option (Array Raw)))
    (h : row.action.reads = false) : ctrlLeft s row args = false := by
  rcases row with ⟨name, sig, action⟩
  cases action <;> first | rfl | simp [CtrlAction.reads] at h

private theorem silent_fixed (action : CtrlAction) (h : action.silent = true) :
    action.reads = false := by
  cases action <;> simp_all [CtrlAction.silent, CtrlAction.reads]

private theorem ctrlRowRun_declared (row : CtrlRow) (c : CtrlCall) (s : St) (l : Lowering)
    (g : CtrlGates) (help : String) (hact : row.action = .lower l g)
    (hh : g.bodyHelp = some help) (hd : s.inDoc = true) : (ctrlRowRun row c s).1 = #[] := by
  rcases row with ⟨name, sig, action⟩
  simp only at hact
  subst hact
  rcases g with ⟨leaves, stands, bodyHelp⟩
  simp only at hh
  subst hh
  cases stands with
  | none =>
    simp only [ctrlRowRun, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      StateT.pure, hd, ↓reduceIte]
    rfl
  | some w =>
    simp only [ctrlRowRun, paramArgs, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure]
    split
    · rfl
    · simp [StateT.bind, StateT.get, StateT.pure, hd]
      rfl

/-- Whether a row is known to emit nothing at a body cursor: a silent row, or a declaration the body
ignores whose row keeps it nowhere. -/
@[expose] public def CtrlRow.quiet (row : CtrlRow) : Bool :=
  match row.action with
  | .lower _ g => g.bodyHelp.isSome && g.leaves.isEmpty
  | .tokens .. | .native .. | .skip _ | .refuse .. | .discard .. | .inert => row.action.silent

private theorem ctrlRowRun_quiet (row : CtrlRow) (c : CtrlCall) (s : St)
    (hq : row.quiet = true) (hd : s.inDoc = true) : (ctrlRowRun row c s).1 = #[] := by
  rcases row with ⟨name, sig, action⟩
  cases action with
  | lower l g =>
    simp only [CtrlRow.quiet, Bool.and_eq_true, Option.isSome_iff_exists] at hq
    obtain ⟨⟨help, hh⟩, _⟩ := hq
    exact ctrlRowRun_declared _ c s l g help rfl hh hd
  | _ => exact ctrlRowRun_silent _ c s (by simpa [CtrlRow.quiet] using hq)

private theorem ctrlLeft_quiet (row : CtrlRow) (s : St) (args : Array (Option (Array Raw)))
    (hq : row.quiet = true) : ctrlLeft s row args = false := by
  rcases row with ⟨name, sig, action⟩
  cases action with
  | lower l g =>
    simp only [CtrlRow.quiet, Bool.and_eq_true, List.isEmpty_iff] at hq
    simp [ctrlLeft, hq.2]
  | _ => rfl

/-- The state a row's control leaves: its action's report and writes, with the dispatcher's guard
where it emits nothing. -/
private def ctrlRowState (s : St) (row : CtrlRow) (c : CtrlCall) : St :=
  if (ctrlRowRun row c s).1.isEmpty then (account row.name c.pos s (ctrlRowRun row c s).2).2
  else (ctrlRowRun row c s).2

private theorem rewriteCtrlAt_found (row : CtrlRow) (hfind : ctrlRow? row.name = some row)
    (hCite : (row.name == "cite") = false) (hAppendix : (row.name == "appendix") = false)
    (pos : Pos) (raws : Array Raw) (start : Nat) (s : St)
    (hd : (s.wholeDoc && s.deck && !s.inDoc && !s.inDef) = false) :
    rewriteCtrl.rewriteCtrlAt row.name pos raws start s =
      match argsRead raws #[] row.sig start with
      | some (args, k) =>
        if ctrlLeft s row args then (none, s)
        else (some ((ctrlRowRun row ⟨row.name, pos, args, raws, start, k⟩ s).1, k),
          (ctrlRowRun row ⟨row.name, pos, args, raws, start, k⟩ s).2)
      | none => (none, s) := by
  simp only [rewriteCtrl.rewriteCtrlAt]
  cases hk : argsRead raws #[] row.sig start with
  | none =>
    simp [bind, StateT.bind, pure, get, getThe, MonadStateOf.get, StateT.get, hd, hCite,
      hAppendix, hfind, hk]
    rfl
  | some r =>
    obtain ⟨args, k⟩ := r
    cases hl : ctrlLeft s row args with
    | true =>
      simp [bind, StateT.bind, pure, get, getThe, MonadStateOf.get, StateT.get, hd, hCite,
        hAppendix, hfind, hk, hl]
      rfl
    | false =>
      simp [bind, StateT.bind, pure, get, getThe, MonadStateOf.get, StateT.get, hd, hCite,
        hAppendix, hfind, hk, hl]
      cases ctrlRowRun row ⟨row.name, pos, args, raws, start, k⟩ s
      rfl

private theorem rewriteCtrlAt_row (hsound : CtrlRowsSound) (row : CtrlRow) (hrow : row ∈ ctrlRows)
    (pos : Pos) (raws : Array Raw) (start : Nat) (s : St)
    (hd : (s.wholeDoc && s.deck && !s.inDoc && !s.inDef) = false) :
    rewriteCtrl.rewriteCtrlAt row.name pos raws start s =
      match argsRead raws #[] row.sig start with
      | some (args, k) =>
        if ctrlLeft s row args then (none, s)
        else (some ((ctrlRowRun row ⟨row.name, pos, args, raws, start, k⟩ s).1, k),
          (ctrlRowRun row ⟨row.name, pos, args, raws, start, k⟩ s).2)
      | none => (none, s) := by
  obtain ⟨hfind, hCite, hAppendix, _, _⟩ := ctrlRow_names hsound row hrow
  exact rewriteCtrlAt_found row hfind hCite hAppendix pos raws start s hd

private theorem rewriteCtrl_found_exact (row : CtrlRow) (hfind : ctrlRow? row.name = some row)
    (hCite : (row.name == "cite") = false) (hAppendix : (row.name == "appendix") = false)
    (pos : Pos) (raws : Array Raw) (start k : Nat) (s : St) (args : Array (Option (Array Raw)))
    (hd : (s.wholeDoc && s.deck && !s.inDoc && !s.inDef) = false)
    (hk : argsRead raws #[] row.sig start = some (args, k))
    (hl : ctrlLeft s row args = false) :
    rewriteCtrl row.name pos raws start s =
      (some ((ctrlRowRun row ⟨row.name, pos, args, raws, start, k⟩ s).1, k - start),
        ctrlRowState s row ⟨row.name, pos, args, raws, start, k⟩) := by
  unfold rewriteCtrl
  rw [rewriteCtrlAt_found row hfind hCite hAppendix pos raws start s hd, hk]
  simp only [hl, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem rewriteCtrl_row_exact (hsound : CtrlRowsSound) (row : CtrlRow)
    (hrow : row ∈ ctrlRows) (pos : Pos) (raws : Array Raw) (start k : Nat) (s : St)
    (args : Array (Option (Array Raw)))
    (hd : (s.wholeDoc && s.deck && !s.inDoc && !s.inDef) = false)
    (hk : argsRead raws #[] row.sig start = some (args, k))
    (hl : ctrlLeft s row args = false) :
    rewriteCtrl row.name pos raws start s =
      (some ((ctrlRowRun row ⟨row.name, pos, args, raws, start, k⟩ s).1, k - start),
        ctrlRowState s row ⟨row.name, pos, args, raws, start, k⟩) := by
  obtain ⟨hfind, hCite, hAppendix, _, _⟩ := ctrlRow_names hsound row hrow
  exact rewriteCtrl_found_exact row hfind hCite hAppendix pos raws start k s args hd hk hl

/-- At a body cursor, or a preamble one outside a deck, a row's control whose signature finds an
argument that must stand missing, or that a leave of its row holds for, is left with the state to
elaboration. -/
public def CtrlRowDeclines (row : CtrlRow) : Prop :=
  ∀ (pos : Pos) (raws : Array Raw) (start : Nat) (s : St),
    (St.wholeDoc s && St.deck s && !St.inDoc s && !St.inDef s) = false →
    (argsRead raws #[] row.sig start = none ∨
      ∃ args k, argsRead raws #[] row.sig start = some (args, k) ∧
        ctrlLeft s row args = true) →
    rewriteCtrl row.name pos raws start s = (none, s)

public theorem ctrlRow_declines_contract (hsound : CtrlRowsSound) (row : CtrlRow)
    (hrow : row ∈ ctrlRows) : CtrlRowDeclines row := by
  intro pos raws start s hd h
  unfold rewriteCtrl
  rw [rewriteCtrlAt_row hsound row hrow pos raws start s hd]
  rcases h with hk | ⟨args, k, hk, hl⟩
  · rw [hk]
  · rw [hk]
    simp only [hl, ↓reduceIte]

private theorem packageCall_args (command names : String) (pos groupPos namePos : Pos) :
    argsRead (packageCall command names pos groupPos namePos) #[] [.opt, .needed] 1 =
      some (#[none, some #[.word names namePos]], 2) := by
  have hs := (packageCall_readers command names pos groupPos namePos).1
  have hopt : takeRawOpt (packageCall command names pos groupPos namePos) 1 = (none, 1) := by
    simp only [takeRawOpt, hs, Id.run]
    simp [packageCall]
  simp only [argsRead, hopt, (packageCall_readers command names pos groupPos namePos).2.2]
  rfl

private theorem rewriteCtrl_package_external_exact
    (command names : String) (pos gp np : Pos) (st : St)
    (hc : command = "usepackage" ∨ command = "RequirePackage")
    (hrow : ctrlRow? command = some (packageRow command))
    (hd : st.inDoc = false) (hdef : st.inDef = false) (hw : st.wholeDoc = false)
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
  have hsrc : rawSrc #[Raw.word names np] = names.trimAscii.toString := by
    simp [rawSrc, rawSrcList, rawSrcOne]
  have hpkgs := rewritePackages_external_exact command
    ((names.trimAscii.toString.splitOn ",").map (·.trimAscii.toString)) none #[] pos st hn hb ht
  have hstep := rewriteCtrl_found_exact (packageRow command) hrow
    (by rcases hc with rfl | rfl <;> rfl) (by rcases hc with rfl | rfl <;> rfl)
    pos (packageCall command names pos gp np) 1 2 st _ (by simp [hw])
    (packageCall_args command names pos gp np)
    (by simp [ctrlLeft, packageRow, CtrlLeave.holds, hdef])
  have hname : (packageRow command).name = command := rfl
  rw [hname] at hstep
  have hlower : ctrlRowRun (packageRow command)
      ⟨command, pos, #[none, some #[.word names np]], packageCall command names pos gp np, 1, 2⟩
      st = rewritePackages command
        ((names.trimAscii.toString.splitOn ",").map (·.trimAscii.toString)) none #[] pos st := by
    simp [ctrlRowRun, packageRow, lowerCall, CtrlCall.src, CtrlCall.arg, CtrlCall.given,
      CtrlCall.optSrc, bind, StateT.bind, pure, get, getThe, MonadStateOf.get, StateT.get, hd,
      hsrc]
  rw [hstep]
  simp only [ctrlRowState, hlower, hpkgs, Array.isEmpty_empty, ↓reduceIte, account, List.map_map,
    Function.comp_def]
  rw [ite_eq_left (Or.inl hsize)]

private theorem rewriteCtrl_unknown_exact (s : St) (pos : Pos)
    (raws : Array Raw) (start : Nat) (hz : ctrlRow? "zzNotAControl" = none)
    (hd : St.inDoc s = true) (hl : St.inList s = false) :
    rewriteCtrl "zzNotAControl" pos raws start s = (none, s) := by
  have hAt : rewriteCtrl.rewriteCtrlAt "zzNotAControl" pos raws start s = (none, s) := by
    rw [rewriteCtrlAt_named_scope "zzNotAControl" pos raws start s (by simp [hd]) hl
      rfl rfl rfl hz]
    rfl
  unfold rewriteCtrl
  rw [hAt]

private theorem rewriteList_skip_exact (inBody : Bool) (raws out : Array Raw)
    (taken rest : List Raw) (i : Nat) :
    rewriteList inBody raws out (taken ++ rest) i taken.length =
      rewriteList inBody raws out rest (i + taken.length) 0 := by
  induction taken generalizing i with
  | nil => simp
  | cons x taken ih =>
    simp only [List.cons_append, List.length_cons]
    rw [rewriteList, ih]
    congr 1; omega

/-- Literal material surrounding an ordinary body control. -/
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

private theorem rewriteList_unknown_exact (inBody : Bool) (raws out : Array Raw)
    (pos : Pos) (rest : List Raw) (i : Nat) (s : St) (hz : ctrlRow? "zzNotAControl" = none)
    (hd : St.inDoc s = true) (hl : St.inList s = false) (hp : St.inPicture s = false) :
    rewriteList inBody raws out (.ctrl "zzNotAControl" pos :: rest) i 0 s =
      rewriteList inBody raws (out.push (.ctrl "zzNotAControl" pos)) rest (i + 1) 0 s := by
  rw [rewriteList]
  case x_3 => simp
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, hp, Bool.false_eq_true, ↓reduceIte]
  have hoverlay : overlayName "zzNotAControl" = "zzNotAControl" := by
    simp [overlayName, String.startsWith_string_iff]
  rw [hoverlay, rewriteCtrl_unknown_exact s pos raws (i + 1) hz hd hl]
  rfl

private theorem rewriteList_control_exact (inBody : Bool) (raws out repl : Array Raw)
    (name : String) (pos : Pos) (taken rest : List Raw) (i : Nat) (s s' : St)
    (hdef : name ≠ "define") (hpic : St.inPicture s = false)
    (hstep : rewriteCtrl (overlayName name) pos raws (i + 1) s =
      (some (repl, taken.length), s')) :
    rewriteList inBody raws out (.ctrl name pos :: (taken ++ rest)) i 0 s =
      rewriteList inBody raws (out ++ repl) rest (i + 1 + taken.length) 0 s' := by
  rw [rewriteList]
  case x_3 => exact fun h => hdef h
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, hpic, Bool.false_eq_true, ↓reduceIte, hstep]
  rw [rewriteList_skip_exact]

private theorem rewriteList_package_external_exact
    (command names : String) (pos gp np : Pos) (st : St)
    (hc : command = "usepackage" ∨ command = "RequirePackage")
    (hrow : ctrlRow? command = some (packageRow command))
    (hd : st.inDoc = false) (hf : st.inDef = false) (hw : st.wholeDoc = false)
    (hpic : st.inPicture = false)
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
    hc hrow hd hf hw hn hb ht part hp
  have h := rewriteList_control_exact false (packageCall command names pos gp np) #[] #[]
    command pos [.group #[.word names np] gp] [] 0 st _ hdef hpic
    (by simpa only [ho, Nat.zero_add, List.length_cons, List.length_nil] using hstep)
  rw [Array.empty_append] at h
  exact h

private theorem rewriteList_row_exact (hsound : CtrlRowsSound) (inBody : Bool)
    (raws out : Array Raw) (row : CtrlRow) (hrow : row ∈ ctrlRows) (pos : Pos)
    (args : Array (Option (Array Raw))) (taken rest : List Raw) (i : Nat) (s : St)
    (hd : (s.wholeDoc && s.deck && !s.inDoc && !s.inDef) = false) (hp : s.inPicture = false)
    (hk : argsRead raws #[] row.sig (i + 1) = some (args, i + 1 + taken.length))
    (hl : ctrlLeft s row args = false) :
    rewriteCtrl row.name pos raws (i + 1) s =
      (some ((ctrlRowRun row ⟨row.name, pos, args, raws, i + 1, i + 1 + taken.length⟩ s).1,
        taken.length), ctrlRowState s row ⟨row.name, pos, args, raws, i + 1, i + 1 + taken.length⟩) ∧
    rewriteList inBody raws out (.ctrl row.name pos :: (taken ++ rest)) i 0 s =
      rewriteList inBody raws
        (out ++ (ctrlRowRun row ⟨row.name, pos, args, raws, i + 1, i + 1 + taken.length⟩ s).1)
        rest (i + 1 + taken.length) 0
        (ctrlRowState s row ⟨row.name, pos, args, raws, i + 1, i + 1 + taken.length⟩) := by
  have hstep := rewriteCtrl_row_exact hsound row hrow pos raws (i + 1) (i + 1 + taken.length) s
    args hd hk hl
  rw [Nat.add_sub_cancel_left] at hstep
  obtain ⟨_, _, _, hdef, hoverlay⟩ := ctrlRow_names hsound row hrow
  refine ⟨hstep, ?_⟩
  apply rewriteList_control_exact inBody raws out _ row.name pos taken rest i s _ hdef hp
  rw [hoverlay]
  exact hstep

private theorem rewriteList_row_body_exact (hsound : CtrlRowsSound) (inBody : Bool)
    (raws out : Array Raw) (row : CtrlRow) (hrow : row ∈ ctrlRows) (pos : Pos)
    (args : Array (Option (Array Raw))) (pre taken post : List Raw) (i : Nat) (s : St)
    (hd : (s.wholeDoc && s.deck && !s.inDoc && !s.inDef) = false) (hp : s.inPicture = false)
    (hpre : LiteralRaws pre) (hpost : LiteralRaws post)
    (hk : argsRead raws #[] row.sig (i + pre.length + 1) =
      some (args, i + pre.length + 1 + taken.length))
    (hl : ctrlLeft s row args = false) :
    rewriteList inBody raws out (pre ++ .ctrl row.name pos :: (taken ++ post)) i 0 s =
      (out ++ pre.toArray ++ (ctrlRowRun row
          ⟨row.name, pos, args, raws, i + pre.length + 1, i + pre.length + 1 + taken.length⟩ s).1 ++
        post.toArray, ctrlRowState s row
          ⟨row.name, pos, args, raws, i + pre.length + 1, i + pre.length + 1 + taken.length⟩) := by
  rw [rewriteList_literal_prefix _ _ _ _ _ _ hpre,
    (rewriteList_row_exact hsound inBody raws (out ++ pre.toArray) row hrow pos args taken post
      (i + pre.length) s hd hp hk hl).2,
    rewriteList_literal_exact _ _ _ _ _ _ hpost]

/-- At a body cursor, or a preamble one outside a deck, a row's control its leaves do not keep
consumes exactly what its signature reads there: its emission takes its place, the walk resumes
where the reading stops, and a silent row emits nothing and is paid for. -/
public def CtrlRowConsumed (row : CtrlRow) : Prop :=
  ∀ (inBody : Bool) (raws out : Array Raw) (pos : Pos) (args : Array (Option (Array Raw)))
    (taken rest : List Raw) (i : Nat) (s : St),
    (St.wholeDoc s && St.deck s && !St.inDoc s && !St.inDef s) = false →
    St.inPicture s = false →
    raws.toList.drop i = .ctrl row.name pos :: (taken ++ rest) →
    argsRead raws #[] row.sig (i + 1) = some (args, i + 1 + taken.length) →
    ctrlLeft s row args = false →
    rewriteCtrl row.name pos raws (i + 1) s =
      (some ((ctrlRowRun row ⟨row.name, pos, args, raws, i + 1, i + 1 + taken.length⟩ s).1,
        taken.length), ctrlRowState s row ⟨row.name, pos, args, raws, i + 1, i + 1 + taken.length⟩) ∧
    rewriteList inBody raws out (raws.toList.drop i) i 0 s =
      rewriteList inBody raws
        (out ++ (ctrlRowRun row ⟨row.name, pos, args, raws, i + 1, i + 1 + taken.length⟩ s).1)
        rest (i + 1 + taken.length) 0
        (ctrlRowState s row ⟨row.name, pos, args, raws, i + 1, i + 1 + taken.length⟩) ∧
    (row.action.silent = true →
      (ctrlRowRun row ⟨row.name, pos, args, raws, i + 1, i + 1 + taken.length⟩ s).1 = #[] ∧
      ((St.diags (ctrlRowState s row
          ⟨row.name, pos, args, raws, i + 1, i + 1 + taken.length⟩)).size > (St.diags s).size ∨
        St.writes (ctrlRowState s row ⟨row.name, pos, args, raws, i + 1, i + 1 + taken.length⟩) >
          St.writes s))

public theorem ctrlRow_control_contract (hsound : CtrlRowsSound) (row : CtrlRow)
    (hrow : row ∈ ctrlRows) : CtrlRowConsumed row := by
  intro inBody raws out pos args taken rest i s hd hp hsource hk hl
  obtain ⟨hstep, hwalk⟩ := rewriteList_row_exact hsound inBody raws out row hrow pos args taken
    rest i s hd hp hk hl
  refine ⟨hstep, by rw [hsource]; exact hwalk, fun hsilent => ?_⟩
  have hempty := ctrlRowRun_silent row ⟨row.name, pos, args, raws, i + 1, i + 1 + taken.length⟩
    s hsilent
  refine ⟨hempty, ?_⟩
  rw [hempty] at hstep
  exact rewriteCtrl_accounts row.name pos raws (i + 1) s _ taken.length hstep

/-- A signature of groups, standing or needed, reads exactly a group prefix, each group standing. -/
public theorem argsRead_groups_exact {raws : Array Raw} {i args stop}
    (h : GroupPrefix raws i args stop) (acc : Array (Option (Array Raw))) (sig : List ArgKind)
    (hlen : sig.length = args.length) (hsig : ∀ k ∈ sig, k = .group ∨ k = .needed) :
    argsRead raws acc sig i = some (acc ++ (args.map some).toArray, stop) := by
  induction h generalizing acc sig with
  | nil =>
    cases sig with
    | nil => simp [argsRead]
    | cons _ _ => simp at hlen
  | @group i body p args stop hg _ ih =>
    cases sig with
    | nil => simp at hlen
    | cons k sig =>
      have hone := takeGroups_prefix_exact (GroupPrefix.group hg GroupPrefix.nil)
      simp only [List.length_cons, List.length_nil, Nat.zero_add] at hone
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hrest := ih (acc.push (some body)) sig hlen fun k hk => hsig k (List.mem_cons_of_mem _ hk)
      rcases hsig k List.mem_cons_self with rfl | rfl <;>
        simp [argsRead, hone, hrest]
  | @ctrl i name p args stop hg _ ih =>
    cases sig with
    | nil => simp at hlen
    | cons k sig =>
      have hone := takeGroups_prefix_exact (GroupPrefix.ctrl hg GroupPrefix.nil)
      simp only [List.length_cons, List.length_nil, Nat.zero_add] at hone
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hrest := ih (acc.push (some #[.ctrl name p])) sig hlen
        fun k hk => hsig k (List.mem_cons_of_mem _ hk)
      rcases hsig k List.mem_cons_self with rfl | rfl <;>
        simp [argsRead, hone, hrest]

/-- An ordinary body control consumes exactly its declared argument prefix. -/
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

/-- At a body cursor a quiet row whose arguments are groups consumes exactly a group prefix of its
arity and is paid for. -/
public theorem ctrlRow_groups_consumed (hsound : CtrlRowsSound) (row : CtrlRow)
    (hrow : row ∈ ctrlRows) (hquiet : row.quiet = true)
    (hsig : ∀ k ∈ row.sig, k = .group ∨ k = .needed) :
    ControlGroupsConsumed row.name row.sig.length := by
  intro inBody raws out pos args taken rest i s hd _ hp hsource hn hg
  have hk := argsRead_groups_exact hg #[] row.sig hn.symm hsig
  have hl := ctrlLeft_quiet row s (#[] ++ (args.map some).toArray) hquiet
  obtain ⟨hstep, hwalk, _⟩ := ctrlRow_control_contract hsound row hrow inBody raws out pos _ taken
    rest i s (by simp [hd]) hp hsource hk hl
  have hempty := ctrlRowRun_quiet row
    ⟨row.name, pos, #[] ++ (args.map some).toArray, raws, i + 1, i + 1 + taken.length⟩ s hquiet hd
  rw [hempty, Array.append_empty] at hwalk
  rw [hempty] at hstep
  dsimp only
  rw [hstep]
  exact ⟨rfl, hwalk, rewriteCtrl_accounts row.name pos raws (i + 1) s _ taken.length hstep⟩

/-- The dispatcher leaves a command and every following raw to elaboration. -/
public def UnknownControlPreserved (name : String) : Prop :=
  ∀ (inBody : Bool) (raws out : Array Raw) (pos : Pos)
    (rest : List Raw) (i : Nat) (s : St),
    St.inDoc s = true → St.inList s = false → St.inPicture s = false →
    raws.toList.drop i = .ctrl name pos :: rest →
    rewriteCtrl name pos raws (i + 1) s = (none, s) ∧
    rewriteList inBody raws out (raws.toList.drop i) i 0 s =
      rewriteList inBody raws (out.push (.ctrl name pos)) rest (i + 1) 0 s

public theorem unknown_control_contract (hz : ctrlRow? "zzNotAControl" = none) :
    UnknownControlPreserved "zzNotAControl" := by
  intro inBody raws out pos rest i s hd hl hp hsource
  refine ⟨rewriteCtrl_unknown_exact s pos raws (i + 1) hz hd hl, ?_⟩
  rw [hsource]
  exact rewriteList_unknown_exact inBody raws out pos rest i s hz hd hl hp

/-- A checkpoint of the compatibility walk: the source array, the rewritten
prefix `out`, and the remaining input `raws.drop index`. -/
public structure RewriteCursor where
  inBody : Bool
  raws : Array Raw
  out : Array Raw := #[]
  index : Nat := 0
  private state : St
  private complete : (Array Raw × St) → (Array Raw × St) := id

/-- The scope permits entry into an ordinary document environment. -/
public def RewriteCursor.outsidePicture (cursor : RewriteCursor) : Prop :=
  cursor.state.inPicture = false

/-- The ordinary document entry does not inherit a list-parameter scope. -/
public def RewriteCursor.outsideList (cursor : RewriteCursor) : Prop :=
  cursor.state.inList = false

/-- The checkpoint with its unread final document replaced, its executed state,
output prefix and continuation kept. -/
public def RewriteCursor.withDocument (cursor : RewriteCursor) (body : Array Raw)
    (pos : Pos) : RewriteCursor :=
  { cursor with raws := #[.env "document" body pos], index := 0 }

private def rewriteCursor (cursor : RewriteCursor) : Array Raw × St :=
  cursor.complete (rewriteList cursor.inBody cursor.raws cursor.out
    (cursor.raws.toList.drop cursor.index) cursor.index 0 cursor.state)

/-- A row's control with arguments `args` stands, no leave of its row holding, at the opening of
the document environment entered from this checkpoint. -/
public def RewriteCursor.rowStandsInBody (cursor : RewriteCursor) (row : CtrlRow)
    (args : Array (Option (Array Raw))) : Prop :=
  ctrlLeft (openDocumentBody cursor.state).2 row args = false

/-- Descends into the document environment at this checkpoint, its continuation
restoring the enclosing scope. -/
public def RewriteCursor.enterDocument (cursor : RewriteCursor)
    (body : Array Raw) (pos : Pos) : RewriteCursor :=
  { inBody := cursor.inBody
    raws := body
    state := (openDocumentBody cursor.state).2
    complete := fun result =>
      let (raw, st) := closeScope cursor.state (closeDocumentBody pos result)
      cursor.complete (rewriteList cursor.inBody cursor.raws (cursor.out.push raw)
        (cursor.raws.toList.drop (cursor.index + 1)) (cursor.index + 1) 0 st) }

private theorem rewriteRaw_document_exact (inBody arg : Bool) (body : Array Raw)
    (pos : Pos) (st : St) (hp : st.inPicture = false) :
    rewriteRaw inBody arg (.env "document" body pos) st =
      closeScope st
        (rewriteDocumentBody (rewriteList inBody body #[] body.toList 0 0) pos st) := by
  rw [rewriteRaw]
  simp only [Parse.inputEnvFile?, String.startsWith_string_iff]
  simp [withScope, closeScope, mathEnvs, pictureEnvs, hp,
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
  simp only [bind, StateT.bind, rewriteRaw_document_exact _ _ _ _ _ hp,
    RewriteCursor.enterDocument, List.drop_zero, ht, rewriteDocumentBody, closeScope,
    closeDocumentBody, pushRewritten]

private def closeLastDocument (cursor : RewriteCursor) (pos : Pos)
    (result : Array Raw × St) : Array Raw × St :=
  let (raw, st) := closeScope cursor.state (closeDocumentBody pos result)
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

/-- The gathered running content, one declaration each. -/
private def flushRunning : M (Array Raw) := do
  let st ← get
  let pos := st.runPos
  let at' (parts : Array (Nat × Array Raw)) (k : Nat) : Array Raw :=
    (parts.filter (·.1 == k)).foldl (init := #[]) fun acc (_, r) =>
      if acc.isEmpty then r else (acc.push .space) ++ r
  let fill := #[Raw.space, Raw.ctrl "hfill" pos, Raw.space]
  -- The line as the lexer reads its spelling, the one its note names.
  let line (parts : Array (Nat × Array Raw)) : Array Raw :=
    (Parse.asSpelled (at' parts 0 ++ fill ++ at' parts 1 ++ fill ++ at' parts 2).toList #[]).map
      (rebase (fun _ => pos) true)
  -- Each part spelled as its group's body is, a closing control space kept.
  let partSrc (r : Array Raw) : String := ((rawSrcOne (.group r pos)).drop 1).dropEnd 1 |>.toString
  let lineSrc (parts : Array (Nat × Array Raw)) : String :=
    s!"{partSrc (at' parts 0)} \\hfill {partSrc (at' parts 1)} \\hfill {partSrc (at' parts 2)}"
  let opt := if st.runFrom > 1 then s!"[from = {st.runFrom}]" else ""
  let optRaws : Array Raw := if st.runFrom > 1 then
    #[.sym '[' pos, .word s!"from = {st.runFrom}" pos, .sym ']' pos] else #[]
  let mut out : Array Raw := #[]
  unless st.head.isEmpty do
    became "\\ihead / \\chead / \\ohead" s!"\\runninghead{opt}\{{lineSrc st.head}}" pos
    out := out ++ #[.ctrl "runninghead" pos] ++ optRaws ++ #[.group (line st.head) pos]
  unless st.foot.isEmpty do
    became "\\ifoot / \\cfoot / \\ofoot" s!"\\runningfoot{opt}\{{lineSrc st.foot}}" pos
    out := out ++ #[.ctrl "runningfoot" pos] ++ optRaws ++ #[.group (line st.foot) pos]
  -- `\thispagestyle{empty}` with no field of its own still gates the opening page's furniture.
  if st.runFrom > 1 && st.head.isEmpty then
    out := out ++ (Native.Head.runningFrom false st.runFrom).raws st.runPos
  if st.runFrom > 1 && st.foot.isEmpty then
    out := out ++ (Native.Head.runningFrom true st.runFrom).raws st.runPos
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

private theorem flushBeamerBlocks_quiet (st : St) (h : QuietTail st) :
    flushBeamerBlocks st = (#[], st) := by
  simp only [flushBeamerBlocks, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, h.2.2.2.2.2.2.2, Array.isEmpty_empty, ↓reduceIte]
  rfl

private theorem flushBeamerFootline_quiet (st : St) (h : QuietTail st) :
    flushBeamerFootline st = ((#[], #[]), st) := by
  simp only [flushBeamerFootline, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, h.2.2.2.2.2.2.1]
  rfl

/-- A replayed hook body split across the `\begin{document}` seam: preamble
declarations to one side, everything else to the body. -/
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
    else if name == titlePageMark then
      let (_, k) := takeGroups raws (i + 1) 1
      seamSplit raws rest (i + 1) (k - (i + 1)) (pre ++ raws.extract i k, body)
    else if name == "defineenv" || name == "newtheorem" || name == "theoremstyle" then
      -- A definition a hook makes at the seam is the preamble's, as LaTeX's stands from there.
      let k := if name == "defineenv" then defineEnvEnd raws (i + 1)
        else theoremDeclEnd raws name (i + 1)
      seamSplit raws rest (i + 1) (k - (i + 1)) (pre ++ raws.extract i k, body)
    else
      seamSplit raws rest (i + 1) 0 (pre, body.push (.ctrl name pos))
  | r :: rest, i, 0, (pre, body) =>
    seamSplit raws rest (i + 1) 0 (pre, body.push r)

mutual

/-- The preamble's completed block hook applied to parsed block environments,
inside definitions too. -/
-- conserves: none — adds native spacing commands only
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

/-- The executed surface and the state its compatibility
rewrite continues from. -/
public structure Executed where
  raws : Array Raw
  private state : St

/-- The executed surface replaced after resolving data requests, its
compatibility state and receipts kept. -/
public def Executed.withRaws (executed : Executed) (raws : Array Raw) : Executed :=
  { executed with raws := raws }

/-- The original source index, which survives execution and
included-file fulfilment. -/
public def Executed.sourceTriggers (executed : Executed) : SourceTriggers :=
  executed.state.sourceTriggers

/-- The reader receipts the evaluator retained. -/
public def Executed.inputAttempts (executed : Executed) : Array InputAttempt :=
  executed.state.inputAttempts

/-- The source of each value a construct execution refused carried. -/
public def Executed.mentions (executed : Executed) : Array String :=
  executed.state.mentions

public theorem Executed.withRaws_contract (executed : Executed) (raws : Array Raw) :
    (executed.withRaws raws).raws = raws ∧
      (executed.withRaws raws).sourceTriggers = executed.sourceTriggers ∧
      (executed.withRaws raws).inputAttempts = executed.inputAttempts := by
  exact ⟨rfl, rfl, rfl⟩

private def executionState (reading : Bool) (file : String) (raws : Array Raw)
    (provideKeeps : List String) (warned : Array String) (diags : Array Diag)
    (ignoredDefs : List String) : St :=
  { file := file, provideKeeps := provideKeeps, ignoredDefs := ignoredDefs, warned := warned
    diags := diags
    sourceTriggers := sourceTriggers file {} raws.toList
    fileTop := reading, boundaryOpen := !boundaryRefused raws
    wholeDoc := raws.any (· matches .env "document" _ _), docFile := file }

private def executeBy [Monad m] (reader : Option (InputReader m))
    (file : String) (raws : Array Raw) (provideKeeps : List String)
    (warned : Array String) (inherited : List String) (diags : Array Diag)
    (ignoredDefs : List String) : m Executed := do
  let go : EvalM m (Array Raw) := do
    -- latex.ltx's `\def\space{ }`.
    recordValue "space"
      (some { raws := #[.space], long := false, prot := false, live := true }) false
    -- A fragment's caller owns these meanings; their text is unread here.
    for n in inherited do setBind n none
    condDocument reader raws
  let (raws, state) ← go.run
    (executionState reader.isSome file raws provideKeeps warned diags ignoredDefs)
  return { raws := raws, state := state }

/-- A surface the walk leaves alone whole, markdown or a code file: nothing executes, and its raws
return as they are after the rewrite. -/
public def kept (file : String) (raws : Array Raw) : Executed :=
  { raws := #[Parse.keptRaw 0 {}], state := { file, docFile := file, kept := #[raws] } }

/-- Executes a file-free surface once, retaining the same source evidence as the
input-fulfilling path. -/
public def execute (file : String) (raws : Array Raw) (provideKeeps : List String := [])
    (warned : Array String := #[]) (inherited : List String := [])
    (ignoredDefs : List String := []) : Executed :=
  executeBy (m := Id) none file raws provideKeeps warned inherited #[] ignoredDefs

/-- Executes the document with a reader that fulfils file
requests at their uses. -/
public def executeInputs [Monad m] (reader : InputReader m) (file : String)
    (raws : Array Raw) (provideKeeps : List String := []) (diags : Array Diag := #[])
    (ignoredDefs : List String := []) : m Executed :=
  executeBy (some reader) file raws provideKeeps #[] [] diags ignoredDefs

private theorem executeInputs_condDocument_exact (reader : InputReader Id)
    (file : String) (raws : Array Raw) (keeps : List String) (ds : Array Diag)
    (ignored : List String) :
    executeInputs reader file raws keeps ds ignored =
      let result := condDocument (some reader) raws
        (withSpaceBinding (executionState true file raws keeps #[] ds ignored))
      { raws := result.1, state := result.2 } := by
  simp only [executeInputs, executeBy, Option.isSome_some, StateT.run,
    evalLift_id, bind, StateT.bind, recordValue_space_exact]
  rfl

private def packageInitialState (file command names : String) (pos gp np : Pos)
    (keeps : List String) (ds : Array Diag) (ignored : List String) : St :=
  withSpaceBinding
    (executionState true file (packageCall command names pos gp np) keeps #[] ds ignored)

private def packageExecutedState (file command names : String) (pos gp np : Pos)
    (keeps : List String) (ds : Array Diag) (ignored : List String) : St :=
  let st := packageInitialState file command names pos gp np keeps ds ignored
  { packageFailed command names pos gp np st with writes := st.writes + 10 }

private theorem executeInputs_package_failed_exact (reader : InputReader Id)
    (file command names : String) (pos gp np : Pos) (keeps : List String) (ds : Array Diag)
    (ignored : List String)
    (hc : command = "usepackage" ∨ command = "RequirePackage")
    (hr : ∀ request context, reader request context = (none, context)) :
    executeInputs reader file (packageCall command names pos gp np) keeps ds ignored =
      { raws := packageCall command names pos gp np
        state := packageExecutedState file command names pos gp np keeps ds ignored } := by
  have hn : command ≠ "space" := by rcases hc with rfl | rfl <;> decide
  have hv : condValueOf
      (packageInitialState file command names pos gp np keeps ds ignored).binds command =
        none := by
    simp [packageInitialState, withSpaceBinding, executionState, condValueOf, Ne.symm hn]
  rw [executeInputs_condDocument_exact]
  have heq := condDocument_package_failed_exact reader command names pos gp np
    (packageInitialState file command names pos gp np keeps ds ignored)
    hc rfl rfl rfl rfl rfl rfl rfl hv hr
  change condDocument (some reader) (packageCall command names pos gp np)
    (withSpaceBinding (executionState true file
      (packageCall command names pos gp np) keeps #[] ds ignored)) = _ at heq
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
  have hr : "usepackage" ∉ Definer.redefiners ∧ "RequirePackage" ∉ Definer.redefiners := by
    decide
  rcases hc with rfl | rfl <;>
    simp [packageCall, delimCallsList, delimCallsRaw, delimClose, hr.1, hr.2,
      bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      hd, write_eq, pure, StateT.pure]

private theorem overprint_package_exact (command names : String) (pos gp np : Pos)
    (hc : command = "usepackage" ∨ command = "RequirePackage") (st : St) :
    overprintList (packageCall command names pos gp np).toList #[] 0 st =
      (packageCall command names pos gp np, st) := by
  have hn : command ≠ "apptocmd" := by rcases hc with rfl | rfl <;> decide
  simp [packageCall, overprintList, overprintRaw, hn, bind, StateT.bind,
    pure, StateT.pure]

private theorem readCxOf_package_exact (command names : String) (pos gp np : Pos)
    (hc : command = "usepackage" ∨ command = "RequirePackage") :
    readCxOf (packageCall command names pos gp np) = { userOnly := false, userAlt := false } := by
  have hn : "usepackage" ∉ Definer.nameDefiners ∧ "RequirePackage" ∉ Definer.nameDefiners := by
    decide
  rcases hc with rfl | rfl <;>
    simp [readCxOf, packageCall, definesList, definesRaw, hn.1, hn.2]

private theorem onlyAlternationsIn_package_exact (cx : ReadCx) (command names : String)
    (pos gp np : Pos) (hc : command = "usepackage" ∨ command = "RequirePackage") :
    onlyAlternationsIn cx (packageCall command names pos gp np) =
      packageCall command names pos gp np := by
  have hn : command ≠ "apptocmd" := by rcases hc with rfl | rfl <;> decide
  simp [onlyAlternationsIn, packageCall, onlyAltList, onlyAltRaw, readList, readRawAlone, hn]

/-- The commands whose first braced argument names a counter they read or set. -/
private def counterCommands : List String :=
  ["stepcounter", "refstepcounter", "addtocounter", "setcounter", "value", "arabic", "roman",
   "Roman", "alph", "Alph", "fnsymbol", "usecounter"]

/-- The commands whose two braced arguments each name a counter. -/
private def counterPairCommands : List String := ["numberwithin", "counterwithin", "counterwithout"]

/-- The braced argument past spaces and a star, `none` inside when it holds a parameter, and the
raws after it. -/
private def counterArg : List Raw → Option (Option String × List Raw)
  | .space :: rest => counterArg rest
  | .word "*" _ :: rest => counterArg rest
  | .group g _ :: rest =>
    some (if holdsParam g.toList then none else some (rawSrc g).trimAscii.toString, rest)
  | _ => none

/-- The raws up to the bracket closing an option, and the raws after it. -/
private def bracketBody (acc : Array Raw) : List Raw → Option (Array Raw × List Raw)
  | [] => none
  | .sym ']' _ :: rest => some (acc, rest)
  | r :: rest => bracketBody (acc.push r) rest

/-- A bracketed option past spaces, as `counterArg` reads a group. -/
private def counterOpt : List Raw → Option (Option String × List Raw)
  | .space :: rest => counterOpt rest
  | .sym '[' _ :: rest => (bracketBody #[] rest).map fun (b, after) =>
    (if holdsParam b.toList then none else some (rawSrc b).trimAscii.toString, after)
  | _ => none

private def readCounter (reads : Std.HashSet String) : Option String → Std.HashSet String
  | some n => reads.insert n
  | none => reads

/-- The counters one control reads from the raws after it: a counter command's argument, both of
a pair's, an allocation's parent, a theorem's shared or parent counter, and the counter a `\the`
or `\c@` control names. -/
private def controlCounterReads (reads : Std.HashSet String) (c : String) (rest : List Raw) :
    Std.HashSet String :=
  if counterCommands.contains c then
    match counterArg rest with
    | some (n, _) => readCounter reads n
    | none => reads
  else if counterPairCommands.contains c then
    match counterArg rest with
    | some (a, after) => match counterArg after with
      | some (b, _) => readCounter (readCounter reads a) b
      | none => readCounter reads a
    | none => reads
  else if c == "newcounter" then
    match counterArg rest with
    | some (_, after) => match counterOpt after with
      | some (p, _) => readCounter reads p
      | none => reads
    | none => reads
  else if c == "newtheorem" then
    match counterArg rest with
    | some (_, after) =>
      let (reads, after) := match counterOpt after with
        | some (shared, after') => (readCounter reads shared, after')
        | none => (reads, after)
      match counterArg after with
      | some (_, after) => match counterOpt after with
        | some (within, _) => readCounter reads within
        | none => reads
      | none => reads
    | none => reads
  else if c.startsWith "the" && c.length > 3 then reads.insert (c.drop 3).toString
  else if c.startsWith "c@" && c.length > 2 then reads.insert (c.drop 2).toString
  else reads

mutual

/-- The counter names a document's raws read, in one pass. -/
private def counterReadsList (reads : Std.HashSet String) : List Raw → Std.HashSet String
  | [] => reads
  | r :: rest =>
    let reads := match r with
      | .ctrl c _ => controlCounterReads reads c rest
      | _ => reads
    counterReadsList (counterReadsOne reads r) rest
termination_by structural l => l

private def counterReadsOne (reads : Std.HashSet String) : Raw → Std.HashSet String
  | .group body _ => counterReadsList reads body.toList
  | .math _ body _ => counterReadsList reads body.toList
  | .env _ body _ => counterReadsList reads body.toList
  | _ => reads
termination_by structural r => r

end

/-- The passes before the compatibility walk: overlay inputs, live groups,
delimiters, columns, overprints and `\only`'s alternations. -/
public def beginRewrite (executed : Executed) : RewriteCursor :=
  let raws := overlayInputs executed.raws
  let cx := readCxOf raws
  let go : M (Array Raw) := do
    -- After the conditionals only a live pair is a group.
    let raws := pairGroupsList true #[] raws.toList
    let raws ← delimDocument raws
    let raws := (splitColumnsList raws.toList).toArray
    let raws ← overprintList raws.toList #[] 0
    pure (onlyAlternationsIn cx raws)
  let st0 : St :=
    { executed.state with
      boundaryOpen := !boundaryRefused raws,
      wholeDoc := raws.any (· matches .env "document" _ _),
      userOverlays := (cx.userOnly, cx.userAlt),
      countersRead := counterReadsList {} raws.toList }
  let (raws, st) := go.run st0
  { inBody := false, raws := raws, state := st }

private def packageRewriteState (st : St) (command names : String) (pos gp np : Pos) : St :=
  { st with
    boundaryOpen := !boundaryRefused (packageCall command names pos gp np)
    wholeDoc := false, deferred := #[], writes := st.writes + 1,
    userOverlays := (false, false),
    countersRead := counterReadsList {} (packageCall command names pos gp np).toList }

private theorem beginRewrite_package_exact (command names : String) (pos gp np : Pos)
    (st : St) (hc : command = "usepackage" ∨ command = "RequirePackage")
    (hd : st.deferred = #[]) :
    beginRewrite { raws := packageCall command names pos gp np, state := st } =
      { inBody := false
        raws := packageCall command names pos gp np
        state := packageRewriteState st command names pos gp np } := by
  simp only [beginRewrite, overlayInputs_package_exact _ _ _ _ _ hc,
    readCxOf_package_exact _ _ _ _ _ hc]
  have hw : (packageCall command names pos gp np).any
      (· matches .env "document" _ _) = false := by simp [packageCall]
  have hdelim := delimDocument_package_exact command names pos gp np hc
    { st with
      boundaryOpen := !boundaryRefused (packageCall command names pos gp np)
      wholeDoc := false
      userOverlays := (false, false)
      countersRead := counterReadsList {} (packageCall command names pos gp np).toList } hd
  have hcols : splitColumnsList (packageCall command names pos gp np).toList =
      (packageCall command names pos gp np).toList := by rfl
  simp only [hw, StateT.run, bind, StateT.bind,
    pairGroups_package_exact, hdelim,
    hcols, overprint_package_exact _ _ _ _ _ hc, onlyAlternationsIn_package_exact _ _ _ _ _ _ hc,
    pure, StateT.pure, packageRewriteState]

/-- The gathered declarations and deferred bodies
interpreted after row lowering. -/
private def finishDeclarations (out : Array Raw) : M (Array Raw) := do
  let running ← flushRunning
  let running := running ++ (← flushListLevels)
  let running ← rewriteList false running #[] running.toList 0 0
  -- Each deferred body is rewritten as preamble material, then routed across the seam.
  let saved := (← get).inDoc
  let savedFile := (← get).file
  write fun st => { st with inDoc := false }
  let mut preSide : Array Raw := #[]
  let mut bodySide : Array Raw := #[]
  for (pt, file, pos, body) in (← get).deferred do
    write fun st => { st with file := file, seam := pt == .beginDocument }
    let body := overlayInputs body
    let (userOnly, userAlt) := (← get).userOverlays
    let body := onlyAlternationsIn
      { userOnly := userOnly || definesList "only" body.toList,
        userAlt := userAlt || definesList "alt" body.toList } body
    let body ← rewriteList false body #[] body.toList 0 0
    -- A hook from an `\input` file replays inside that file's wrapper.
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
  preSide := preSide ++ footerPre ++ (← flushBeamerBlocks) ++ (← get).pageAttr
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

private def finishRewrittenState (result : Array Raw × St) : Array Raw × St :=
  let go : M (Array Raw) := do
    -- After the idiom rewrite, so a `\parbox` is the box it became.
    let out ← boxRowList #[] result.1.toList
    let out ← boxRowEmit out
    finishDeclarations out
  go.run result.2

/-- The production tail after the compatibility walk. -/
private def finishRewritten (result : Array Raw × St) :
    Array Raw × Array Diag × Array String × Array TemplateDecl :=
  let (out, st) := finishRewrittenState result
  let out := if st.beamerBlockBegin.isEmpty then out
    else blockHookList st.beamerBlockBegin #[] out.toList
  let out := if st.kept.isEmpty then out else Parse.spliceKeptList st.kept #[] out.toList
  (out, st.diags, st.warned, st.templates)

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

/-- Completes a rewrite checkpoint: boxes, running content, deferred hooks,
counters and block hooks. -/
public def finishRewrite (cursor : RewriteCursor) :
    Array Raw × Array Diag × Array String × Array TemplateDecl :=
  finishRewritten (rewriteCursor cursor)

/-- The compatibility rewrite finished after execution and file fulfilment. -/
@[expose] public def rewriteExecuted (executed : Executed) :
    Array Raw × Array Diag × Array String × Array TemplateDecl :=
  finishRewrite (beginRewrite executed)

/-- Names for which the package dispatcher has no native, external-picture or
installed-theme interpretation. -/
@[expose] public def ExternalPackageNames (names : String) : Prop :=
  ∀ part ∈ names.trimAscii.toString.splitOn ",",
    part.trimAscii.toString.isEmpty = false ∧
    nativePackages.contains part.trimAscii.toString = false ∧
    boundaryPkgs.contains part.trimAscii.toString = false ∧
    themeSlotOfPackage? part.trimAscii.toString = none

attribute [local irreducible] finishRewritten in
/-- A failed reader answer to a live package declaration is both recorded and
named by the compatibility producer. -/
public theorem executeInputs_package_refusal_contract (reader : InputReader Id)
    (file command names : String) (pos groupPos namePos : Pos)
    (keeps : List String) (ds : Array Diag) (ignored : List String)
    (hc : command = "usepackage" ∨ command = "RequirePackage")
    (hrow : ctrlRow? command = some (packageRow command)) (hnames : ExternalPackageNames names)
    (hr : ∀ request context, reader request context = (none, context)) :
    let executed := executeInputs reader file
      (packageCall command names pos groupPos namePos) keeps ds ignored
    executed.inputAttempts =
        #[⟨⟨command, file, pos, pos, #[.group #[.word names namePos] groupPos]⟩, false⟩] ∧
      ∀ part ∈ names.trimAscii.toString.splitOn ",",
        executed.sourceTriggers.attribute
          (packageRefusal file pos part.trimAscii.toString) ∈
            (rewriteExecuted executed).2.1 := by
  rw [executeInputs_package_failed_exact reader file command names pos groupPos namePos
    keeps ds ignored hc hr]
  let initial := packageExecutedState file command names pos groupPos namePos keeps ds ignored
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
      hc hrow rfl rfl rfl rfl hn hb ht part hpart
    let reports := ((names.trimAscii.toString.splitOn ",").map fun p =>
      atSource st pos (packageRefusal st.file pos p.trimAscii.toString)).toArray
    let after := { st with diags := st.diags ++ reports }
    have hquiet : QuietTail after := by
      exact ⟨rfl, rfl, Nat.le_refl 1, rfl, rfl, rfl, rfl, rfl⟩
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

/-- A row's control's document completed from the retained body around the row's emission at
`call` and from the state it leaves. -/
public def finishCtrlRowDocument (cursor : RewriteCursor) (row : CtrlRow) (call : CtrlCall)
    (docPos : Pos) (pre post : Array Raw) :
    Array Raw × Array Diag × Array String × Array TemplateDecl :=
  finishRewritten (closeLastDocument cursor docPos
    (pre ++ (ctrlRowRun row call (openDocumentBody cursor.state).2).1 ++ post,
      ctrlRowState (openDocumentBody cursor.state).2 row call))

public theorem finishCtrlRowDocument_source_exact (cursor : RewriteCursor) (body : Array Raw)
    (row : CtrlRow) (call : CtrlCall) (docPos : Pos) (pre post : Array Raw) :
    finishCtrlRowDocument (cursor.withDocument body docPos) row call docPos pre post =
      finishCtrlRowDocument cursor row call docPos pre post := by rfl

/-- A row whose action reads no argument completes its document alike wherever its call stands. -/
public theorem finishCtrlRowDocument_fixed_exact (cursor : RewriteCursor) (row : CtrlRow)
    (call call' : CtrlCall) (h : row.action.reads = false) (hpos : call.pos = call'.pos)
    (docPos : Pos) (pre post : Array Raw) :
    finishCtrlRowDocument cursor row call docPos pre post =
      finishCtrlRowDocument cursor row call' docPos pre post := by
  simp only [finishCtrlRowDocument, ctrlRowState, ctrlRowRun_fixed row call call' h hpos, hpos]

public theorem finishRewrite_row_document_exact (hsound : CtrlRowsSound)
    (cursor : RewriteCursor) (body : Array Raw) (row : CtrlRow) (hrow : row ∈ ctrlRows)
    (pos docPos : Pos) (args : Array (Option (Array Raw))) (pre taken post : List Raw)
    (hp : cursor.outsidePicture)
    (hs : cursor.raws.toList.drop cursor.index = [.env "document" body docPos])
    (hb : body.toList = pre ++ .ctrl row.name pos :: (taken ++ post))
    (hpre : LiteralRaws pre) (hpost : LiteralRaws post)
    (hk : argsRead body #[] row.sig (pre.length + 1) =
      some (args, pre.length + 1 + taken.length))
    (hl : cursor.rowStandsInBody row args) :
    finishRewrite cursor =
      finishCtrlRowDocument cursor row
        ⟨row.name, pos, args, body, pre.length + 1, pre.length + 1 + taken.length⟩
        docPos pre.toArray post.toArray := by
  unfold finishRewrite
  rw [rewriteCursor_last_document_exact cursor body docPos hp hs, hb]
  have hbody := rewriteList_row_body_exact hsound cursor.inBody body #[] row hrow pos args pre
    taken post 0 (openDocumentBody cursor.state).2
    (by simp [show (openDocumentBody cursor.state).2.inDoc = true from rfl]) hp hpre hpost
    (by simpa only [Nat.zero_add] using hk) hl
  simp only [Nat.zero_add] at hbody
  rw [hbody]
  simp only [Array.empty_append, finishCtrlRowDocument]

/-- The commands whose first argument names the length they assign. -/
private def lengthAssigners : List String := ["setlength", "addtolength"]

/-- A raw walk's tally: each control word's occurrences, each length declaration's or assignment's
target, and the file and place of a target's first assignment to a literal value. -/
private structure LengthTally where
  seen : Std.HashMap String Nat := {}
  targets : Std.HashMap String Nat := {}
  first : Array (String × String × Pos) := #[]

private def LengthTally.see (t : LengthTally) (n : String) : LengthTally :=
  { t with seen := t.seen.insert n (t.seen.getD n 0 + 1) }

private def LengthTally.target (t : LengthTally) (n : String) : LengthTally :=
  { t with targets := t.targets.insert n (t.targets.getD n 0 + 1) }

private def LengthTally.assign (t : LengthTally) (n file : String) (p : Pos) : LengthTally :=
  { t.target n with first := if t.first.any (·.1 == n) then t.first else t.first.push (n, file, p) }

/-- The length a length command's next raw names, `\x` or `{\x}`, and the raws after it. -/
private def assignedLength : List Raw → Option (String × List Raw)
  | .space :: rest => assignedLength rest
  | .ctrl n _ :: rest => some (n, rest)
  | .group g _ :: rest => match g.toList.filter (!· matches .space) with
    | [.ctrl n _] => some (n, rest)
    | _ => none
  | _ => none

/-- Whether an assignment's value is a braced literal the length door reads, so names nothing
itself. -/
private def literalValue : List Raw → Bool
  | .space :: rest => literalValue rest
  | .group g _ :: _ =>
    let src := (rawSrc g).trimAscii.toString
    g.all (fun r => !(r matches .ctrl ..)) && readsAsLength src && texWordsOnly src
  | _ => false

mutual

private def tallyList (file : String) (t : LengthTally) : List Raw → LengthTally
  | [] => t
  | r :: rest =>
    let t := match r with
      | .ctrl c p =>
        match assignedLength rest with
        | some (n, after) =>
          if lengthAssigners.contains c && literalValue after then t.assign n file p
          else if lengthAssigners.contains c || c == "newlength" then t.target n
          else t
        | none => t
      | _ => t
    tallyList file (tallyOne file t r) rest
termination_by structural l => l

private def tallyOne (file : String) (t : LengthTally) : Raw → LengthTally
  | .ctrl n _ => t.see n
  | .group body _ => tallyList file t body.toList
  | .math _ body _ => tallyList file t body.toList
  | .env n body _ => tallyList ((Parse.inputEnvFile? n).getD file) t body.toList
  | _ => t
termination_by structural r => r

end

/-- Each length the document assigns that neither it nor the engine reads, named at its first
assignment. -/
public def unusedLengths (file : String) (raws : Array Raw) : Array Diag :=
  let t := tallyList file {} raws.toList
  t.first.filterMap fun (n, f, p) =>
    if (paramSites.lookup n).isSome || Ir.engineTokenNames.contains n ||
        t.seen.getD n 0 > t.targets.getD n 0 then none
    else some (Diag.of .W0104
      s!"'\\{n}' is set, but nothing in the document or the engine reads it; the setting changes nothing"
      (some ⟨f, p⟩) (help := "use the length where the page should read it, or drop the setting")
      (subject := some (paramSubject "setlength" n)))

/-- Rewrites a whole parsed document. -/
public def rewrite (file : String) (raws : Array Raw) (provideKeeps : List String := [])
    (warned : Array String := #[]) (inherited : List String := []) :
    Array Raw × Array Diag × Array String :=
  let r := rewriteExecuted (execute file raws provideKeeps warned inherited)
  (r.1, r.2.1, r.2.2.1)

/-- Diagnostic codes that carry a refused name. -/
public def nameRefusalAsk : List (DiagCode × String) :=
  [(.W0103, ""), (.W0319, "beamertheme")]

mutual

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
    -- A theme-family command asks for its prefixed file name.
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

/-- Descends into an `\input` wrapper, which asks exactly as
the top level does. -/
private def styCandRaw (out : Array String) : Raw → Array String
  | .env n body _ =>
    if (Parse.inputEnvFile? n).isSome then styCandList body out body.toList 0 0
    else out
  | _ => out

end

/-- Style-file candidates from a source stream; native
packages ask for no file. -/
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
    · have _ : sizeOf body = 1 + sizeOf body.toList := by rfl
      exact styCandList_monotone body out body.toList 0 0 nm hm
    · exact hm
  | word w pos | ctrl cn pos | sym c pos | group body pos | math display body pos | verb name body pos | par pos | space => exact hm
termination_by sizeOf r
end

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

/-- Every slot of beamer's theme-loading family asks the
input path for exactly its prefixed file. -/
public theorem themeAsking_candidates (nm : String) (pos : Pos) (hne : nm.trimAscii.toString = nm)
    (hnz : nm ≠ "") :
    ∀ p ∈ themeAsking,
      localStyCandidates #[.ctrl p.1 pos, .group #[.word nm pos] pos]
        = #[p.2 ++ nm] := by
  intro p hp
  simp only [themeAsking, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  all_goals exact localSty_theme _ _ nm pos rfl hne hnz (by decide) (by decide)


/-- One step of the option scheduler, emitted in source order. -/
private inductive StyOptionStep where
  | raw (value : Raw)
  | processed (pos : Pos)
  | unhandled (option : String) (pos : Pos)
  deriving Repr, BEq

/-- A declared option recorded in its first-declaration slot; redeclaring
replaces the body in place. -/
private def declareStyOption (declared : Array (String × Option (Array Raw)))
    (name : String) (body : Array Raw) : Array (String × Option (Array Raw)) :=
  if declared.any (·.1 == name) then
    declared.map fun (nm, old) => (nm, if nm == name then some body else old)
  else declared.push (name, some body)

private def styOptionBody (declared : Array (String × Option (Array Raw)))
    (name : String) : Option (Array Raw) :=
  (declared.find? (·.1 == name)).bind (·.2)

/-- Literal package option scheduling as ltclass.dtx defines it. -/
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
        -- TeX's `\@for` skips an empty list but keeps empty items in a nonempty one.
        unless opts.isEmpty do
          for nm in KeyVal.split opts do
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
        -- `\ProcessOptions` empties the empty-name handler before either pass.
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

/-- The scheduler's requests encoded in the raw stream,
without re-parsing option text. -/
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

/-- The shipped bundle a theme file stands on, installed
before the file's own content. -/
private def bundleFloor (pre nm : String) (pos : Pos) : Array Raw :=
  let nm := themeAlias nm
  if pre == "beamertheme" && (Theme.find? nm).isSome then
    #[.ctrl "theme" pos, .group #[.word nm pos] pos]
  else #[]

/-- Splices one admitted file. -/
public def spliceLocalPackage (name : String) (passed : List String)
    (raws : Array Raw) (pos : Pos) : Array Raw :=
  let floor := match themeSlotOfPackage? name with
    | some (_, pre, nm) => bundleFloor pre nm pos
    | none => #[]
  floor.push (.env (Parse.inputEnv (name ++ ".sty")) (spliceStyOptions name passed raws) pos)

/-- The replacement for one `\usepackage`/`\RequirePackage` at `i` given the
style files read; `none` when it names no local file. -/
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

/-- The replacement for one member of the theme family at `i`: the theme file's
fragment when it was read, `none` otherwise. -/
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

-- conserves: none — a local file's `\usepackage` becomes its content
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

/-- Descends into an `\input` wrapper, splicing inside it as
at the top level. -/
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

/-- Splices the local style files the driver found, each
wrapped as that file's input fragment. -/
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

public theorem applyLocalSty_id (raws : Array Raw) : applyLocalSty raws #[] = (raws, #[]) := by
  rw [applyLocalSty, applyStyList_empty]
  simp

/-- What a spliced `.sty` yielded after elaboration: constructs honoured, named,
and TeX internals refused. -/
public def styCounts (sty : String) (diags : Array Diag) : Nat × Nat × Nat :=
  let mine := diags.filter fun d => d.span.any (·.file == sty)
  ((mine.filter (·.code == "N0100")).size,
   (mine.filter (·.severity == .warning)).size,
   (mine.filter fun d =>
     d.severity == .note &&
       (d.code == "W0301" || d.code == "W0357" || d.code == "W0391")).size)

/-- The one N0020 note: that the file was read, and how much of it took. -/
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

/-- The unit symbols, transcribed from siunitx's own declarations. -/
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

/-- The SI prefixes, from siunitx's own declarations. -/
private def siPrefixes : List (String × String) :=
  [("quecto", "q"), ("ronto", "r"), ("yocto", "y"), ("zepto", "z"),
   ("atto", "a"), ("femto", "f"), ("pico", "p"), ("nano", "n"),
   ("micro", "\u03BC"), ("milli", "m"), ("centi", "c"), ("deci", "d"),
   ("deca", "da"), ("deka", "da"), ("hecto", "h"), ("kilo", "k"),
   ("mega", "M"), ("giga", "G"), ("tera", "T"), ("peta", "P"),
   ("exa", "E"), ("zetta", "Z"), ("yotta", "Y"), ("ronna", "R"),
   ("quetta", "Q")]

/-- The superscript glyph per digit, and the superscript minus. -/
private def supChar : Char → Char
  | '0' => '⁰' | '1' => '¹' | '2' => '²' | '3' => '³' | '4' => '⁴'
  | '5' => '⁵' | '6' => '⁶' | '7' => '⁷' | '8' => '⁸' | '9' => '⁹'
  | '-' => '⁻' | c => c

private def toSup (s : String) : String :=
  String.ofList (s.toList.map supChar)

/-- A digit run grouped in threes with the locale's
separator, only when it has five or more digits. -/
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

/-- `\num`'s output for one plain number: grouped digits, the locale's decimal
marker, and a superscript exponent. -/
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

/-- A unit argument flattened, so `{\kilo\metre}` and bare
`\kilo\metre` read the same. -/
-- conserves: none — a projection to a unit's atoms
private def unitAtoms (out : Array Raw) : List Raw → Array Raw
  | [] => out
  | r :: rest => unitAtoms (unitAtomOne out r) rest

private def unitAtomOne (out : Array Raw) : Raw → Array Raw
  | .group b _ => unitAtoms out b.toList
  | r => out.push r

end

/-- One unit group's symbols, with siunitx's prefix and power syntax. -/
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

/-- `\ang`'s degrees, arcminutes and arcseconds with the
symbols siunitx sets. -/
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

/-- The listing defaults standing in one layer: each declaration's entries, beside its index in
`listingDefaults` where the declaration is the document's own. -/
private abbrev DefaultLayer := Array (Option Nat × Array String)

/-- The state the text pass threads in flow order. -/
private structure TextSt where
  /-- `\lstset` entries standing, injected ahead of every
  following listing's own options. -/
  lstOpts : DefaultLayer := #[]
  /-- Minted's global and lexer defaults, separate layers. -/
  mintedOpts : DefaultLayer := #[]
  mintedLangOpts : Array (String × DefaultLayer) := #[]
  /-- `\setmintedinline`'s layers, read by inline code
  alone, after both of `\setminted`'s. -/
  inlineOpts : DefaultLayer := #[]
  inlineLangOpts : Array (String × DefaultLayer) := #[]
  /-- Names the document defines; a defined `\num` is the document's. -/
  defined : Array String := #[]
  /-- The document's argument-free commands standing for a minted call short of
  its code, each with that call's head. -/
  shortcuts : Array (String × Array Raw) := #[]
  /-- Brace groups the pass stands inside, where a definition's body stands too. -/
  depth : Nat := 0
  /-- Inside a file a package or class file inputs, whose declarations are the package's. -/
  owned : Bool := false

/-- The standing entries injected ahead of an environment's
own options, which win. -/
private def injectListingOpts (opts : Array String) (s : String) : String :=
  if opts.isEmpty then s else
  let joined := String.intercalate "," opts.toList
  match Parse.listingOptHead s with
  | some (o, past) => "[" ++ joined ++ "," ++ o ++ "]" ++ (s.drop past).toString
  | none => "[" ++ joined ++ "]" ++ s

/-- The layers a listing of `env` in `lang` reads, in the order its options stack: `\lstset`'s for
a `lstlisting`, minted's global and lexer layers for minted's display, and the inline layers too
for `\mintinline`. -/
private def readLayers (st : TextSt) (env lang : String) : Array DefaultLayer :=
  let layer (l : Array (String × DefaultLayer)) := ((l.find? (·.1 == lang)).map (·.2)).getD #[]
  if env == "lstlisting" then #[st.lstOpts]
  else if env == "mintinline" then
    #[st.mintedOpts, layer st.mintedLangOpts, st.inlineOpts, layer st.inlineLangOpts]
  else #[st.mintedOpts, layer st.mintedLangOpts]

/-- The entries the layers a listing reads stack, in order. -/
private def readEntries (st : TextSt) (env lang : String) : Array String :=
  (readLayers st env lang).foldl (fun acc l => l.foldl (· ++ ·.2) acc) #[]

/-- The document's own declarations among the layers a listing reads. -/
private def readIds (st : TextSt) (env lang : String) : Array Nat :=
  (readLayers st env lang).foldl (fun acc l => l.foldl (fun acc d => acc ++ d.1.toArray) acc) #[]

/-- Marks the defaults a listing reads as read. -/
private def markRead (ids : Array Nat) : M Unit :=
  unless ids.isEmpty do
    write fun s => { s with listingDefaults := ids.foldl (fun ds i =>
      ds.modify i fun d => { d with read := true }) s.listingDefaults }

/-- The lexer a minted call names, its options aside. -/
private def mintedLang (s : String) : String :=
  let afterOpt := ((Parse.listingOptHead s).map (·.2)).getD 0
  ((Parse.mintedLangHead s afterOpt).map (·.1.trimAscii.toString)).getD ""

/-- Records a listing default the document itself declares at the pass's top level, and its
index; a definition's body or a group's is no standing declaration. -/
private def declareDefault (st : TextSt) (reader : String) (lang : Option String) (pos : Pos) :
    M (Option Nat) := do
  let file := (← get).file
  -- A declaration a definition's replacement text makes at its call is the definition's.
  let written := pos.command.isSome && (← get).sourceTriggers.writtenAt file pos == pos.command
  if st.depth != 0 || !written || !UnusedSetting.ownSite (packageFile file || st.owned) false pos then
    return none
  let i := (← get).listingDefaults.size
  write fun s => { s with listingDefaults := s.listingDefaults.push { reader, lang, pos, file } }
  return some i

/-- Names each declared listing default no listing after it read. -/
private def nameUnreadDefaults : M Unit := do
  let saved := (← get).file
  for d in (← get).listingDefaults do
    unless d.read do
      let (msg, subject) := UnusedSetting.listingWords d.reader d.lang
      write fun s => { s with file := d.file }
      say .W0449 msg d.pos (help := some (UnusedSetting.unusedHelp "the declaration"))
        (subject := some subject)
  write fun s => { s with file := saved }

/-- One siunitx command's replacement and the index past its arguments. -/
private def siCtrl (loc : Locale) (n : String) (pos : Pos) (raws : Array Raw)
    (start : Nat) : M (Array Raw × Nat) := do
  sayOnce ("si:" ++ n) .N0100
    s!"'\\{n}' spells its text natively: locale digits and unit symbols (siunitx)" pos
  let (opt, j) := takeOpt raws start
  if opt.isSome then
    sayOnce ("siopt:" ++ n) .W0110 s!"'\\{n}' options are not honoured; ignored" pos
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

/-- A minted call with the standing defaults injected ahead
of its own options. -/
private def injectMinted (st : TextSt) (env s : String) : String :=
  injectListingOpts (readEntries st env (mintedLang s)) s

/-- The head of a minted call a definition's text is, alone, or `none`. -/
private def shortcutHead (raws : Array Raw) (j : Nat) : Option (Array Raw) := do
  let k := skipSpaces raws (j + 1)
  guard (raws[k]? matches some (.word "()" _))
  let some (.group body _) := raws[skipSpaces raws (k + 1)]? | none
  let body := body.filter fun (r : Raw) => !(r matches .space)
  let some (Raw.ctrl c _) := body[0]? | none
  guard (c == "mintinline" || c == "mint")
  guard (body.back? matches some (.group _ _))
  guard (body.extract 1 (body.size - 1) |>.all fun r =>
    match r with
    | .group .. => false
    | _ => true)
  return body

/-- minted's command met as a control word, its call
assembled by a definition's text. -/
private def mintedRaws (raws : Array Raw) (start : Nat) : Option (String × Nat × Option Raw) := Id.run do
  let mut k := skipSpaces raws start
  let mut head := ""
  if raws[k]? matches some (.sym '[' _) then
    let mut m := k + 1
    let mut shut := false
    for _ in [k + 1:raws.size] do
      match raws[m]? with
      | some (.sym ']' _) =>
        shut := true
        break
      | some _ => m := m + 1
      | none => break
    unless shut do return none
    head := "[" ++ Parse.rawSrcList (raws.extract (k + 1) m).toList ++ "]"
    k := skipSpaces raws (m + 1)
  let some (.group lang _) := raws[k]? | return none
  head := head ++ "{" ++ Parse.rawSrc lang ++ "}"
  let c := skipSpaces raws (k + 1)
  match raws[c]? with
  | some (.group code _) => return some (head ++ "{" ++ Parse.rawSrcList code.toList ++ "}", c + 1, none)
  | some (.word w p) =>
    let some d := w.toList.head? | return none
    let mut text := ""
    let mut rest := (w.drop 1).toString
    let mut m := c
    for _ in [c:raws.size] do
      match rest.splitOn (String.singleton d) with
      | before :: after :: more =>
        let tail := String.intercalate (String.singleton d) (after :: more)
        return some (head ++ String.singleton d ++ text ++ before ++ String.singleton d, m + 1,
          if tail.isEmpty then none else some (.word tail p))
      | _ =>
        text := text ++ rest
        m := m + 1
        match raws[m]? with
        | some (.par _) | none => return none
        | some (.word w' _) => rest := w'
        | some r => rest := Parse.rawSrcOne r
    return none
  | _ => return none

mutual

-- conserves: none — spells siunitx constructs as their output text
private def textList (loc : Locale) (st : TextSt) (raws : Array Raw)
    (out : Array Raw) : List Raw → Nat → Nat → M (Array Raw × TextSt)
  | [], _, _ => return (out, st)
  | _ :: rest, i, skip + 1 => textList loc st raws out rest (i + 1) skip
  | .ctrl n pos :: rest, i, 0 => do
    if n == "define" then
      -- The definition wins: its name is the document's from here on.
      let j := skipSpaces raws (i + 1)
      let st := match raws[j]?.bind boundName with
        | some b =>
          let shortcuts := st.shortcuts.filter (·.1 != b)
          { st with defined := st.defined.push b
                    shortcuts := match shortcutHead raws j with
                      | some head => shortcuts.push (b, head)
                      | none => shortcuts }
        | none => st
      textList loc st raws ((out.push (.ctrl n pos)) ++ raws.extract (i + 1) (j + 1)) rest (i + 1)
        (j - i)
    else if let some (_, head) := st.shortcuts.find? (·.1 == n) then
      let joined := head ++ raws.extract (i + 1) raws.size
      match head[0]?, mintedRaws joined 1 with
      | some (Raw.ctrl c _), some (call, k, tail) =>
        let used := k - head.size
        markRead (readIds st c (mintedLang call))
        let out := out.push (.verb c (injectMinted st c call) pos)
        textList loc st raws (match tail with | some r => out.push r | none => out) rest (i + 1) used
      | _, _ => textList loc st raws (out.push (.ctrl n pos)) rest (i + 1) 0
    else if (n == "lstset" || n == "setminted" || n == "setmintedinline") &&
        !st.defined.contains n then
      let (lang, j) := if n == "lstset" then (none, i + 1) else takeOpt raws (i + 1)
      let (args, k) := takeGroups raws j 1
      let entries := KeyVal.items (rawSrc (args.getD 0 #[]))
      if n == "setmintedinline" then
        for e in entries do
          let key := (KeyVal.entry e).1
          -- premise: inlineDisplayChecks — lualatex sets inline code alike under each display key
          if mintedDisplayKeys.contains key then
            inertParam "\\setmintedinline" key s!"\\setmintedinline\{{e}}"
              "it configures a display, and inline code reads none" pos
      let lang := lang.map (·.trimAscii.toString)
      let decl := (← declareDefault st n lang pos, entries)
      let layered (layer : Array (String × DefaultLayer)) (lang : String) :=
        let old := ((layer.find? (·.1 == lang)).map (·.2)).getD #[]
        Ir.redeclare layer lang (old.push decl)
      let st := if n == "lstset" then { st with lstOpts := st.lstOpts.push decl }
        else if n == "setminted" then match lang with
          | none => { st with mintedOpts := st.mintedOpts.push decl }
          | some lang => { st with mintedLangOpts := layered st.mintedLangOpts lang }
        else match lang with
          | none => { st with inlineOpts := st.inlineOpts.push decl }
          | some lang => { st with inlineLangOpts := layered st.inlineLangOpts lang }
      textList loc st raws out rest (i + 1) (k - (i + 1))
    else if (n == "mintinline" || n == "mint") && !st.defined.contains n &&
        (mintedRaws raws (i + 1)).isSome then
      let (call, k, tail) := (mintedRaws raws (i + 1)).getD ("", i + 1, none)
      markRead (readIds st n (mintedLang call))
      let out := out.push (.verb n (injectMinted st n call) pos)
      textList loc st raws (match tail with | some r => out.push r | none => out) rest (i + 1)
        (k - (i + 1))
    else if siCtrls.contains n && !st.defined.contains n then
      let (repl, k) ← siCtrl loc n pos raws (i + 1)
      textList loc st raws (out ++ repl) rest (i + 1) (k - (i + 1))
    else
      -- listings' inline and file readers read `\lstset`'s defaults, refused or not.
      if (n == "lstinline" || n == "lstinputlisting") && !st.defined.contains n then
        markRead (readIds st "lstlisting" "")
      textList loc st raws (out.push (.ctrl n pos)) rest (i + 1) 0
  | .verb env s vpos :: rest, i, 0 => do
    -- A document's own `\mintinline` is the command its calls run.
    if (env == "mintinline" || env == "mint") && st.defined.contains env then
      let args := (Parse.verbatimRaws (← get).file s).map (rebase (fun _ => vpos) true)
      return ← textList loc st raws ((out.push (.ctrl env vpos)) ++ args) rest (i + 1) 0
    if env == "lstlisting" || env == "minted" || env == "mint" || env == "mintinline" then
      markRead (readIds st env (mintedLang s))
    let s := if env == "lstlisting" then injectListingOpts (readEntries st env "") s
      else if env == "minted" || env == "mint" || env == "mintinline" then injectMinted st env s
      else s
    textList loc st raws (out.push (.verb env s vpos)) rest (i + 1) 0
  | r :: rest, i, 0 => do
    let (r, st) ← textRaw loc st r
    textList loc st raws (out.push r) rest (i + 1) 0

/-- Descends into a group or environment; listing defaults are local to it, and
an input wrapper opens no group. -/
private def textRaw (loc : Locale) (st : TextSt) : Raw → M (Raw × TextSt)
  | .group body p => do
    let (body, inner) ← textList loc { st with depth := st.depth + 1 } body #[] body.toList 0 0
    return (.group body p, { st with defined := inner.defined })
  | .env n body p => do
    if let some file := Parse.inputEnvFile? n then
      let savedFile := (← get).file
      write fun s => { s with file := file }
      let (body, inner) ← textList loc { st with owned := st.owned || packageFile savedFile } body
        #[] body.toList 0 0
      write fun s => { s with file := savedFile }
      return (.env n body p, { inner with owned := st.owned })
    let (body, inner) ← textList loc st body #[] body.toList 0 0
    return (.env n body p, { st with defined := inner.defined })
  | r => return (r, st)

end

mutual

/-- The document's declared language tag, wherever it stands. -/
private def declaredTagList : List Raw → Option String
  | [] => none
  | .ctrl "pdfmeta" _ :: rest =>
    match (rest.dropWhile (· matches .space)).head? with
    | some (.group g _) =>
      match (Decl.splitEntries (rawSrc g)).findSome? (fun e =>
          match Decl.splitEntry e with
          | some ("language", v) =>
            match Decl.parseValue v with
            | some (.str tag) => some tag
            | _ => some (((v.replace "\"" "").trimAscii).toString)
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

/-- Whether the pass has anything to do: listing defaults or
a siunitx command anywhere. -/
private def textNeededList : List Raw → Bool
  | [] => false
  | .ctrl n _ :: rest =>
    n == "lstset" || n == "setminted" || n == "setmintedinline" || siCtrls.contains n ||
      n == "mintinline" || n == "mint" ||
      (n == "define" && ((rest.dropWhile (· matches .space)).head?.bind boundName).any
        (fun b => b == "mintinline" || b == "mint")) ||
      textNeededList rest
  | r :: rest => textNeededOne r || textNeededList rest

private def textNeededOne : Raw → Bool
  | .group b _ => textNeededList b.toList
  | .env _ b _ => textNeededList b.toList
  | _ => false

end

/-- The listings and siunitx pass, run right after `rewrite`. -/
public def rewriteText (file : String) (raws : Array Raw) (warned : Array String := #[]) :
    Array Raw × Array Diag × Array String :=
  if !textNeededList raws.toList then (raws, #[], warned) else
  let loc := ((declaredTagList raws.toList).bind Locale.forTag).getD Locale.en
  let go : M (Array Raw) := do
    let (out, _) ← textList loc {} raws #[] raws.toList 0 0
    nameUnreadDefaults
    return out
  let (out, st) := go.run
    { file := file, warned := warned, sourceTriggers := sourceTriggers file {} raws.toList }
  (out, st.diags, st.warned)

end LeanTex.Core.Compat
