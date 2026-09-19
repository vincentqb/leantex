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
   "fontspec", "url", "xurl", "scrlayer-scrpage", "inputenc", "fontenc", "lmodern",
   "amsmath", "amssymb", "amsfonts", "unicode-math", "parskip", "titlesec", "fancyhdr",
   "textcomp", "csquotes", "polyglossia", "graphicx", "booktabs", "array",
   "calc", "etoolbox", "xparse", "kvoptions", "setspace", "soul", "tikz",
   "caption", "subcaption", "nicefrac", "multirow",
   "appendixnumberbeamer"]

/-- Classes that are an `article` with different defaults. -/
def articleClasses : List String :=
  ["scrartcl", "scrreprt", "scrbook", "report", "book", "memoir", "letter",
   "moderncv", "res"]

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
   ("fontseries", 1,
    "'\\fontseries' selects a font series; the family's regular weight is used",
    none),
   ("sloppy", 0,
    "'\\sloppy' loosens TeX's line-breaking tolerance; the breaker keeps \
its own and an overfull line warns by itself", none),
   ("selectlanguage", 1,
    "'\\selectlanguage' would change the hyphenation language; patterns stay English",
    some "hyphenation patterns are English-only; \\page{ hyphenate = off } turns them off")]

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

private def say (code : DiagCode) (msg : String) (pos : Pos) (help : Option String := none) :
    M Unit :=
  modify fun st => { st with
    diags := st.diags.push (Diag.of code msg (some ⟨st.file, pos⟩) help) }

/-- Keys are namespaced (`ctrl:`, `spec:`, `beamer:`), never bare names: the
catch-all `beamer:` key set grows with `beamerConfig`, and a flat space would
let a future entry claim a literal arm's key and silence it. -/
private def sayOnce (key : String) (code : DiagCode) (msg : String) (pos : Pos)
    (help : Option String := none) : M Unit := do
  unless (← get).warned.contains key do
    modify fun st => { st with warned := st.warned.push key }
    say code msg pos help

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

/-- A TeX length in the native spelling: `0.5\rhythm` is `0.5 * rhythm`,
`\relax` vanishes. -/
private def lengthSrc (raws : Array Raw) : String := Id.run do
  let mut s := ""
  let mut prevNumber := false
  for r in raws do
    match r with
    | .ctrl "relax" _ => pure ()
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

/-- `\usepackage[opts]{geometry}` → `\page{...}`. -/
private def geometry (opts : String) (pos : Pos) : M (Array Raw) := do
  let mut keys : Array String := #[]
  let mut dropped : Array String := #[]
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
      if ["margin", "vmargin", "hmargin", "width", "height"].contains k then
        keys := keys.push s!"{k} = {lengthOfTeX v}"
      else dropped := dropped.push k
    | [] => pure ()
  let native := s!"\\page\{ {String.intercalate ", " keys.toList} }"
  became "\\usepackage{geometry}" native pos
  unless dropped.isEmpty do
    say .W0101 s!"geometry keys without a native equivalent were dropped: \
{String.intercalate ", " dropped.toList}" pos
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
  | "usepackage" =>
    let (opt, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    if args.isEmpty then return none
    let pkgs := (rawSrc (args.getD 0 #[])).splitOn "," |>.map (·.trimAscii.toString)
    let mut out : Array Raw := #[]
    for p in pkgs do
      if p == "geometry" then
        out := out ++ (← geometry (opt.getD "") pos)
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
      else if nativePackages.contains p then
        became s!"\\usepackage\{{p}}" "nothing: the engine does this itself" pos
      else
        say .W0103 s!"package '{p}' is not supported; skipped" pos
    return some (out, k)
  | "documentclass" =>
    let (opt, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    let cls := rawSrc (args.getD 0 #[])
    if articleClasses.contains cls then
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
      let native := s!"\\documentclass{o}\{article}\\page\{ parskip = {komaSkip.getD "0pt"} }"
      became s!"\\documentclass\{{cls}}" native pos
      return some (← synthAt native pos, k)
    else if cls == "beamer" then
      let o := match opt with | some o => s!"[{o}]" | none => ""
      became "\\documentclass{beamer}" s!"\\documentclass{o}\{slides}" pos
      return some (← synthAt s!"\\documentclass{o}\{slides}" pos, k)
    else return none
  | "babelfont" | "setmainfont" | "setsansfont" | "setmonofont" =>
    let (slotArgs, j) := if name == "babelfont" then takeGroups raws start 1 else (#[], start)
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
        parts := parts.push s!"{slot}.{variant} = \"{f}\""
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
      let native := s!"\\palette\{ {rawSrc args[0]} = {rawSrc args[1]} }"
      became "\\colorlet" native pos
      return some (← synthAt native pos, k)
    else return none
  | "geometry" =>
    -- The command form: the same keys the package options carry.
    let (args, k) := takeGroups raws start 1
    if args.isEmpty then return none
    return some (← geometry (rawSrc (args.getD 0 #[])) pos, k)
  | "setlength" =>
    let (args, k) := takeGroups raws start 2
    if h : args.size = 2 then
      match ctrlName args[0] with
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
    | "empty" =>
      modify fun st => { st with head := #[], foot := #[] }
      became "\\pagestyle{empty}" "no running furniture, the state the engine starts from" pos
      return some (#[], k)
    | _ =>
      sayOnce "ctrl:pagestyle" .W0104
        s!"'\\pagestyle\{{v}}' names page furniture the engine does not model; ignored" pos
        (help := "\\runninghead / \\runningfoot declare the page furniture")
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
  | "color" =>
    -- `\color{n}` colours to the end of the group, which is what a bare
    -- palette name does.
    let (args, k) := takeGroups raws start 1
    let n := rawSrc (args.getD 0 #[])
    became s!"\\color\{{n}}" s!"\\{n}" pos
    return some (#[.ctrl n pos], k)
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
        if expanding then
          sayOnce ("ctrl:" ++ name) .W0357
            s!"'\\{name}' defines by expanding at definition time; the engine has no \
expansion step, so the definition is skipped" pos
            (help := "\\define \\name(...) {body} declares typed commands")
        else
          sayOnce "ctrl:def-delimited" .W0357
            s!"'\\{name}' with a delimited parameter text is a TeX scanning program; \
the definition is skipped" pos
            (help := "\\define \\name(...) {body} declares typed commands")
        return some (#[], k2)
    | none =>
      sayOnce "ctrl:def" .W0357 s!"TeX '\\{name}' is not supported; skipped" pos
        (help := "\\define \\name(...) {body} declares typed commands")
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
  return out

/-- Rewrite a whole parsed document. The gathered running content lands just
before `\begin{document}`, where a declaration belongs. -/
def rewrite (file : String) (raws : Array Raw) : Array Raw × Array Diag :=
  let go : M (Array Raw) := do
    let raws ← condList raws #[] [] raws.toList 0
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

end LeanTex.Core.Compat
