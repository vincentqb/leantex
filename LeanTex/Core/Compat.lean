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
not a warning: nothing was lost. -/
def nativePackages : List String :=
  ["geometry", "hyperref", "xcolor", "color", "microtype", "enumitem", "babel",
   "fontspec", "url", "scrlayer-scrpage", "inputenc", "fontenc", "lmodern",
   "amsmath", "amssymb", "unicode-math", "parskip", "titlesec", "fancyhdr",
   "textcomp", "csquotes", "polyglossia", "graphicx", "booktabs", "array",
   "calc", "etoolbox", "xparse", "kvoptions", "setspace", "soul"]

/-- Classes that are an `article` with different defaults. -/
def articleClasses : List String :=
  ["scrartcl", "scrreprt", "scrbook", "report", "book", "memoir", "letter",
   "moderncv", "res"]

/-- Commands that configure TeX's own machinery and have no meaning here.
Dropped silently, arguments included; they say nothing about the document. -/
def inert : List (String × Nat) :=
  [("makeatletter", 0), ("makeatother", 0), ("relax", 0), ("noindent", 0),
   ("clearpairofpagestyles", 0), ("pagestyle", 1), ("urlstyle", 1),
   ("KOMAoptions", 1), ("newlength", 1), ("frenchspacing", 0),
   ("nonfrenchspacing", 0), ("sloppy", 0), ("raggedright", 0),
   ("raggedbottom", 0), ("flushbottom", 0), ("selectlanguage", 1),
   ("column", 1), ("midrule", 0), ("toprule", 0), ("bottomrule", 0),
   ("addlinespace", 0), ("hline", 0), ("cline", 1)]

/-- Beamer configuration commands: how many `{...}` arguments each carries.
The engine has no beamer templating layer, so each is skipped whole — the
construct, its options, and its arguments — with one warning naming it (and
its native spelling, where one exists). What must never happen is the
arguments leaking into elaboration as stray content (that was an E0313
cascade per construct). `\usetheme` is not here: it rewrites to `\theme`.
Neither is `\setbeamertemplate`: `frame footer` has a native meaning
(`\framefoot`) and its own arm; every other template skips there. -/
def beamerConfig : List (String × Nat) :=
  [("usecolortheme", 1), ("usefonttheme", 1),
   ("setbeameroption", 1),
   ("addtobeamertemplate", 3),
   ("setbeamerfont", 2), ("setbeamercolor", 2),
   ("beamertemplatenavigationsymbolsempty", 0),
   ("titlegraphic", 1)]

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
  /-- Running-content pieces gather across `\ihead`/`\chead`/`\ohead` and land
  as one declaration once the preamble ends. Slot 0 inner, 1 centre, 2 outer. -/
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

private abbrev M := StateM St

private def say (sev : Severity) (code msg : String) (pos : Pos) (help : Option String := none) :
    M Unit :=
  modify fun st => { st with diags := st.diags.push {
    severity := sev, code := code, message := msg
    span := some ⟨st.file, pos⟩, help := help } }

/-- Keys are namespaced (`ctrl:`, `spec:`, `beamer:`), never bare names: the
catch-all `beamer:` key set grows with `beamerConfig`, and a flat space would
let a future entry claim a literal arm's key and silence it. -/
private def sayOnce (key : String) (sev : Severity) (code msg : String) (pos : Pos)
    (help : Option String := none) : M Unit := do
  unless (← get).warned.contains key do
    modify fun st => { st with warned := st.warned.push key }
    say sev code msg pos help

/-- Every translation is one note in the same shape, so `-v` reads as a list
of things the document could say directly. -/
private def became (what native : String) (pos : Pos) : M Unit :=
  say .note "N0100" s!"{what} → {native}" pos

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

private def skipSpaces (raws : Array Raw) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [i:raws.size] do
    match raws[j]? with
    | some .space => j := j + 1
    | _ => break
  return j

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
      else dropped := dropped.push f
    | k :: v =>
      let k := k.trimAscii.toString
      let v := (String.intercalate "=" v).trimAscii.toString
      if ["margin", "vmargin", "hmargin", "width", "height"].contains k then
        keys := keys.push s!"{k} = {v}"
      else dropped := dropped.push k
    | [] => pure ()
  let native := s!"\\page\{ {String.intercalate ", " keys.toList} }"
  became "\\usepackage{geometry}" native pos
  unless dropped.isEmpty do
    say .note "N0101" s!"geometry keys without a native equivalent were dropped: \
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
  | "rgb" | "RGB" =>
    let parts := (value.splitOn ",").filterMap fun p =>
      Decl.parseDecimal p.trimAscii.toString
    match parts with
    | [(r, rs), (g, gs), (b, bs)] =>
      let mult := if model == "rgb" then 255 else 1
      let ch (m : Int) (s : Nat) : Nat := min 255 (m * mult / s).toNat
      let hex (n : Nat) : String :=
        let d := "0123456789ABCDEF".toList
        String.ofList [d[n / 16]!, d[n % 16]!]
      return some s!"#{hex (ch r rs)}{hex (ch g gs)}{hex (ch b bs)}"
    | _ => return none
  | _ =>
    say .warning "W0102" s!"colour model '{model}' is not supported; use HTML or rgb" pos
    return none

/-- KOMA's `\\sectionlinesformat` is a hook for drawing after a heading. The one
idiom worth reading is a rule in a colour, `\\textcolor{X}{\\leaders\\hrule …}`;
anything else is dropped. -/
private def sectionRule (src : String) (pos : Pos) : M (Array Raw) := do
  match (src.splitOn "\\textcolor {")[1]? with
  | some rest =>
    let color := ((rest.splitOn "}").headD "").trimAscii.toString
    if (src.splitOn "hrule").length > 1 && !color.isEmpty then
      let native := s!"\\style\{section}\{ rule = {color} }"
      became "\\sectionlinesformat" native pos
      synthAt native pos
    else return #[]
  | none => return #[]

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
      else if nativePackages.contains p then
        became s!"\\usepackage\{{p}}" "nothing: the engine does this itself" pos
      else
        say .warning "W0103" s!"package '{p}' is not supported; skipped" pos
          (help := "leantex has no packages: see PLAN.md for the native declarations")
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
  | "NewDocumentCommand" | "newcommand" | "providecommand"
  | "DeclareDocumentCommand" | "RenewDocumentCommand" =>
    let xparse := name.endsWith "DocumentCommand"
    let (nameArgs, j) := takeGroups raws start 1
    let some cmd := ctrlName (nameArgs.getD 0 #[]) | return none
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
    let native := s!"\\define \\{cmd}({spec})"
    became s!"\\{name}\{\\{cmd}}" (native ++ " {...}") pos
    modify fun st => { st with bodyNext := 1 }
    return some (← synthAt native pos, j)
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
      if name.endsWith "head" then { st with head := st.head.push (slot, src) }
      else { st with foot := st.foot.push (slot, src) }
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
    let (_, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    let native := s!"\\block[before = {lengthSrc (args.getD 0 #[])}]\{}"
    became "\\vspace" native pos
    return some (← synthAt native pos, k)
  | "thepage" => return some (#[.ctrl "pagenumber" pos], start)
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
    say .warning "W0106" "expl3 code (\\ExplSyntaxOn … \\ExplSyntaxOff) is not supported; skipped" pos
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
        say .note "N0105" s!"\\setkomafont\{{element}}: not a styleable element; ignored" pos
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
  | "renewcommand" =>
    -- \\renewcommand\\sectionlinesformat[4]{...} is the spelling KOMA documents;
    -- other renewals define a command like \\newcommand does.
    let (nameArgs, j) := takeGroups raws start 1
    let some cmd := ctrlName (nameArgs.getD 0 #[]) | return none
    let (count, j) := takeOpt raws j
    if cmd == "sectionlinesformat" then
      let (args, k) := takeGroups raws j 1
      return some (← sectionRule (rawSrc (args.getD 0 #[])) pos, k)
    let (dflt, j) := takeOpt raws j
    let n := (count.bind String.toNat?).getD 0
    let spec := if dflt.isSome then "o" ++ String.ofList (List.replicate (n - 1) 'm')
      else String.ofList (List.replicate n 'm')
    let native := s!"\\define \\{cmd}({signature spec})"
    became s!"\\renewcommand\{\\{cmd}}" (native ++ " {...}") pos
    modify fun st => { st with bodyNext := 1 }
    return some (← synthAt native pos, j)
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
    sayOnce "ctrl:directlua" .warning "W0104"
      "'\\directlua' is Lua code for luatex; skipped" pos
      (help := "there is no Lua here; see PLAN.md for the native declarations")
    return some (#[], k)
  | "def" | "edef" | "gdef" | "xdef" =>
    -- TeX's macro layer: consume through the body group, so the definition
    -- never leaks into the document as stray content.
    let mut k := start
    let mut found := false
    for j in [start:raws.size] do
      match raws[j]? with
      | some (.group _ _) =>
        found := true
        k := j + 1
        break
      | some _ => k := j + 1
      | none => break
    sayOnce "ctrl:def" .warning "W0104" s!"TeX '\\{name}' is not supported; skipped" pos
      (help := "\\define declares typed commands")
    return some (#[], if found then k else start)
  | "newenvironment" | "renewenvironment" =>
    -- `\newenvironment{name}[n][default]{begin}{end}` is the native
    -- `\defineenv{name}(a1: content, ...) {begin} {end}`. The two body
    -- groups stay in the stream and are announced as macro bodies, so `#k`
    -- becomes `\ak` in each and idioms inside them translate as usual.
    let (args, j) := takeGroups raws start 1
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
    sayOnce "ctrl:ifdefined" .warning "W0104"
      s!"TeX conditional ('\\{name}' … '\\fi') is not supported; skipped whole" pos
    return some (#[], k)
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
      let (_, k) := takeGroups raws j 1
      sayOnce "beamer:setbeamertemplate" .warning "W0104"
        "'\\setbeamertemplate' is beamer configuration the engine does not have; skipped" pos
        (help := beamerNative.lookup "setbeamertemplate")
      return some (#[], k)
  | "usetheme" =>
    let (_, j) := takeOpt raws start
    let (args, k) := takeGroups raws j 1
    let tname := (rawSrc (args.getD 0 #[])).trimAscii.toString
    let native := s!"\\theme\{{tname}}"
    became "\\usetheme" native pos
    -- Only a theme the engine ships turns the themed mappings on: an
    -- unknown name leaves the document unthemed (W0314 says so), and
    -- \alert keeps its unthemed bold stand-in.
    if (Theme.find? tname).isSome then
      modify fun st => { st with themed := true }
    return some (← synthAt native pos, k)
  | "nolinkurl" =>
    -- Its group stays in the stream: the URL renders as its own text.
    became "\\nolinkurl" "the URL as plain text" pos
    return some (#[], start)
  | "multicolumn" =>
    -- `\multicolumn{n}{align}{text}`: spans are not laid out — tables
    -- degrade to rows and W0308 says so — but the cell's text is content
    -- and the span count and alignment spec are not.
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
  | "setbeamercovered" =>
    -- beamer's default covering is invisible and `transparent` makes it
    -- show dimmed; this engine's covering is dim-not-hide always (PLAN
    -- M5), so `transparent` asks for what already happens — agreement, not
    -- missing configuration, and no warning. `transparent=<n>` shows
    -- covered text at n% opaqueness (beamer manual, \setbeamercovered:
    -- 0 transparent .. 100 opaque; 15 is the default), which over the page
    -- is an n% mix of the body ink into it: the covered colour, declared.
    -- Everything else (invisible, dynamic, still/again covered) asks for
    -- hiding or per-slide opacity the engine deliberately does not do.
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
        -- Unthemed there is no fg/bg to mix over: the page is white, the
        -- ink black.
        let native := if (← get).themed then s!"\\palette\{ covered = fg!{n}!bg }"
          else s!"\\palette\{ covered = black!{n} }"
        became "\\setbeamercovered" native pos
        return some (← synthAt native pos, k)
      else
        sayOnce "beamer:setbeamercovered" .warning "W0104"
          s!"'\\setbeamercovered\{{src}}' asks for {if n == 0 then "invisible" else "undimmed"} \
covered content; the engine always dims (dim-not-hide)" pos
          (help := "\\palette{ covered = ... } sets the dim colour")
        return some (#[], k)
    | none =>
      sayOnce "beamer:setbeamercovered" .warning "W0104"
        s!"'\\setbeamercovered\{{src}}' is not modelled; covered content always \
dims (dim-not-hide), it is never hidden" pos
        (help := "\\palette{ covered = ... } sets the dim colour; 'transparent' \
and 'transparent=<n>' are understood")
      return some (#[], k)
  | _ =>
    match beamerConfig.lookup name with
    | some n =>
      let (_, j) := takeOpt raws start
      let (_, k) := takeGroups raws j n
      sayOnce ("beamer:" ++ name) .warning "W0104"
        s!"'\\{name}' is beamer configuration the engine does not have; skipped" pos
        (help := (beamerNative.lookup name).getD
          "a theme is a token bundle here: \\theme selects one, and \\palette \
and \\tokens declare the design directly")
      return some (#[], k)
    | none =>
    match inert.lookup name with
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
