import LeanTex.Core.Lex
import LeanTex.Core.Parse
import LeanTex.Core.Decl

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
   "calc", "etoolbox", "xparse", "kvoptions", "setspace"]

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
   ("raggedbottom", 0), ("flushbottom", 0), ("selectlanguage", 1)]

private structure St where
  file : String
  diags : Array Diag := #[]
  /-- Running-content pieces gather across `\ihead`/`\chead`/`\ohead` and land
  as one declaration once the preamble ends. Slot 0 inner, 1 centre, 2 outer. -/
  head : Array (Nat × String) := #[]
  foot : Array (Nat × String) := #[]
  runPos : Pos := ⟨1, 1⟩
  /-- The next group is a macro body, where `#k` names a parameter. -/
  bodyNext : Bool := false

private abbrev M := StateM St

private def say (sev : Severity) (code msg : String) (pos : Pos) (help : Option String := none) :
    M Unit :=
  modify fun st => { st with diags := st.diags.push {
    severity := sev, code := code, message := msg
    span := some ⟨st.file, pos⟩, help := help } }

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

/-- The control word inside a group, ignoring whitespace around it. -/
private def ctrlName (raws : Array Raw) : Option String :=
  match raws.toList.filter (fun r => match r with | .space => false | _ => true) with
  | [.ctrl n _] => some n
  | _ => none

/-- An xparse argument spec, or a plain count, as native parameters
`a1 … an`. Only the argument *types* matter here: `m` is mandatory, and `o`,
`O{..}`, `d..`, `D..{..}`, `s`, `t.` are all optional. Payloads such as
defaults and delimiters ride inside braces that the parser has already
grouped, so a spec is read from its own source text and braces are skipped. -/
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
    s!"a{k + 1}{if c == 'o' then "?" else ""}: text"
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
      became s!"\\documentclass\{{cls}}" s!"\\documentclass{o}\{article}" pos
      return some (← synthAt s!"\\documentclass{o}\{article}" pos, k)
    else if cls == "beamer" then
      let o := match opt with | some o => s!"[{o}]" | none => ""
      became "\\documentclass{beamer}" s!"\\documentclass{o}\{slides}" pos
      return some (← synthAt s!"\\documentclass{o}\{slides}" pos, k)
    else return none
  | "babelfont" | "setmainfont" | "setsansfont" | "setmonofont" =>
    let (slotArgs, j) := if name == "babelfont" then takeGroups raws start 1 else (#[], start)
    let (_, j) := takeOpt raws j
    let (args, k) := takeGroups raws j 1
    let slot := match name with
      | "babelfont" => match rawSrc (slotArgs.getD 0 #[]) with
        | "rm" => "body" | "sf" => "sans" | "tt" => "mono" | s => s
      | "setmainfont" => "body" | "setsansfont" => "sans" | _ => "mono"
    let family := rawSrc (args.getD 0 #[])
    let native := s!"\\fonts\{ {slot} = \"{family}\" }"
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
      | some n =>
        let native := s!"\\tokens\{ {n} = {lengthSrc args[1]} }"
        became s!"\\setlength\{\\{n}}" native pos
        return some (← synthAt native pos, k)
      | none => return none
    else return none
  | "NewDocumentCommand" | "newcommand" | "renewcommand" | "providecommand"
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
    modify fun st => { st with bodyNext := true }
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
    let (_, k) := takeGroups raws start 1
    say .note "N0104" "\\thispagestyle has no effect yet; running content appears on every page" pos
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
  | "setkomafont" | "RedeclareSectionCommand" | "setlist" | "sectionlinesformat" =>
    let (_, j) := takeOpt raws start
    let (_, k) := takeGroups raws j (if name == "setkomafont" then 2 else 1)
    say .note "N0105" s!"\\{name}: element styling is planned (PLAN.md M3d); default style used" pos
    return some (#[], k)
  | _ =>
    match inert.lookup name with
    | some n =>
      let (_, k) := takeGroups raws start n
      return some (#[], k)
    | none => return none
  termination_by structural name => name

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
    modify fun st => { st with bodyNext := true }
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
    -- A group is a macro body when a definition announced one; the flag is
    -- consumed here so only that group is read as a body.
    let isBody := (← get).bodyNext
    modify fun st => { st with bodyNext := false }
    return .group (← rewriteList (inBody || isBody) body #[] body.toList 0 0) p
  | .env n body p => do
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
  unless st.head.isEmpty do
    let native := s!"\\runninghead\{{line st.head}}"
    became "\\ihead / \\chead / \\ohead" native st.runPos
    out := out ++ (← synthAt native st.runPos)
  unless st.foot.isEmpty do
    let native := s!"\\runningfoot\{{line st.foot}}"
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
