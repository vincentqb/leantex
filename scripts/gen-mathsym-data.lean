/-
Regenerate LeanTex/Core/MathSymData.lean: the math symbols fontmath.ltx, amsfonts and amssymb
declare, each with its declaring file's class and unicode-math's scalar.
Usage: lake env lean --run scripts/gen-mathsym-data.lean
-/
import scripts.GenData
import Std.Data.HashMap

open GenData

/-- Legacy names unicode-math spells differently, `(package name, unicode-math name)`,
each judged by unicode-math's description of the target glyph. -/
def renamed : List (String × String) :=
  [("square", "mdlgwhtsquare"), ("blacksquare", "mdlgblksquare"),
   ("lozenge", "mdlgwhtlozenge"), ("blacklozenge", "mdlgblklozenge"),
   ("circlearrowright", "cwopencirclearrow"), ("circlearrowleft", "acwopencirclearrow"),
   ("ntriangleleft", "nvartriangleleft"), ("ntriangleright", "nvartriangleright"),
   ("doteqdot", "Doteq"), ("centerdot", "cdotp"),
   ("dashrightarrow", "rightdasharrow"), ("dashleftarrow", "leftdasharrow"),
   ("yen", "mathyen")]

/-- The packages read, in load order: amssymb loads amsfonts first. -/
def packages : List String := ["amsfonts", "amssymb"]

/-- Kernel commands unicode-math lists as symbols that take an argument in LaTeX, which
the parser reads structurally. -/
def kernelConstructs : List String := ["sqrt"]

/-- The first `n` brace groups at the start of `s`, whitespace between
them skipped; fewer when anything else comes first. -/
def groups (s : String) (n : Nat) : List String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  let mut depth := 0
  for c in s.toList do
    if out.size == n then break
    if depth == 0 then
      if c == '{' then
        depth := 1
        cur := ""
      else if !c.isWhitespace then
        break
    else if c == '{' then
      depth := depth + 1
      cur := cur.push c
    else if c == '}' then
      depth := depth - 1
      if depth == 0 then out := out.push cur else cur := cur.push c
    else
      cur := cur.push c
  return out.toList

/-- The control word at the start of `s` (after one backslash), or none. -/
def ctrlWord (s : String) : Option String :=
  match s.trimAscii.toString.toList with
  | '\\' :: rest =>
    let w := rest.takeWhile Char.isAlpha
    if w.isEmpty then none else some (String.ofList w)
  | _ => none

/-- A declared command's name: a control word with no `@` (LaTeX internals
are not commands a document calls). -/
def publicName (g : String) : Option String := do
  let n ← ctrlWord g
  let t := g.trimAscii.toString
  if t.length == n.length + 1 then some n else none

inductive Decl where
  | sym (name cls slot : String)
  | alias (name target : String)
  | composite (name cls : String)
  deriving Inhabited

def Decl.name : Decl → String
  | .sym n _ _ | .alias n _ | .composite n _ => n

/-- The class a parameterless definition's body opens with: an explicit `\mathrel{…}` or a
sibling, an ordinary atom for a box or group, empty otherwise. -/
def compositeClass (body : String) : String :=
  let b := body.trimAscii.toString
  let lead := [("\\mathinner", "mathinner"), ("\\mathrel", "mathrel"), ("\\mathbin", "mathbin"),
    ("\\mathopen", "mathopen"), ("\\mathclose", "mathclose"), ("\\mathop", "mathop"),
    ("\\mathpunct", "mathpunct"), ("\\mathord", "mathord"), ("\\mathit", "mathord"),
    ("\\noexpand\\mathhexbox", "mathord"), ("\\vbox", "mathord"), ("\\hbox", "mathord"),
    ("{", "mathord")]
  ((lead.find? fun (p, _) => b.startsWith p).map (·.2)).getD ""

/-- The symbol declarations of one package file, in file order. -/
def declsOf (text : String) : Array Decl := Id.run do
  let body := String.intercalate "\n" ((text.splitOn "\n").map uncomment)
  let mut out : Array (Nat × Decl) := #[]
  let at_ (kw : String) : List (Nat × String) := Id.run do
    let ps := body.splitOn kw
    let mut pos := 0
    let mut acc : Array (Nat × String) := #[]
    for p in ps do
      acc := acc.push (pos, p)
      pos := pos + p.length + kw.length
    return (acc.toList.drop 1)
  for kw in ["DeclareMathSymbol", "DeclareMathDelimiter"] do
    for (pos, piece) in at_ kw do
      match groups piece 4 with
      | [n, c, f, s] =>
        if let (some name, some cls) := (publicName n, ctrlWord c) then
          out := out.push (pos, .sym name cls s!"{f}:{s}")
      | _ => pure ()
  for (pos, piece) in at_ "\\global\\let" do
    match ctrlWord piece with
    | some name =>
      let rest := (piece.trimAscii.toString.drop (name.length + 1)).toString
      if let some target := ctrlWord rest then
        unless target == "undefined" do out := out.push (pos, .alias name target)
    | none => pure ()
  for kw in ["\\xdef", "\\edef"] do
    for (pos, piece) in at_ kw do
      if let some name := ctrlWord piece then
        let rest := (piece.trimAscii.toString.drop (name.length + 1)).toString
        if rest.startsWith "{" then
          out := out.push (pos, .composite name (compositeClass ((groups rest 1).headD "")))
  -- The kernel's composites, `\DeclareRobustCommand\name{…}`; one taking an argument is a
  -- construct, not a symbol.
  for (pos, piece) in at_ "\\DeclareRobustCommand" do
    let p := piece.trimAscii.toString
    let p := if p.startsWith "{" then (p.drop 1).toString else p
    if let some name := ctrlWord p then
      let rest := (p.drop (name.length + 1)).toString
      let rest := (if rest.startsWith "}" then (rest.drop 1).toString else rest).trimAscii.toString
      if rest.startsWith "{" then
        out := out.push (pos, .composite name (compositeClass ((groups rest 1).headD "")))
  return (out.qsort (·.1 < ·.1)).map (·.2)

/-- unicode-math's table: name ↦ (scalar, class). -/
def umTable (text : String) : Std.HashMap String (Nat × String) := Id.run do
  let mut m : Std.HashMap String (Nat × String) := {}
  for piece in (text.splitOn "\\UnicodeMathSymbol").drop 1 do
    match groups piece 3 with
    | [hex, n, c] =>
      let hex := (hex.drop 1).toString
      let v := hex.foldl (fun a ch =>
        a * 16 + (if ch.isDigit then ch.toNat - 48 else ch.toNat - 55)) 0
      if let (some name, some cls) := (ctrlWord n, ctrlWord c) then
        unless m.contains name do m := m.insert name (v, cls)
    | _ => pure ()
  return m

/-- unicode-math's one-word aliases (`\protected\def\a{\b}`,
`\cs_set_protected:Npn \a {\b}`) and normal-style alphabet positions. -/
def umAliases (text : String) : Std.HashMap String String × Std.HashMap String Nat := Id.run do
  let mut al : Std.HashMap String String := {}
  let mut usv : Std.HashMap String Nat := {}
  for line in text.splitOn "\n" do
    let l := line.trimAscii.toString
    for kw in ["\\protected\\def", "\\cs_set_protected:Npn"] do
      if l.startsWith kw then
        let rest := (l.drop kw.length).toString
        if let some a := ctrlWord rest then
          let after := ((rest.trimAscii.toString).drop (a.length + 1)).toString
          match groups after 1 with
          | [g] =>
            if let some b := ctrlWord g then
              if g.trimAscii.toString == "\\" ++ b then al := al.insert a b
          | _ => pure ()
    if l.startsWith "\\usv_set:nnn {normal}" then
      match groups ((l.drop "\\usv_set:nnn".length).toString) 3 with
      | [_, n, hex] =>
        let hex := hex.trimAscii.toString
        if hex.startsWith "\"" then
          let v := (hex.drop 1).toString.foldl (fun a ch =>
            a * 16 + (if ch.isDigit then ch.toNat - 48 else ch.toNat - 55)) 0
          usv := usv.insert n v
      | _ => pure ()
  return (al, usv)

def classOf : String → Option String
  | "mathord" | "mathalpha" => some ".ord"
  | "mathop" => some ".op"
  | "mathbin" => some ".bin"
  | "mathrel" => some ".rel"
  | "mathopen" => some ".opening"
  | "mathclose" => some ".closing"
  | "mathpunct" => some ".punct"
  | "mathinner" => some ".inner"
  | _ => none

def hex4 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n) |>.toUpper
  String.ofList (List.replicate (4 - s.length) '0') ++ s

def charLit (n : Nat) : String :=
  if n < 0x10000 then s!"'\\u{hex4 n}'" else s!"'{String.ofList [Char.ofNat n]}'"

/-- A Lean list literal of strings, wrapped before column 100. -/
def strList (xs : Array String) : String := Id.run do
  let mut out := "["
  let mut col := 3
  let mut first := true
  for x in xs do
    let item := s!"\"{x}\""
    if first then
      out := out ++ item
      col := col + item.length
    else if col + item.length + 2 > 96 then
      out := out ++ ",\n   " ++ item
      col := 3 + item.length
    else
      out := out ++ ", " ++ item
      col := col + item.length + 2
    first := false
  return out ++ "]"

def provides (text : String) : String :=
  let kw := if (text.splitOn "\\ProvidesPackage").length > 1 then "\\ProvidesPackage" else "\\ProvidesFile"
  match (text.splitOn kw).drop 1 with
  | piece :: _ =>
    let g := groups piece 1
    let rest := (piece.dropWhile (· != '}')).drop 1
    let stamp := ((rest.toString.dropWhile (· != '[')).drop 1).takeWhile (· != ']')
    s!"{g.headD ""} {" ".intercalate ((stamp.toString.split Char.isWhitespace).toList.map (·.toString) |>.filter (!·.isEmpty))}"
  | [] => "?"

/-- The kernel's documented math symbols: the names the LaTeX2e manual's "Math formulas"
chapter indexes (`testdata/coverage/latex2e-index.txt`) that lualatex confirmed as a math
symbol or a command. -/
def kernelNames (index : String) : Array String := Id.run do
  let mut out : Array String := #[]
  for line in index.splitOn "\n" do
    match line.splitOn "\t" with
    | [n, "Math formulas", m] => if m == "math_given" || m == "call" then out := out.push n
    | _ => pure ()
  return out

def main : IO UInt32 := do
  let umT ← IO.FS.readFile (← locate "unicode-math-table.tex")
  let umS ← IO.FS.readFile (← locate "unicode-math-luatex.sty")
  let umTop ← IO.FS.readFile (← locate "unicode-math.sty")
  let table := umTable umT
  let (al, usv) := umAliases umS
  let umVersion := match (umTop.splitOn "\\ProvidesExplPackage{unicode-math}").drop 1 with
    | piece :: _ => String.intercalate " " ((groups piece 2).map fun (g : String) => g.trimAscii.toString)
    | [] => "?"
  let mut rows : Array (String × String × Nat) := #[]
  let mut refused : Array String := #[]
  let mut names : Array (String × Array String) := #[]
  let mut stamps : Array String := #[]
  let byName (n : String) : Option (Nat × String) :=
    match usv[n]? with
    | some v => some (v, "mathord")
    | none =>
      match table[n]? with
      | some v => some v
      | none =>
        match al[n]?.bind (table[·]?) with
        | some v => some v
        | none => (renamed.lookup n).bind (table[·]?)
  -- The kernel first, classes from fontmath.ltx; accents, radicals and fences are no rows.
  let fontmath ← IO.FS.readFile (← locate "fontmath.ltx")
  stamps := stamps.push (provides fontmath)
  let fmDecls := declsOf fontmath
  let index ← IO.FS.readFile "testdata/coverage/latex2e-index.txt"
  stamps := stamps.push ("additional kernel names: testdata/coverage/latex2e-index.txt, " ++
    "chapter Math formulas")
  -- The index is not the declaration list, so fontmath.ltx's declarations join it.
  let candidates := kernelNames index ++ fmDecls.map Decl.name
  for n in candidates do
    if kernelConstructs.contains n then continue
    if let some (v, umCls) := byName n then
      let declared := (fmDecls.findSome? fun d => match d with
        | .sym m c _ => if m == n then some c else none
        | .composite m c => if m == n && !c.isEmpty then some c else none
        | _ => none).getD umCls
      if let some cls := classOf declared then
        unless rows.any (·.1 == n) do rows := rows.push (n, cls, v)
  for pkg in packages do
    let text ← IO.FS.readFile (← locate s!"{pkg}.sty")
    stamps := stamps.push (provides text)
    let ds := declsOf text
    -- The first declaration of a name stands; a later one re-declares it.
    let mut seen : Array String := #[]
    let mut own : Array Decl := #[]
    for d in ds do
      unless seen.contains d.name do
        seen := seen.push d.name
        own := own.push d
    let mut resolved : Std.HashMap String (Nat × String) := {}
    -- Rules 1–4 first, then aliases and slot siblings, which read what the
    -- first pass resolved (one level is all these packages use).
    for d in own do
      if let some v := byName d.name then resolved := resolved.insert d.name v
    for d in own do
      unless resolved.contains d.name do
        match d with
        | .alias n t =>
          if let some v := resolved[t]? <|> byName t then resolved := resolved.insert n v
        | .sym n _ slot =>
          let sib := own.findSome? fun e => match e with
            | .sym m _ s => if s == slot && m != n then resolved[m]? else none
            | _ => none
          if let some v := sib then resolved := resolved.insert n v
        | _ => pure ()
    let mut pkgNames : Array String := #[]
    for d in own do
      pkgNames := pkgNames.push d.name
      match resolved[d.name]? with
      | none => refused := refused.push d.name
      | some (v, umCls) =>
        let ownClass : Decl → String
          | .sym _ c _ => c
          | .composite _ c => if c.isEmpty then umCls else c
          | .alias _ _ => umCls
        let declared := match d with
          | .alias _ t => match own.find? (·.name == t) with
            | some e => ownClass e
            | none => umCls
          | e => ownClass e
        let some cls := classOf declared
          | die s!"{pkg}: \\{d.name} has class '{declared}', which no atom class names"
        unless rows.any (·.1 == d.name) do rows := rows.push (d.name, cls, v)
    names := names.push (pkg, pkgNames)
  let mut out := s!"module

/-
Generated by scripts/gen-mathsym-data.lean; do not edit by hand. Regenerate with:
  lake env lean --run scripts/gen-mathsym-data.lean

Sources, read from the TeX tree and never vendored:
{String.intercalate "\n" (stamps.toList.map (s!"- {·}"))}
- unicode-math {umVersion} (unicode-math-table.tex, unicode-math-luatex.sty;
  LPPL 1.3c).
Each row is a command the kernel or a package declares, its TeX atom class
as the declaring file gives it, and the scalar unicode-math sets for it;
the rules that find the scalar are the generator's header. This module
carries only data: the parser reads it through `MathParse.ctrlAtom`, and its
contracts are checked by the suite.
-/
public import LeanTex.Core.Math

namespace LeanTex.Core.MathSymData

open LeanTex.Core.Math

/-- The symbol rows: the kernel's documented and declared symbols, then each package's;
the first declaration of a name stands. -/
public def rows : List (String × MathClass × Char) :=
  ["
  let mut first := true
  for (n, c, v) in rows do
    out := out ++ (if first then "" else ",\n   ") ++ s!"(\"{n}\", {c}, {charLit v})"
    first := false
  out := out ++ "]\n"
  for (pkg, ns) in names do
    out := out ++ s!"\n/-- Every symbol command {pkg}.sty declares, in file order. -/\n\
public def {pkg} : List String :=\n  {strList ns}\n"
  out := out ++ s!"\n/-- The declared commands no rule answers: no scalar of their own in \
unicode-math, so they stay unknown to the parser. -/\npublic def refused : List String :=\n  \
{strList refused}\n\nend LeanTex.Core.MathSymData\n"
  IO.FS.writeFile "LeanTex/Core/MathSymData.lean" out
  IO.println s!"wrote LeanTex/Core/MathSymData.lean: {rows.size} rows, {refused.size} refused"
  return 0
