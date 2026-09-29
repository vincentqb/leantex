/-
Differential probe for xcolor's rgb, gray, and cmyk PDF operators. Run from
repository root after building the executable:

  lake build leantex && lake env lean --run scripts/color-diff.lean

The reference PDF disables stream and object compression. Each synthetic case
is built independently by LuaLaTeX and leantex, then both files are parsed
through `PdfRead`; comparisons are over PDF numeric semantics, while the
LuaLaTeX spelling is also pinned to distinguish direct values from
`\definecolor`'s five-decimal normalization.
-/
import LeanTex

open LeanTex.Core

structure ColorProbe where
  label : String
  model : String
  source : String
  defined : Bool
  operator : String
  expectedRef : Array String

structure ColorOp where
  operator : String
  operands : Array String
  deriving Repr

def probes : Array ColorProbe := #[
  { label := "direct-rgb", model := "rgb", source := ".000009,.123456,.999999",
    defined := false, operator := "rg", expectedRef := #[".000009", ".123456", ".999999"] },
  { label := "defined-rgb", model := "rgb", source := ".000009,.123456,.999999",
    defined := true, operator := "rg", expectedRef := #["0", "0.12345", "0.99999"] },
  { label := "direct-gray", model := "gray", source := ".500009",
    defined := false, operator := "g", expectedRef := #[".500009"] },
  { label := "defined-gray", model := "gray", source := ".500009",
    defined := true, operator := "g", expectedRef := #["0.5"] },
  { label := "direct-cmyk", model := "cmyk",
    source := ".000009,.00001,.123456,.999999", defined := false, operator := "k",
    expectedRef := #[".000009", ".00001", ".123456", ".999999"] },
  { label := "defined-cmyk", model := "cmyk",
    source := ".000009,.00001,.123456,.999999", defined := true, operator := "k",
    expectedRef := #["0", "0.00001", "0.12345", "0.99999"] },
  { label := "mixed-separators", model := "rgb", source := "0.1, 0.2 0.3",
    defined := false, operator := "rg", expectedRef := #["0.1", "0.2", "0.3"] }
]

def texSource (p : ColorProbe) (reference : Bool) : String :=
  let compression := if reference then
      "\\pdfvariable compresslevel=0\n\\pdfvariable objcompresslevel=0\n"
    else ""
  let definition := if p.defined then
      s!"\\definecolor\{probe}\{{p.model}}\{{p.source}}\n"
    else ""
  let use := if p.defined then "\\pagecolor{probe}x"
    else s!"\\pagecolor[{p.model}]\{{p.source}}x"
  "\\documentclass{article}\n\\usepackage{xcolor}\n" ++ compression ++ definition ++
    "\\begin{document}\n" ++ use ++ "\n\\end{document}\n"

def pageContent (pdf : ByteArray) : Except String String := do
  let es := (← PdfRead.objects pdf).val
  let some page := es.find? fun e => e.val.get? "Type" == some (.name "Page")
    | throw "no page object"
  let refs : Array Nat ← match page.val.get? "Contents" with
    | some (.ref n _) => pure #[n]
    | some (.arr xs) => pure (xs.filterMap fun x => match x with
        | .ref n _ => some n
        | _ => none)
    | _ => throw "page has no content reference"
  let mut out := ""
  for n in refs do
    let some entry := es.find? (·.num == n) | throw s!"content object {n} is absent"
    let some bytes ← entry.decoded | throw s!"object {n} is not a stream"
    let some text := String.fromUTF8? bytes | throw s!"content object {n} is not UTF-8"
    out := out ++ text ++ "\n"
  return out

def arity : String → Nat
  | "g" => 1
  | "rg" => 3
  | "k" => 4
  | _ => 0

def parsedOps (content : String) : Array ColorOp := Id.run do
  let tokens := (content.split Char.isWhitespace).filterMap fun s =>
    let t := s.toString
    if t.isEmpty then none else some t
  let mut out : Array ColorOp := #[]
  for (token, i) in tokens.toArray.zipIdx do
    let n := arity token
    if n > 0 && n ≤ i then
      out := out.push { operator := token, operands := (tokens.drop (i - n) |>.take n).toArray }
  return out

def decimalEq (a b : String) : Bool :=
  match Decl.parseDecimal a, Decl.parseDecimal b with
  | some (an, ad), some (bn, bd) => an * (bd : Int) == bn * (ad : Int)
  | _, _ => false

def opSemEq (a b : ColorOp) : Bool :=
  a.operator == b.operator && a.operands.size == b.operands.size &&
    (a.operands.zip b.operands).all fun (x, y) => decimalEq x y

def nonzero (op : ColorOp) : Bool := op.operands.any fun x => !decimalEq x "0"

def firstOp (content operator : String) : Option ColorOp :=
  (parsedOps content).find? fun op => op.operator == operator && nonzero op

def renderOp (op : ColorOp) : String :=
  String.intercalate " " op.operands.toList ++ " " ++ op.operator

def compile (cmd : String) (args : Array String) (cwd : System.FilePath) : IO UInt32 := do
  let out ← IO.Process.output { cmd, args, cwd }
  if out.exitCode != 0 then
    IO.eprintln (out.stdout ++ out.stderr)
  return out.exitCode

def main : IO UInt32 := do
  let haveLua ← try
    pure ((← IO.Process.output { cmd := "lualatex", args := #["--version"] }).exitCode == 0)
  catch _ => pure false
  if !haveLua then
    IO.eprintln "color-diff: lualatex not found"
    return 2
  let bin ← IO.FS.realPath ".lake/build/bin/leantex"
  let work ← IO.FS.createTempDir
  try
    let mut failed := false
    for p in probes do
      IO.FS.writeFile (work / "reference.tex") (texSource p true)
      IO.FS.writeFile (work / "engine.tex") (texSource p false)
      if (← compile "lualatex"
          #["--interaction=batchmode", "--halt-on-error", "reference.tex"] work) != 0 then
        IO.eprintln s!"color-diff: {p.label}: LuaLaTeX failed"
        failed := true
        continue
      let enginePdf := work / "engine.pdf"
      if (← compile bin.toString
          #["-q", "build", (work / "engine.tex").toString, "-o", enginePdf.toString]
          (← IO.currentDir)) != 0 then
        IO.eprintln s!"color-diff: {p.label}: leantex failed"
        failed := true
        continue
      let refContent ← match pageContent (← IO.FS.readBinFile (work / "reference.pdf")) with
        | .ok content => pure content
        | .error e => IO.eprintln s!"color-diff: {p.label}: reference {e}"; failed := true; continue
      let engineContent ← match pageContent (← IO.FS.readBinFile enginePdf) with
        | .ok content => pure content
        | .error e => IO.eprintln s!"color-diff: {p.label}: engine {e}"; failed := true; continue
      let expected : ColorOp := { operator := p.operator, operands := p.expectedRef }
      let some refOp := firstOp refContent p.operator
        | IO.eprintln s!"color-diff: {p.label}: reference operator absent"; failed := true; continue
      let some engineOp := firstOp engineContent p.operator
        | IO.eprintln s!"color-diff: {p.label}: engine operator absent; got {repr (parsedOps engineContent)}"; failed := true; continue
      IO.println s!"{p.label}: LuaLaTeX {renderOp refOp}; leantex {renderOp engineOp}"
      if refOp.operator != expected.operator || refOp.operands != expected.operands then
        IO.eprintln s!"color-diff: {p.label}: reference spelling moved; expected {renderOp expected}"
        failed := true
      if !opSemEq refOp engineOp then
        IO.eprintln s!"color-diff: {p.label}: numeric operator mismatch"
        failed := true
    if failed then return 1
    IO.println s!"color-diff: {probes.size} xcolor operator cases match"
    return 0
  finally
    IO.FS.removeDirAll work
