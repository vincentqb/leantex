/-
Permutation oracle for preamble commutation — T1's evidence while the
theorem stays open (an executable oracle is evidence, not a theorem):
swapping two adjacent preamble declarations with different heads, neither
of which is `\theme` or a name-declaring/name-reading head, must leave the
elaborated `Doc` unchanged and the diagnostic codes the same multiset.
Run with:

  lake env lean --run scripts/compose-fuzz.lean

Kept out of `lake test` (the kp-fuzz precedent): it re-elaborates every
corpus document once per adjacent pair, plus a synthetic preamble that
exercises every swappable pair the corpus does not.
-/
import LeanTex

open LeanTex.Core

/-- Heads the oracle may swap. Deliberately coarser than T1's exception
list: `\theme` (positional by design, its own named exception), the
name-declaring and name-reading heads (`\define`, `\defineenv`, `\tokens`,
`\palette`, `\style` — reference→referent order is essential, E1-E3 in the
audit), and same-head pairs (same-key last-wins is inherently ordered) are
all excluded wholesale rather than pairwise. `\documentclass` is excluded
because a class-conditional diagnostic (W0318) legitimately reads the class
declared so far. -/
def safeHeads : List String :=
  ["page", "pdfmeta", "fonts", "output", "chrome", "assert", "allow",
   "runninghead", "runningfoot", "logo", "title", "subtitle", "author",
   "institute", "date"]

/-- Every head that starts a new declaration unit during segmentation. -/
def declHeads : List String :=
  safeHeads ++ ["documentclass", "define", "defineenv", "tokens", "palette",
    "style", "theme", "usetheme", "maketitle"]

/-- Split the preamble into declaration units: a unit starts at a top-level
`.ctrl` whose name is a known head and carries everything up to the next
one. Unit 0 is whatever precedes the first head (unswappable). -/
def segment (pre : Array Parse.Raw) : Array (Option String × Array Parse.Raw) := Id.run do
  let mut units : Array (Option String × Array Parse.Raw) := #[]
  let mut cur : Array Parse.Raw := #[]
  let mut head : Option String := none
  for r in pre do
    match r with
    | .ctrl n _ =>
      if declHeads.contains n then
        unless cur.isEmpty && head.isNone do
          units := units.push (head, cur)
        head := some n
        cur := #[r]
      else
        cur := cur.push r
    | _ => cur := cur.push r
  unless cur.isEmpty && head.isNone do
    units := units.push (head, cur)
  return units

def flatten (units : Array (Option String × Array Parse.Raw)) : Array Parse.Raw :=
  units.foldl (fun acc u => acc ++ u.2) #[]

/-- The fields a block declaration writes, at field granularity: `size`
writes width and height, `margin` both margins, a `\fonts` alias its slot —
two blocks commute only when these sets are disjoint, not merely their key
spellings. Heads without a keyed block return none: same-head swaps are
attempted only where a key set is extractable. -/
def unitFields (head : String) (raws : Array Parse.Raw) : Option (List String) := do
  let body ← raws.findSome? fun r => match r with
    | .group b _ => some b
    | _ => none
  let src := Parse.rawSrc body
  let keyFields (k : String) : List String :=
    match head, k with
    | "page", "size" => ["width", "height"]
    | "page", "margin" => ["vmargin", "hmargin"]
    | "fonts", "rm" => ["body"]
    | "fonts", "sf" => ["sans"]
    | "fonts", "tt" => ["mono"]
    | _, _ => [k]
  match head with
  | "page" | "pdfmeta" | "fonts" =>
    some ((Decl.splitEntries src).flatMap fun e =>
      match Decl.splitEntry e with
      | some (k, _) => keyFields k
      | none => ["<malformed>"])
  | "output" =>
    some ((Decl.splitEntries src).map fun e =>
      match Decl.splitEntry e with
      | some (k, _) => k
      | none => "formats")
  | "chrome" =>
    some ((Decl.splitEntries src).flatMap fun e =>
      match Decl.splitEntry e with
      | some (k, v) =>
        let inner := v.trimAscii.toString
        if inner.startsWith "{" && inner.endsWith "}" && inner.length ≥ 2 then
          (Decl.splitEntries (String.ofList (inner.toList.drop 1).dropLast)).map fun se =>
            match Decl.splitEntry se with
            | some (sk, _) => k ++ "." ++ sk
            | none => k ++ ".<malformed>"
        else [k]
      | none => ["<malformed>"])
  | _ => none

/-- Elaborate raws to the comparison key: the document, and the diagnostic
codes as a sorted list (a swap may reorder emission; it must not change
what fires). -/
def key (file : String) (raws : Array Parse.Raw) : Ir.Doc × List String :=
  let (doc, ds) := Elab.runRaws file raws
  (doc, (ds.map (·.code)).toList.mergeSort (· ≤ ·))

def checkSource (label : String) (src : String) : IO Nat := do
  let file := label
  let (toks, _) := Lex.lex file src
  let (raws, _) := Parse.parse file toks
  let docIdx := raws.findIdx? fun r => match r with
    | .env "document" _ _ => true
    | _ => false
  let cut := docIdx.getD raws.size
  let pre := raws.extract 0 cut
  let rest := raws.extract cut raws.size
  let units := segment pre
  let base := key file raws
  let mut bad := 0
  for i in [0:units.size] do
    if h : i + 1 < units.size then
      let (h1, u1) := units[i]!
      let (h2, u2) := units[i + 1]
      let swappable := match h1, h2 with
        | some a, some b =>
          if a != b then safeHeads.contains a && safeHeads.contains b
          else
            -- Same head: only with extractable, field-disjoint key sets
            -- (T1's "touch disjoint keys"; same-key order is the one
            -- essential order last-wins carries).
            safeHeads.contains a &&
              (match unitFields a u1, unitFields a u2 with
               | some k1, some k2 => k1.all (fun k => !k2.contains k)
               | _, _ => false)
        | _, _ => false
      if swappable then
        let swapped := (units.set! i units[i + 1]).set! (i + 1) units[i]!
        let raws' := flatten swapped ++ rest
        let k := key file raws'
        unless k == base do
          bad := bad + 1
          IO.eprintln s!"{label}: swapping '\\{h1.getD ""}' and '\\{h2.getD ""}' \
(units {i}, {i + 1}) changes the document"
          unless k.1 == base.1 do IO.eprintln "  the Doc differs"
          unless k.2 == base.2 do
            IO.eprintln s!"  diag codes {base.2} became {k.2}"
  return bad

/-- One preamble naming every swappable head once, so every adjacent pair
is exercised somewhere even though no corpus document repeats them all. -/
def synthetic : String :=
  "\\documentclass{slides}\n" ++
  "\\title{An Invented Title}\n" ++
  "\\author{Placeholder Name}\n" ++
  "\\pdfmeta{ subject = \"an invented subject\" }\n" ++
  "\\page{ margin = 18mm }\n" ++
  "\\fonts{ body = \"Nonexistent Face\" }\n" ++
  "\\output{ formats = pdf }\n" ++
  "\\chrome{ footer = { left = \\sectiontitle } }\n" ++
  "\\runninghead[from = 2]{An Invented Head}\n" ++
  "\\runningfoot{An Invented Foot}\n" ++
  "\\logo{L}\n" ++
  "\\assert{ pages <= 4 }\n" ++
  "\\allow{W0318}\n" ++
  "\\begin{document}\n\\begin{frame}{A}\nx\n\\end{frame}\n\\end{document}\n"

/-- Same-head adjacent blocks with field-disjoint keys: the shape whose
across-block accidents (I1, the chrome wholesale replace) the different-head
sweep cannot see. -/
def syntheticSameHead : String :=
  "\\documentclass{slides}\n" ++
  "\\page{ margin = 18mm }\n" ++
  "\\page{ leading = 1.3 }\n" ++
  "\\fonts{ body = \"Nonexistent Face\" }\n" ++
  "\\fonts{ mono = \"Another Nonexistent Face\" }\n" ++
  "\\pdfmeta{ subject = \"an invented subject\" }\n" ++
  "\\pdfmeta{ keywords = \"invented, synthetic\" }\n" ++
  "\\output{ formats = pdf }\n" ++
  "\\output{ css = own }\n" ++
  "\\chrome{ footer = { left = \\sectiontitle } }\n" ++
  "\\chrome{ footer = { right = \\framenumber } }\n" ++
  "\\begin{document}\n\\begin{frame}{A}\nx\n\\end{frame}\n\\end{document}\n"

def main : IO UInt32 := do
  let mut bad := 0
  let mut pairs := 0
  bad := bad + (← checkSource "synthetic.tex" synthetic)
  bad := bad + (← checkSource "synthetic-samehead.tex" syntheticSameHead)
  let dir : System.FilePath := "tests/corpus"
  let entries ← dir.readDir
  let texs := (entries.map (·.path)).filter (·.extension == some "tex")
  for p in texs.qsort (fun a b => a.toString < b.toString) do
    let src ← IO.FS.readFile p
    bad := bad + (← checkSource p.fileName.get! src)
    pairs := pairs + 1
  if bad == 0 then
    IO.println s!"compose-fuzz: every swappable adjacent pair commutes \
(synthetic + {pairs} corpus files)"
    return 0
  else
    IO.eprintln s!"compose-fuzz: {bad} non-commuting swaps"
    return 1
