/-
Permutation oracle: swapping two adjacent preamble declarations of different, order-free heads
leaves the elaborated `Doc` and the diagnostic codes unchanged.
Usage: lake env lean --run scripts/compose-fuzz.lean
-/
import LeanTex

open LeanTex.Core

/-- Heads the oracle may swap: `\theme`, the name-declaring and name-reading heads, and
`\documentclass`, whose class a diagnostic reads, are excluded wholesale. -/
def safeHeads : List String :=
  ["page", "pdfmeta", "fonts", "output", "chrome", "assert", "allow",
   "runninghead", "runningfoot", "logo", "title", "subtitle", "author",
   "institute", "date", "urlstyle", "figures"]

/-- Every head that starts a new declaration unit during segmentation. -/
def declHeads : List String :=
  safeHeads ++ ["documentclass", "define", "defineenv", "tokens", "palette",
    "style", "theme", "usetheme", "maketitle"]

/-- The preamble's declaration units: each starts at a top-level `.ctrl` naming a known
head; unit 0 is what precedes the first head. -/
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

/-- The fields a block declaration writes, at field granularity, so two blocks commute
only when these sets are disjoint; none for a head without a keyed block. -/
def unitFields (head : String) (raws : Array Parse.Raw) : Option (List String) := do
  let body ← raws.findSome? fun r => match r with
    | .group b _ => some b
    | _ => none
  let entries := (Entries.read .native body).toList
  let keyFields (k : String) : List String :=
    match head, k with
    | "page", "size" => ["width", "height"]
    | "page", "margin" => ["vmargin", "hmargin", "block"]
    | "page", "vmargin" => ["vmargin", "block"]
    | "page", "tmargin" | "page", "bmargin" | "page", "textheight" | "page", "vmarginratio"
    | "page", "vscale" | "page", "textheight-under" => ["block"]
    | "fonts", "rm" => ["body"]
    | "fonts", "sf" => ["sans"]
    | "fonts", "tt" => ["mono"]
    | _, _ => [k]
  match head with
  | "page" | "pdfmeta" | "fonts" =>
    some (entries.flatMap fun e =>
      match e.pair? with
      | some (k, _) => keyFields k
      | none => ["<malformed>"])
  | "output" =>
    -- A bare entry continues the last opened list (`formats`, `profiles`).
    some ((entries.foldl (fun (acc : List String × String) e =>
      match e.pair? with
      | some (k, _) => (acc.1 ++ [k], if k == "profiles" then k else "formats")
      | none => (acc.1 ++ [acc.2], acc.2)) ([], "formats")).1)
  | "chrome" =>
    some (entries.flatMap fun e =>
      match e.pair?, (e.value.map Array.toList : Option (List Parse.Raw)) with
      | some (k, _), some [.group g _] =>
        (Entries.read .native g).toList.map fun se =>
          match se.pair? with
          | some (sk, _) => k ++ "." ++ sk
          | none => k ++ ".<malformed>"
      | some (k, _), _ => [k]
      | none, _ => ["<malformed>"])
  | _ => none

/-- Elaborate raws to the comparison key: the document, and the diagnostic codes as a
sorted list. -/
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
            -- Same head: only with extractable, field-disjoint key sets.
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
  "\\output{ formats = pdf, profiles = pdf/a-4 }\n" ++
  "\\figures{ convert = none }\n" ++
  "\\chrome{ footer = { left = \\sectiontitle } }\n" ++
  "\\runninghead[from = 2]{An Invented Head}\n" ++
  "\\runningfoot{An Invented Foot}\n" ++
  "\\logo{L}\n" ++
  "\\assert{ pages <= 4 }\n" ++
  "\\allow{W0318}\n" ++
  "\\begin{document}\n\\begin{frame}{A}\nx\n\\end{frame}\n\\end{document}\n"

/-- Same-head adjacent blocks with field-disjoint keys, which the different-head sweep
cannot see. -/
def syntheticSameHead : String :=
  "\\documentclass{slides}\n" ++
  "\\page{ margin = 18mm }\n" ++
  "\\page{ leading = 1.3 }\n" ++
  "\\fonts{ body = \"Nonexistent Face\" }\n" ++
  "\\fonts{ mono = \"Another Nonexistent Face\" }\n" ++
  "\\pdfmeta{ subject = \"an invented subject\" }\n" ++
  "\\pdfmeta{ keywords = \"invented, synthetic\" }\n" ++
  "\\output{ formats = pdf }\n" ++
  "\\output{ css = own, color = device }\n" ++
  "\\output{ profiles = pdf/a-4, pdf/ua-2 }\n" ++
  "\\chrome{ footer = { left = \\sectiontitle } }\n" ++
  "\\chrome{ footer = { right = \\framenumber } }\n" ++
  "\\begin{document}\n\\begin{frame}{A}\nx\n\\end{frame}\n\\end{document}\n"

/-- `\urlstyle` beside the inline-content heads that can hold a `\url`: a logo and a
running head. -/
def syntheticUrl : String :=
  "\\documentclass{slides}\n" ++
  "\\logo{\\url{https://example.org/logo}}\n" ++
  "\\urlstyle{sf}\n" ++
  "\\runninghead{\\url{https://example.org/head}}\n" ++
  "\\date{An Invented Date}\n" ++
  "\\begin{document}\n\\begin{frame}{A}\nx\n\\end{frame}\n\\end{document}\n"

/-- The title parts, exercised where `\maketitle` sets them: an author holding a `\url`
beside the selector. -/
def syntheticUrlTitle : String :=
  "\\documentclass{article}\n" ++
  "\\title{An Invented Title}\n" ++
  "\\author{Placeholder Name \\url{https://example.org/me}}\n" ++
  "\\urlstyle{same}\n" ++
  "\\date{An Invented Date \\url{https://example.org/date}}\n" ++
  "\\begin{document}\n\\maketitle\nx\n\\end{document}\n"

def main : IO UInt32 := do
  let mut bad := 0
  let mut pairs := 0
  bad := bad + (← checkSource "synthetic.tex" synthetic)
  bad := bad + (← checkSource "synthetic-samehead.tex" syntheticSameHead)
  bad := bad + (← checkSource "synthetic-urlstyle.tex" syntheticUrl)
  bad := bad + (← checkSource "synthetic-urlstyle-title.tex" syntheticUrlTitle)
  let dir : System.FilePath := "testdata/corpus"
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
