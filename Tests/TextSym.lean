module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- A paragraph's text, when the document is one paragraph of text runs. -/
def soleParaText (d : Ir.Doc) : Option String :=
  match d.body with
  | #[.para xs] => xs.foldl (fun acc x => acc.bind fun s =>
      match x with
      | .text t => some (s ++ t)
      | _ => none) (some "")
  | _ => none

/-- The generated TU tables (`TextSymData`) against the page: every symbol and composite elaborates
to its scalar, whichever table answers first. -/
def textSymChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let body (s : String) := s!"\\documentclass\{article}\n\\begin\{document}\n{s}\n\\end\{document}"
  for (name, v) in TextSymData.symbols do
    let (d, ds) := elabStr (body s!"x\\{name}\{}y")
    t s!"text symbol \\{name} sets U+{String.ofList (Nat.toDigits 16 v.toNat)} between its neighbours"
      (ds.isEmpty && soleParaText d == some ("x" ++ String.ofList [v] ++ "y"))
  for (acc, base, v) in TextSymData.composites do
    let b := if base.startsWith "\\" then Elab.accentBase (base.drop 1).toString else some base.front
    let mark := TextSymData.accents.lookup acc
    t s!"tuenc composite \\{acc}\{{base}} is the NFC composition of its pair"
      ((mark.bind fun m => b.bind (Bib.composeAccent m ·)) == some v)
    let (d, ds) := elabStr (body s!"\\{acc}\{{base}}")
    t s!"\\{acc}\{{base}} elaborates to its composite"
      (ds.isEmpty && soleParaText d == some (String.ofList [v]))
  for (acc, v) in TextSymData.emptyBase do
    let (d, ds) := elabStr (body s!"a\\{acc}\{}b")
    t s!"\\{acc}\{} over an empty base sets its composite"
      (ds.isEmpty && soleParaText d == some ("a" ++ String.ofList [v] ++ "b"))
  -- A control word swallows the space after it, as in TeX: `\S 1` is "§1".
  let (d1, ds1) := elabStr (body "\\S 1 \\dag x \\v c")
  t "a symbol word swallows the space after it"
    (ds1.isEmpty && soleParaText d1 == some "§1 †x č")
  let (d2, ds2) := elabStr (body "\\lq q\\rq{} \\LaTeXe")
  t "the kernel quote words and the LaTeX2e logo"
    (ds2.isEmpty && soleParaText d2 == some "‘q’ LaTeX2ε")
  -- A `\` ending a line is the control space `\^^M`.
  let (d3, ds3) := elabStr (body "i.e.\\\n   the rest")
  t "a line ending in a backslash is the control space"
    (ds3.isEmpty && soleParaText d3 == some "i.e. the rest")
  let (d4, ds4) := elabStr (body "one\\\n\ntwo")
  t "a control space before a blank line still ends the paragraph"
    (ds4.isEmpty && d4.body.size == 2)
  t "an accent with no precomposed form over its base still warns"
    ((elabStr (body "\\b{a}")).2.map (·.code) == #["W0301"])
  -- A role is invocable only while no symbol spells its name: the symbol tables are read before the palette.
  t "no shipped palette role is spelled by a text symbol"
    (Theme.builtin.all fun th => (deckBundle th).entries.toList.all fun e =>
      (Elab.escapeOf e.1.key).isNone)
  t "a document palette role a text symbol spells is refused by name"
    ((elabStr ("\\documentclass{article}\n\\palette{ dag = #112233 }\n" ++
      "\\begin{document}\nx\n\\end{document}")).2.map (·.code) == #["E0303"])
  match ← serifFacesSet with
  | none => failures ref "text symbols: the shipped serif faces did not load"
  | some fonts =>
    let shipped := pageTextOf fonts (body "\\S 2, \\P 3, \\dag, \\pounds 5, \\OE uvre, \
Dvo\\v{r}\\'ak, Erd\\H{o}s, \\.{Z}\\'o\\l{}w, \\textquoteleft q\\textquoteright")
    t "the page ships the symbols and the composed letters"
      (hasStr shipped "§2" && hasStr shipped "¶3" && hasStr shipped "†" &&
        hasStr shipped "£5" && hasStr shipped "Œuvre" && hasStr shipped "Dvořák" &&
        hasStr shipped "Erdős" && hasStr shipped "Żółw" && hasStr shipped "‘q’")
