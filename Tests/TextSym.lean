import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- A paragraph's text, when the document is one paragraph of text runs. -/
def soleParaText (d : Ir.Doc) : Option String :=
  match d.body with
  | #[.para xs] => xs.foldl (fun acc x => acc.bind fun s =>
      match x with
      | .text t => some (s ++ t)
      | _ => none) (some "")
  | _ => none

/-- The generated TU tables (`TextSymData`) against the page. Every symbol
row, spelled `x\name{}y`, elaborates to its scalar between the two letters
with no diagnostic — whichever table answers it first (`Elab.escapes`,
`Bib.charCommands`, `Lex.textSymbols`, `Compat`'s literal rewrites), so a
hand row that shadows a generated one sets the same scalar. Every
tuenc.def composite is the scalar NFC composes its accent and base to
(`Bib.composeAccent`), and spelled `\accent{base}` it elaborates to that
scalar. The shipped page carries a sample of both, set in the test face. -/
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
  -- The kernel's own definitions beside the TU table: latex.ltx's `\lq`
  -- and `\rq` through the quote ligatures, and the LaTeX2e logo's word.
  let (d2, ds2) := elabStr (body "\\lq q\\rq{} \\LaTeXe")
  t "the kernel quote words and the LaTeX2e logo"
    (ds2.isEmpty && soleParaText d2 == some "‘q’ LaTeX2ε")
  -- An accent pair with no precomposed scalar still falls through by name.
  t "an accent with no precomposed form over its base still warns"
    ((elabStr (body "\\b{a}")).2.map (·.code) == #["W0301"])
  -- A role is invocable only while no symbol spells its name first: the
  -- inline dispatch reads the symbol tables before the palette.
  t "no shipped palette role is spelled by a text symbol"
    (Theme.builtin.all fun th => th.palette.entries.toList.all fun e =>
      (Elab.escapeOf e.1).isNone)
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
