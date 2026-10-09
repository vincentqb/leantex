module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- The document's own reference list, `thebibliography` (classes.dtx),
against its citations: resolved with no `.bib` file requested. Kernel
numbering — the list counter steps only for an entry without a label
(latex.ltx `\@bibitem` against `\@lbibitem`), so `\bibitem[X]` cites as X
and the next unlabelled entry takes the next number; natbib's author-year
labels (`Knuth(1984)`) cite as names and year; a key no entry answers is
W0351. The checks read the resolved IR (`Bib.apply` with no sources, as a
build runs it) and the shipped page. -/
def ownBibChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let doc (pre body : String) :=
    s!"\\documentclass\{article}\n{pre}\\begin\{document}\n{body}\n\\end\{document}"
  let list := "\\begin{thebibliography}{9}\n\\bibitem{a} A. Author.\n\\newblock Title one.\n\n\
\\bibitem[X]{b} B. Author. Title two.\n\n\\bibitem{c} C. Author.\n\\end{thebibliography}"
  let src := doc "" s!"Citing \\cite\{a} and \\cite\{b,c}.\n\n{list}"
  let (d0, ds0) := elabStr src
  let (d, ds) := Bib.apply #[] d0
  let paraText (b : Ir.Block) : String := match b with
    | .para xs => Ir.plainText xs
    | _ => ""
  t "thebibliography requests no .bib file" (Ir.bibRefs d0).isEmpty
  t "thebibliography's citations resolve, with no diagnostic but newblock's note"
    ((ds0 ++ ds).all (·.severity == Severity.note))
  t "kernel numbering: a label cites as written and steps no counter"
    ((d.body[0]?.map paraText) == some "Citing [1] and [X, 2].")
  let items := match d.body.find? (· matches .bibliography _ _ _) with
    | some (.bibliography _ _ its) => its
    | _ => #[]
  t "the list keeps its entries in source order, marked as cited"
    (items.map (·.key) == #["a", "b", "c"] &&
      items.map (·.marker) == #[some "1", some "X", some "2"] &&
      (items[0]?.map (Ir.plainText ·.content)) == some "A. Author. Title one.")
  t "the list opens with its References heading"
    (d.body.any fun b => b matches .section 1 true none _)
  let ay := doc "\\usepackage[round]{natbib}\n"
    ("\\citet{k} and \\citep{p}.\n\n\\begin{thebibliography}{9}\n\\bibitem[Knuth(1984)]{k} \
D. Knuth. The book.\n\\bibitem[Knuth and Plass(1981)]{p} D. Knuth and M. Plass. Breaking.\n\
\\end{thebibliography}")
  let (e0, _) := elabStr ay
  let (e, es) := Bib.apply #[] e0
  t "natbib author-year labels cite as names and year"
    ((e.body[0]?.map paraText) == some "Knuth (1984) and (Knuth and Plass, 1981)." &&
      es.isEmpty)
  let (m0, _) := elabStr (doc "" s!"See \\cite\{zz}.\n\n{list}")
  let (_, ms) := Bib.apply #[] m0
  t "a key no entry answers is W0351, named by its key"
    (ms.map (·.code) == #["W0351"] && ms.all (·.subject == some "zz"))
  match ← serifFacesSet with
  | none => failures ref "own bibliography: the shipped serif faces did not load"
  | some fonts =>
    let (pd, _) := Bib.apply #[] d0
    let shipped := String.join ((bodyLines (layoutOf fonts pd)).toList.map (lineText ·))
    t "the page ships the heading, the marks and the entries"
      (hasStr shipped "References" && hasStr shipped "[X]" && hasStr shipped "Title two." &&
        hasStr shipped "[2]" && hasStr shipped "Citing [1] and [X, 2].")
