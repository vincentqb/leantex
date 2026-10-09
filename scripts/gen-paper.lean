/-
Regenerates bench/paper.tex and bench/refs.bib — a deterministic,
paper-shaped bench fixture: two-level sections with \paragraph runs,
numbered equations cross-referenced with \eqref, figure and table floats
with captions, natbib citations resolved from the .bib beside it, and an
appendix — the constructs of an academic paper, with invented content
(the private paper it is shaped after never enters this repo; compare
construct counts locally when recalibrating). Targets roughly 10 pages.
Fonts and images come from testdata/corpus, so the run is hermetic. Run with:

  lake env lean --run scripts/gen-paper.lean
-/

def words : Array String := #[
  "escarpment", "sandstone", "tributary", "glaciation", "stratification",
  "permafrost", "archipelago", "metamorphism", "watercourse", "riverbed",
  "floodplain", "conglomerate", "limestone", "headwaters", "estuary",
  "topography", "groundwater", "riverbanks", "cartography", "alluvium"]

def sentence (seed len : Nat) : String := Id.run do
  let mut s := "The"
  for i in [0:len] do
    s := s ++ " " ++ words.getD ((seed * 7 + i * 13) % words.size) ""
  return s ++ " holds."

def para (seed : Nat) (cite : Option String := none) : String := Id.run do
  let mut p := sentence seed 9
  for i in [1:5] do
    p := p ++ " " ++ sentence (seed + i * 31) (7 + (seed + i) % 5)
  match cite with
  | some c => return p ++ " " ++ c
  | none => return p

def bibKeys : Array String := Id.run do
  let mut ks : Array String := #[]
  for i in [0:12] do
    ks := ks.push s!"ref{i + 2010}"
  return ks

def bibEntry (i : Nat) : String :=
  let k := bibKeys.getD i ""
  let a := words.getD ((i * 3) % words.size) ""
  let b := words.getD ((i * 5 + 2) % words.size) ""
  s!"@article\{{k},
  author = \{Placeholder, A. and Invented, B.},
  title = \{On {a} and {b}},
  journal = \{Journal of Synthetic Results},
  year = \{{2010 + i}},
  url = \{https://example.org/{k}}
}
"

def cite (i : Nat) : String :=
  let k := bibKeys.getD (i % bibKeys.size) ""
  if i % 3 == 0 then s!"\\citet\{{k}} agree." else s!"It is known \\citep\{{k}}."

def equation (i : Nat) : String :=
  s!"\\begin\{equation}\\label\{eq:{i}}
x_\{{i}} = \\frac\{a_\{{i}}}\{b_\{{i}}} + \\sqrt\{c_\{{i}}}
\\end\{equation}"

def figure (i : Nat) : String :=
  s!"\\begin\{figure}
\\includegraphics[width=0.4\\textwidth]\{../testdata/corpus/rects.png}
\\caption\{An invented measurement, run {i}.}
\\end\{figure}"

def table (i : Nat) : String :=
  s!"\\begin\{table}
\\begin\{tabular}\{lll}\\toprule
run & median & spread \\\\ \\midrule
{i} & 12.{i} & 0.{i} \\\\
{i + 1} & 14.{i} & 0.{i} \\\\ \\bottomrule
\\end\{tabular}
\\caption\{Invented medians, batch {i}.}
\\end\{table}"

def gen : String := Id.run do
  let mut out : Array String := #[
    "\\documentclass{article}",
    "\\usepackage{natbib}",
    "\\usepackage{booktabs}",
    "\\usepackage{graphicx}",
    "\\usepackage{amsmath}",
    "\\fonts{ dir = \"../testdata/corpus/fonts\", body = \"Source Serif Pro\", math = \"Fira Math\" }",
    "\\title{A Synthetic Paper-Shaped Benchmark}",
    "\\author{Placeholder Name (placeholder@example.org)}",
    "\\begin{document}",
    "\\maketitle", ""]
  let mut eq := 0
  for s in [1:6] do
    out := out.push s!"\\section\{Invented section {s}}"
    out := out.push (para (s * 100) (some (cite s))) |>.push ""
    for sub in [1:4] do
      let seed := s * 100 + sub * 10
      out := out.push s!"\\subsection\{Invented subsection {s}.{sub}}"
      out := out.push (para seed (some (cite (s * 3 + sub)))) |>.push ""
      eq := eq + 1
      out := out.push (equation eq) |>.push ""
      out := out.push (s!"\\paragraph\{A named run} As \\eqref\{eq:{eq}} shows, " ++
        para (seed + 5))
      out := out.push ""
      if sub == 1 then
        out := out.push (if s % 2 == 0 then table s else figure s) |>.push ""
  out := out.push "\\appendix"
  out := out.push "\\section{Invented appendix}"
  out := out.push (para 9000 (some (cite 11))) |>.push ""
  out := out.push "\\bibliographystyle{plainnat}"
  out := out.push "\\bibliography{refs}"
  out := out.push "\\end{document}"
  return String.intercalate "\n" out.toList ++ "\n"

def main : IO Unit := do
  IO.FS.createDirAll "bench"
  let paper := gen
  IO.FS.writeFile "bench/paper.tex" paper
  IO.println s!"{paper.utf8ByteSize} bench/paper.tex"
  let mut bib := ""
  for i in [0:bibKeys.size] do
    bib := bib ++ bibEntry i
  IO.FS.writeFile "bench/refs.bib" bib
  IO.println s!"{bib.utf8ByteSize} bench/refs.bib"
