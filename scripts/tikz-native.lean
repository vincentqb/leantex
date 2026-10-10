/-
How much of TikZ the engine draws itself, committed as numbers. Run from
the repository root after `lake build TestsModules`:

  lake env lean --run scripts/tikz-native.lean              regenerate the baseline
  lake env lean --run scripts/tikz-native.lean --check      gate against the committed one
  lake env lean --run scripts/tikz-native.lean --selftest   break each verdict once

One item per construct: an invented probe exercising it, elaborated
in-process under the declared refusal (`\pictures{ tool = none }`), so what
the subset draws is all that ships. The value is the probe's verdict:

  2  drawn natively with no loss named;
  1  drawn natively with a named loss (W0334, E0333, W0012);
  0  refused: no engine picture ships, or only the placeholder (W0362).

The spec's 2 also asks that the drawing be structurally equal to its
lualatex reference as the PDF figure reader reads it. That reader has not
landed, so the structural half is not measured yet: when it lands, a probe
whose drawing differs falls from 2, and the fall is the finding. Positions
against lualatex are `scripts/tikz-diff.lean`'s report, never this gate.

Hermetic: the probes are in this file, the faces are the suite's, and no
tool runs.
-/
import Tests.Support
import scripts.Board

open LeanTex.Core Scoreboard

/-- A probe's kind: a `tikzpicture` body, or a `tikzcd` body standing alone
in a display. -/
inductive ProbeKind where
  | picture
  | cd

/-- The constructs, each with its invented probe. -/
def probes : Array (String × ProbeKind × String) := #[
  ("alert-group", .picture, "\\alert{\\draw (0,0) -- (1,0);}"),
  ("anchor-key", .picture, "\\node[anchor=north east] at (0,0) {a};\\draw (0,0) -- (1,0);"),
  ("arc", .picture, "\\draw (0,0) arc (0:90:1);"),
  ("brace", .picture,
    "\\draw[decorate, decoration={brace, amplitude=4pt}] (0,0) -- (2,0);"),
  ("calc-factor", .picture, "\\draw ($2*(1,0)$) -- ($(0,1)+0.5*(2,2)$);"),
  ("calc-partway", .picture, "\\draw ($(0,0)!0.5!(2,2)$) -- ($(0,0)!1cm!(3,0)$);"),
  ("calc-sum", .picture, "\\coordinate (a) at (1,1);\\draw ($(a)+(1,0)$) -- ($(a)-(1,1)$);"),
  ("cd-ampersand", .cd, "[ampersand replacement=\\&] A \\arrow[r] \\& B"),
  ("cd-arrow", .cd, "A \\arrow[r] & B"),
  ("cd-bend", .cd, "A \\arrow[r, bend left] & B"),
  ("cd-color", .cd, "A \\arrow[r, red] & B"),
  ("cd-description", .cd, "A \\arrow[r, \"f\" description] & B"),
  ("cd-diagonal", .cd, "A \\arrow[dr] & B \\\\ & C"),
  ("cd-labels", .cd, "A \\arrow[r, \"f\"] \\arrow[d, \"g\"'] & B \\\\ C"),
  ("cd-old-syntax", .cd, "A \\arrow{r}{f} & B"),
  ("cd-sep", .cd, "[row sep=large, column sep=small] A \\arrow[r] & B"),
  ("circle-op", .picture, "\\draw (0,0) circle (1);"),
  ("circle-radius-key", .picture, "\\draw (0,0) circle [radius=3mm];"),
  ("clip", .picture, "\\clip (0,0) rectangle (1,1);\\fill (0,0) circle (1);"),
  ("color-decl", .picture, "{\\color{grid}\\draw (0,0) -- (1,0);}\\draw (0,1) -- (1,1);"),
  ("color-group", .picture, "\\textcolor{grid}{\\draw (0,0) -- (1,0);}"),
  ("coordinate", .picture, "\\coordinate (c) at (1,1);\\draw (0,0) -- (c);"),
  ("diamond-shape", .picture, "\\node[diamond, draw] at (0,0) {a};"),
  ("double-tip", .picture, "\\draw[<->] (0,0) -- (2,0);"),
  ("draw-none", .picture, "\\draw[draw=none] (0,0) -- (1,0);\\node[draw=none] at (0,0) {a};"),
  ("draw-opacity", .picture, "\\draw[draw opacity=0.5] (0,0) -- (1,0);"),
  ("edge-from-parent", .picture,
    "\\node {r} child {node {a} edge from parent[draw=none]} child {node {b}};"),
  ("ellipse-op", .picture, "\\draw (0,0) ellipse (1 and 0.5);"),
  ("ellipse-shape", .picture, "\\node[ellipse, draw] at (0,0) {a};"),
  ("fill-opacity", .picture, "\\fill[fill opacity=0.5] (0,0) rectangle (1,1);"),
  ("fill-path", .picture, "\\fill (0,0) -- (1,0) -- (0,1) -- cycle;"),
  ("filldraw", .picture, "\\filldraw[fill=grid] (0,0) circle (1);"),
  ("fit", .picture,
    "\\node (a) at (0,0) {a};\\node (b) at (2,1) {b};\\node[draw, fit=(a) (b)] {};"),
  ("font-key", .picture, "\\node[font=\\small] at (0,0) {a};"),
  ("label-key", .picture, "\\node[label=above:a] at (0,0) {b};"),
  ("latex-tip", .picture, "\\draw[-Latex] (0,0) -- (1,0);"),
  ("length-coords", .picture, "\\draw (0.5cm,10mm) -- (2,1);"),
  ("length-macro", .picture, "\\pgfmathsetlengthmacro{\\h}{0.5cm}\\draw (0,0) -- (\\h,\\h);"),
  ("opacity", .picture, "\\draw[opacity=0.5] (0,0) -- (1,0);"),
  ("pin-key", .picture, "\\node[pin=above:a] at (0,0) {b};"),
  ("placement-key", .picture, "\\node[above] at (0,0) {a};\\node[below left=2pt] at (0,0) {b};"),
  ("reversed-tip", .picture, "\\draw[<-] (0,0) -- (2,0);"),
  ("rounded-corners", .picture, "\\draw[rounded corners] (0,0) rectangle (2,1);"),
  ("scope-rotate", .picture, "\\begin{scope}[rotate=30]\\draw (0,0) -- (1,0);\\end{scope}"),
  ("scope-scale", .picture, "\\begin{scope}[scale=2]\\draw (0,0) -- (1,0);\\end{scope}"),
  ("scope-shift", .picture,
    "\\begin{scope}[shift={(1,0)}, xshift=1cm, yshift=2mm]\\draw (0,0) -- (1,0);\\end{scope}"),
  ("shade-axial", .picture, "\\shade[left color=grid, right color=white] (0,0) rectangle (2,1);"),
  ("shade-ball", .picture, "\\shade[ball color=grid] (0,0) circle (1);"),
  ("shade-radial", .picture,
    "\\shade[inner color=white, outer color=grid] (0,0) circle (1);"),
  ("shorten", .picture, "\\draw[->, shorten >=2pt, shorten <=1pt] (0,0) -- (2,0);"),
  ("size-decl", .picture, "{\\small\\node at (0,0) {a};}\\node at (1,0) {b};"),
  ("stealth-tip", .picture, "\\draw[-Stealth] (0,0) -- (1,0);"),
  ("tree", .picture, "\\node {r} child {node {a}} child {node {b}};"),
  ("tree-grow", .picture, "\\node {r} [grow=up] child {node {a}} child {node {b}};"),
  ("tree-level-style", .picture,
    "[level 1/.style={sibling distance=30mm}]\\node {r} child {node {a}} child {node {b}};"),
  ("tree-sibling", .picture,
    "\\node {r} [sibling distance=20mm, level distance=10mm] child {node {a}} child {node {b}};")]

/-- The document a probe elaborates as. -/
def probeDoc (kind : ProbeKind) (body : String) : String :=
  let pre := "\\documentclass{article}\n\\pictures{ tool = none }\n\\usepackage{tikz-cd}\n" ++
    "\\palette{ grid = #2A6F4E }\n\\begin{document}\n"
  match kind with
  | .picture => pre ++ "\\begin{tikzpicture}\n" ++ body ++ "\n\\end{tikzpicture}\n\\end{document}"
  | .cd => pre ++ "\\[\\begin{tikzcd}" ++ body ++ "\\end{tikzcd}\\]\n\\end{document}"

/-- A probe's verdict (the file header's 0/1/2). -/
def verdict (doc : Ir.Doc) (ds : Array Diag) : Int :=
  let drawn := Elab.enginePictures doc.body > 0 && !(ds.any (·.code == "W0362"))
  let lost := ds.any fun d => d.code == "W0334" || d.code == "E0333" || d.code == "W0012"
  if !drawn then 0 else if lost then 1 else 2

def measureTier : IO (Array String × Array Row) := do
  let rows := probes.map fun (item, kind, body) =>
    let (doc, ds) := elabStr (probeDoc kind body)
    ({ item, value := verdict doc ds } : Row)
  let count (v : Int) := (rows.filter (·.value == v)).size
  return (#[s!"# source: {probes.size} invented probes, elaborated in-process under tool = none; \
2 native and lossless {count 2}, 1 native with named losses {count 1}, 0 refused {count 0}; \
the structural half waits on the PDF figure reader"], rows)

def selftest : IO UInt32 := tierSelftest "tikz-native" fun no => do
  let (drawn, _) := elabStr (probeDoc .picture "\\draw (0,0) -- (1,0);")
  let (none', _) := elabStr (probeDoc .picture "")
  let named (c : DiagCode) : Diag := Diag.of c "a probe's loss" none
  no "verdict: an engine picture with no loss named is 2" (verdict drawn #[] == 2)
  no "verdict: a construct outside the subset makes it 1" (verdict drawn #[named .W0334] == 1)
  no "verdict: a document error makes it 1" (verdict drawn #[named .E0333] == 1)
  no "verdict: a formula floor makes it 1" (verdict drawn #[named .W0012] == 1)
  no "verdict: the placeholder is 0" (verdict drawn #[named .W0362] == 0)
  no "verdict: no engine picture is 0" (verdict none' #[] == 0)
  no "verdict: a note is no loss" (verdict drawn #[named .N0376] == 2)
  no "probes: items are unique" ((probes.map (·.1)).toList.eraseDups.length == probes.size)
  no "probes: items are tier item names"
    (probes.all fun (i, _, _) => !i.isEmpty && i.all fun c => c.isLower || c.isDigit || c == '-')

def main (args : List String) : IO UInt32 :=
  tierMain "tikz-native" .raw measureTier selftest args
