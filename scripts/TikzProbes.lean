/-
The invented probes of the picture subset, one per construct: what the
`tikz-native` tier elaborates in-process and what `tikz-diff` draws with
both engines. Data only; each consumer owns what it measures.
-/
/-- A probe's kind: a `tikzpicture` body, a `tikzcd` body standing alone
in a display, or one standing as a block outside mathematics (the tikz-cd
manual's own spelling). -/
inductive ProbeKind where
  | picture
  | cd
  | cdBlock

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
  ("cd-block", .cdBlock, "A \\arrow[r, \"f\"] & B \\\\ & C"),
  ("cd-color", .cd, "A \\arrow[r, red] & B"),
  ("cd-description", .cd, "A \\arrow[r, \"f\" description] & B"),
  ("cd-diagonal", .cd, "A \\arrow[dr] & B \\\\ & C"),
  ("cd-labels", .cd, "A \\arrow[r, \"f\"] \\arrow[d, \"g\"'] & B \\\\ C"),
  ("cd-old-syntax", .cd, "A \\arrow{r}{f} & B"),
  ("cd-sep", .cd, "[row sep=large, column sep=small] A \\arrow[r] & B"),
  ("circle-op", .picture, "\\draw (0,0) circle (1);"),
  ("circle-radius-key", .picture, "\\draw (0,0) circle [radius=3mm];"),
  ("clip", .picture, "\\clip (0,0) rectangle (1,1);\\fill (0,0) circle (1);"),
  ("clip-order", .picture,
    "\\clip (0,0) rectangle (2,2);\\node at (1,1) {a};\\fill[grid] (0,0) rectangle (2,1);"),
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
  | .cdBlock => pre ++ "\\begin{tikzcd}" ++ body ++ "\\end{tikzcd}\n\\end{document}"

