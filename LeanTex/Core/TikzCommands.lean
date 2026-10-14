module

/-! The control words TikZ gives a meaning of its own inside every picture. -/

namespace LeanTex.Core.TikzCommands

/-- The commands TikZ installs at the start of every picture (`\tikz@installcommands`), where no
definition the document made outside the picture reaches them. -/
public def installed : List String :=
  ["scope", "scoped", "endscope", "startscope", "stopscope", "path", "againpath", "draw",
   "pattern", "fill", "filldraw", "shade", "shadedraw", "clip", "graph", "useasboundingbox",
   "node", "pic", "coordinate", "matrix", "calendar", "datavisualization"]

/-- The commands pgf defines when it loads that a picture walk reads, which a document's
`\providecommand` leaves as they are. -/
public def pgfDefined : List String :=
  ["foreach", "pgfmathsetmacro", "pgfmathtruncatemacro", "pgfmathsetlengthmacro"]

/-- The control words a picture walk keeps from the document's definitions besides the
conditionals: TikZ's installed commands, and TeX's `\else` and `\fi`, which close the conditionals
it reads. -/
public def walkOwned : List String := installed ++ ["else", "fi"]

end LeanTex.Core.TikzCommands
