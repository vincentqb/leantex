import Tests.Support

open LeanTex.Core

/-! **Code on paper: every character reaches the page.**

A markdown document can declare no listing keys, and its code set at the
body size in a measure-wide face ran past the page edge: hundreds of lines
of a long generated report lost their ends. A markdown fence now sets as
its surface sets code (`Ir.Surface.listing`) — `\footnotesize`, wrapping —
and a wrapping listing wraps as listings.sty wraps it: greedily, at a space
or between two output units, never inside an identifier, each continuation
standing 20 pt past its own line's indentation (`breakindent`,
`breakautoindent`), so every declared line holds. A LuaLaTeX probe of
listings set exactly that: continuations 20 pt in, past the line's own
indentation; a break before a comma; an identifier wider than the measure
left whole. The invariants are over `Layout.Out` (where each line's first
glyph stands, what each line holds, that each fits) and over the IR's
listing values the two artifacts read. Every word here is invented. -/

namespace Tests.MarkdownCode

/-- The first listing a document's top-level body holds. -/
def firstListing (doc : Ir.Doc) : Option Ir.ListingSpec :=
  doc.body.findSome? fun b => match b with
    | .verbatim _ _ spec => some spec
    | _ => none

/-- Where a character first stands on a shipped line, walking every
segment's advance. -/
def glyphX (l : Layout.LineOut) (wanted : Char) : Option Dim.Sp := Id.run do
  let mut x := l.x
  for s in l.segs do
    match s with
    | .run _ _ _ w glyphs _ _ _ _ _ _ =>
      let mut pen := x
      for (_, c, advance) in glyphs do
        if c == wanted then return some pen
        pen := pen + advance
      x := x + w
    | .gap w _ | .decoratedGap w _ _ | .decoration _ w _ _ _
    | .rule w _ _ _ | .image _ w _ => x := x + w
    | .poly _ _ => pure ()
  return none

/-- Where a shipped line's first glyph other than a space stands. -/
def firstGlyphX (l : Layout.LineOut) : Option Dim.Sp := Id.run do
  let mut x := l.x
  for s in l.segs do
    match s with
    | .run _ _ _ w glyphs _ _ _ _ _ _ =>
      let mut pen := x
      for (_, c, advance) in glyphs do
        if c != '\u00a0' && c != ' ' then return some pen
        pen := pen + advance
      x := x + w
    | .gap w _ | .decoratedGap w _ _ | .decoration _ w _ _ _
    | .rule w _ _ _ | .image _ w _ => x := x + w
    | .poly _ _ => pure ()
  return none

/-- A line's text with every space and no-break space removed. -/
def bare (s : String) : String := (s.replace "\u00a0" "").replace " " ""

def markdownCodeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- The surface: one decision, read by the reader choice and the document.
  t "the surface is the path's: a .md source is markdown, any other tex"
    (Ir.Surface.ofPath "notes.md" == .markdown && Ir.Surface.ofPath "notes.tex" == .tex
      && Ir.Surface.ofPath "notes" == .tex)
  t "the elaborated document records its surface"
    ((elabMd "Words.\n").1.surface == .markdown && (elabStr (dvDoc "" "Words.")).1.surface == .tex)
  -- The listing values both artifacts read.
  let mdSpec := firstListing (elabMd "```\nplain code\n```\n").1
  let mdLang := firstListing (elabMd "```python\nx = 1\n```\n").1
  t "a markdown fence sets as its surface's code: footnotesize, wrapping as listings wraps"
    ([mdSpec, mdLang].all fun s => s.any fun s =>
      s.fontSize == .size "footnotesize" && s.breakLines
        && s.breakIndent == some Ir.listingBreakIndent)
  let texPlain := firstListing (elabStr (dvDoc "" "\\begin{verbatim}\nx\n\\end{verbatim}")).1
  let texLst := firstListing (elabStr (dvDoc "" "\\begin{lstlisting}\nx\n\\end{lstlisting}")).1
  t "a tex listing keeps LaTeX's defaults: the ambient size, no wrapping"
    ([texPlain, texLst].all fun s => s.any fun s =>
      s.fontSize == .size "normalsize" && !s.breakLines)
  let lstWrap := firstListing (elabStr (dvDoc ""
    "\\begin{lstlisting}[breaklines=true]\nx\n\\end{lstlisting}")).1
  let mintedWrap := firstListing (elabStr (dvDoc ""
    "\\begin{minted}[breaklines]{text}\nx\n\\end{minted}")).1
  t "listings wraps with its own continuation indent; minted's fvextra wrap is not that"
    (lstWrap.any (fun s => s.breakLines && s.breakIndent == some Ir.listingBreakIndent)
      && mintedWrap.any (fun s => s.breakLines && s.breakIndent.isNone))
  -- The page.
  let some text ← loadTestFont "OpenSans-Regular.ttf"
    | t "markdown code: the text face loads" false
  let some mono ← loadTestFont "SourceCodePro-Regular.otf"
    | t "markdown code: the typewriter face loads" false
  let fonts := monoSlotOf text mono
  let size := Dim.pt 8
  let cell := size * mono.spaceAdvance / mono.unitsPerEm
  let words := "alpha beta gamma delta epsilon zeta eta theta iota kappa lambda mu nu xi \
omicron pi rho sigma tau upsilon phi chi psi omega"
  let src := "```\n" ++ words ++ "\nshort line\n    indented " ++ words ++ "\n```\n"
  let doc := (elabMd src).1
  let out := layoutOf fonts doc
  let measure := doc.page.width - 2 * doc.page.hmargin
  let lines := bodyLines out
  t s!"markdown code: long lines wrap and every shipped line fits the measure ({lines.size})"
    (lines.size ≥ 5 && lines.all (·.setWidth ≤ measure))
  t "markdown code: every source character ships once, in order"
    (String.join (lines.toList.map (bare ∘ lineText)) ==
      bare (words ++ "short line" ++ "indented" ++ words))
  t "markdown code: no line re-flows and none runs past the measure"
    (!out.diags.any fun d => d.kind == .W0386 || d.kind == .W0005)
  let x0 := (lines[0]?.bind firstGlyphX)
  t "markdown code: a continuation stands 20 pt in"
    (lines[1]?.bind firstGlyphX == x0.map (· + Ir.listingBreakIndent))
  let indentedAt := lines.findIdx? fun l => hasStr (lineText l) "indented"
  t "markdown code: an indented line's continuation stands its own indentation and 20 pt in"
    (match indentedAt with
      | some k =>
        (lines[k]?.bind firstGlyphX) == x0.map (· + 4 * cell) &&
          (lines[k + 1]?.bind firstGlyphX) == x0.map (· + 4 * cell + Ir.listingBreakIndent)
      | none => false)
  -- The markdown measure holds 80 columns of this 0.6 em face at
  -- footnotesize: an 80-column line stays one line, an 81-column one wraps.
  let cols (n : Nat) : String :=
    String.ofList ((List.range n).map fun k => if k % 5 == 4 && k + 1 < n then ' ' else 'a')
  let linesOf (s : String) := bodyLines (layoutOf fonts (elabMd ("```\n" ++ s ++ "\n```\n")).1)
  t "markdown code: an 80-column line fits the markdown measure whole"
    ((linesOf (cols 79)).size == 1 && (linesOf (cols 80)).size == 1
      && (linesOf (cols 81)).size == 2)
  -- Never inside an identifier: a word wider than the measure is TeX's
  -- overfull line, whole, and a run of output units breaks between units.
  let ident := String.ofList (List.replicate 100 'q')
  let identLines := linesOf ident
  t "markdown code: an identifier wider than the measure is never split"
    (identLines.size == 1 && identLines.all fun l => bare (lineText l) == ident)
  let units := "f(" ++ String.intercalate "," ((List.range 30).map fun k => s!"arg{k}") ++ ")"
  let unitLines := linesOf units
  let joins := (unitLines.zip (unitLines.extract 1 unitLines.size)).toList.map fun (a, b) =>
    ((bare (lineText a)).back, (bare (lineText b)).front)
  t "markdown code: a run of output units wraps between units, never inside one"
    (unitLines.size ≥ 2 && String.join (unitLines.toList.map (bare ∘ lineText)) == units
      && joins.all fun (a, b) => !(a.isAlphanum && b.isAlphanum))
  -- A tex listing that declares listings' wrapping wraps as listings does,
  -- line numbers included: no re-flow named, continuations past the
  -- number column.
  let texSrc := dvDoc "" ("\\begin{minipage}{120pt}\n\\begin{lstlisting}[breaklines=true,\
numbers=left,basicstyle=\\ttfamily\\footnotesize]\n" ++ words ++ "\n\\end{lstlisting}\n\\end{minipage}")
  let texOut := layoutOf fonts (elabStr texSrc).1
  let texLines := bodyLines texOut
  t s!"tex listing: breaklines wraps inside the measure with no re-flow named ({texLines.size})"
    (texLines.size ≥ 3 && texLines.all (·.setWidth ≤ Dim.pt 120)
      && !texOut.diags.any (·.kind == .W0386))
  t "tex listing: a continuation stands past the line numbers and 20 pt in"
    (match texLines[0]?, texLines[1]? with
      | some a, some b => !(lineText b).any Char.isDigit &&
          firstGlyphX b == (glyphX a 'a').map (· + Ir.listingBreakIndent)
      | _, _ => false)

end Tests.MarkdownCode
