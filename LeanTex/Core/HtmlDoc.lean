import LeanTex.Core.Html
import LeanTex.Core.Ir
import LeanTex.Core.Dim
import LeanTex.Core.Contrast

namespace LeanTex.Core.HtmlDoc

open LeanTex.Core LeanTex.Core.Ir LeanTex.Core.Dim LeanTex.Core.Html

/-- How much CSS to emit, and whose class names to use. -/
inductive CssMode where
  /-- Our own token-driven stylesheet, inlined. Self-contained by default: no
  CDN, no webfont round-trip, works offline. -/
  | own
  /-- Bulma class names plus a `--bulma-*` binding of our tokens, for pages
  that drop into an existing Bulma site. The framework itself is not shipped;
  the host page provides it. -/
  | bulma
  /-- Semantic markup only. Bring your own stylesheet. -/
  | none
  deriving Repr, BEq

structure Config where
  css : CssMode := .own
  lang : String := "en"
  /-- Optional client-side math renderer, used until native MathML lands.
  A boundary, not a dependency: nothing is emitted unless asked for. -/
  mathBoundary : Option String := none
  styles : Styles := {}
  deriving Repr

private def hex2 (v : UInt8) : String :=
  let d := "0123456789abcdef".toList
  String.ofList [d[v.toNat / 16]!, d[v.toNat % 16]!]

def cssColor (c : Color) : String := s!"#{hex2 c.r}{hex2 c.g}{hex2 c.b}"

/-- Thousandths to a decimal, so `1.2em` round-trips as `1.2em`. It was once
emitted as `120%`, which for padding is a fraction of the container and pushed
every styled list off the page. -/
private def decMilli (n : Int) : String :=
  let sign := if n < 0 then "-" else ""
  let a := n.natAbs
  let frac := toString (a % 1000)
  let frac := "".pushn '0' (3 - frac.length) ++ frac
  let frac := String.ofList (frac.toList.reverse.dropWhile (· == '0')).reverse
  s!"{sign}{a / 1000}" ++ (if frac.isEmpty then "" else "." ++ frac)

/-- A length in CSS. `em`/`ex` survive as their CSS equivalents rather than
being resolved, so the browser scales them with the reader's font size — the
one place HTML should *not* copy what the PDF path does. -/
def cssLength (l : Length) : String :=
  let parts :=
    (if l.sp != 0 then [s!"{l.sp.toPtString}pt"] else []) ++
    (if l.em != 0 then [s!"{decMilli l.em}em"] else []) ++
    -- CSS has an `ex` unit of its own; the browser measures the real font.
    (if l.ex != 0 then [s!"{decMilli l.ex}ex"] else [])
  match parts with
  | [] => "0"
  | [one] => one
  | many => "calc(" ++ String.intercalate " + " many ++ ")"

/-- The content measure, as the page declared it: text width over the base
font size, in `em` so it scales with the browser font. `article` is PDF-first
and its HTML is a faithful degradation, so the measure comes from `\page`
rather than a fixed reading-column width. -/
def measureEm (page : PageSpec) : String :=
  let textWidth := page.width - 2 * page.hmargin
  s!"{decMilli (textWidth * 1000 / page.fontSize)}em"

/-- `\style` declarations as CSS on the element selectors. A marker becomes
`::marker` content only when it is plain text; styled markers fall back to the
default, which is the honest degradation until `::marker` styling is portable.
A base list element styles every nesting level (as the PDF path does), so its
marker rule is emitted at each depth — the depth-qualified selectors match
the level defaults' specificity and, standing later in the sheet, win. -/
def styleRules (doc : Doc) : String :=
  let sel : String → Option String
    | "section" => some "h2" | "subsection" => some "h3" | "subsubsection" => some "h4"
    | "itemize" => some "ul" | "enumerate" => some "ol"
    | "itemize2" => some "ul ul" | "itemize3" => some "ul ul ul"
    | "itemize4" => some "ul ul ul ul"
    | "enumerate2" => some "ol ol" | "enumerate3" => some "ol ol ol"
    | "enumerate4" => some "ol ol ol ol"
    | _ => none
  let markerSel : String → String
    | "ul" => "ul > li::marker, ul ul > li::marker, ul ul ul > li::marker, " ++
      "ul ul ul ul > li::marker"
    | "ol" => "ol > li::marker, ol ol > li::marker, ol ol ol > li::marker, " ++
      "ol ol ol ol > li::marker"
    | tag => s!"{tag} > li::marker"
  let plainText (xs : Array Inline) : Option String :=
    xs.foldl (fun acc x => match acc, x with
      | some a, .text t => some (a ++ t)
      | _, _ => none) (some "")
  String.join (doc.styles.entries.toList.filterMap fun (element, st) => do
    let tag ← sel element
    let decls :=
      (st.before.map fun g => s!"margin-top: {cssLength g.width};").toList ++
      (st.after.map fun g => s!"margin-bottom: {cssLength g.width};").toList ++
      (st.indent.map fun g => s!"padding-left: {cssLength g.width};").toList ++
      (st.rule.map fun (c, n) =>
        let color := match n with
          | some name => s!"var(--{name}, {cssColor c})"
          | none => cssColor c
        -- Baseline, not center: the rule is drawn where the PDF draws it,
        -- level with the heading's baseline, via the flex items' baselines.
        s!"display: flex; align-items: baseline; gap: 0.5em; --rule-color: {color};").toList
    let liDecls :=
      (st.gap.map fun g => s!"{tag} > li \{ margin-top: {cssLength g.width}; }\n").toList ++
      (st.marker.bind plainText |>.map fun m =>
        s!"{markerSel tag} \{ content: \"{m}  \"; }\n").toList
    let own := if decls.isEmpty then "" else s!"{tag} \{ {String.intercalate " " decls} }\n"
    some (own ++ String.join liDecls))

/-- Furniture the semantic palette keys turn on — one shared rule set for
every theme, so a theme stays a table of values. Each rule fires only when
its key is declared, mirroring the PDF path: `bg`/`fg` colour the page,
`frametitlebg` turns the frame title into a colour bar, `progressfg` styles
the section pages and their progress bar. -/
def themeCss (doc : Doc) : String :=
  let has (k : String) : Bool := (doc.palette.find? k).isSome
  (if has "bg" then "body { background: var(--bg); }\n" else "") ++
  (if has "fg" then "body { color: var(--fg); }\n" else "") ++
  (if has "frametitlebg" then
    "section.slide > header { background: var(--frametitlebg);\n" ++
    "  color: var(--frametitlefg, var(--bg, #fff));\n" ++
    "  margin: -1.4rem -1.8rem 0.8rem; padding: 0.7rem 1.8rem;\n" ++
    "  border-radius: 7px 7px 0 0; }\n" ++
    "section.slide > header h2 { color: inherit; }\n" else "") ++
  (if has "progressfg" then
    "section.section-page { text-align: center; padding: 2.5rem 0;\n" ++
    "  break-inside: avoid; }\n" ++
    "section.section-page h2 { display: inline-block; text-align: left;\n" ++
    "  min-width: 60%; margin: 0; }\n" ++
    ".progress { background: var(--progressbg, var(--rule)); height: 3px;\n" ++
    "  width: 60%; margin: 0.6rem auto 0; }\n" ++
    ".progress > div { background: var(--progressfg); height: 100%; }\n" else "")

/-- Design tokens become CSS custom properties, so the same declarations drive
both backends and a reader's stylesheet can override them. -/
def tokenVars (doc : Doc) : String :=
  let palette := doc.palette.entries.toList.map fun (n, c) =>
    s!"    --{n}: {cssColor c};"
  let tokens := doc.tokens.entries.toList.map fun (n, g) =>
    s!"    --{n}: {cssLength g.width};"
  let fonts :=
    (match doc.fonts.body with
     | some f => [s!"    --font-body: \"{f}\", Georgia, serif;"]
     | none => []) ++
    (match doc.fonts.sans with
     | some f => [s!"    --font-sans: \"{f}\", system-ui, sans-serif;"]
     | none => []) ++
    (match doc.fonts.mono with
     | some f => [s!"    --font-mono: \"{f}\", ui-monospace, monospace;"]
     | none => [])
  String.intercalate "\n" (palette ++ tokens ++ fonts)

/-- Size rules generated from the IR's scale, so the two backends cannot drift
apart on what `\Huge` means. `em` rather than `rem`: sizes nest. -/
private def sizeRules : String :=
  String.join (Ir.sizeScale.map fun (name, k) =>
    s!".size-{name} \{ font-size: {k / 1000}.{padLeft (k % 1000) 3}em; }\n")
where
  padLeft (n w : Nat) : String :=
    let s := toString n
    "".pushn '0' (w - min w s.length) ++ s

/-- The base stylesheet. Small on purpose: a generated document should not
ship a framework to use four of its rules. Dark mode is a variant of the same
token set, not an inversion hack. -/
def baseCss (doc : Doc) : String :=
  -- The two token sets are `Contrast.light`/`Contrast.dark`, not literals
  -- here: every pairing they create is proved legible over there
  -- (`light_contract`, `dark_contract`), and a value only a backend knows
  -- would be a value no theorem covers.
  let lt := Contrast.light
  let dk := Contrast.dark
  ":root {\n" ++
  "    color-scheme: light dark;\n" ++
  s!"    --measure: {measureEm doc.page};\n" ++
  s!"    --ink: {cssColor lt.ink};\n" ++
  s!"    --surface: {cssColor lt.surface};\n" ++
  s!"    --muted: {cssColor lt.muted};\n" ++
  s!"    --accent: {cssColor lt.accent};\n" ++
  s!"    --tint: {cssColor lt.tint};\n" ++
  s!"    --rule: {cssColor lt.rule};\n" ++
  "    --font-body: Georgia, \"Times New Roman\", serif;\n" ++
  "    --font-sans: system-ui, -apple-system, \"Segoe UI\", sans-serif;\n" ++
  "    --font-mono: ui-monospace, SFMono-Regular, Menlo, monospace;\n" ++
  tokenVars doc ++ "\n" ++
  "}\n" ++
  "@media (prefers-color-scheme: dark) {\n" ++
  "  :root {\n" ++
  s!"    --ink: {cssColor dk.ink};\n" ++
  s!"    --surface: {cssColor dk.surface};\n" ++
  s!"    --muted: {cssColor dk.muted};\n" ++
  -- The light accent read at 2.64:1 on the dark surface -- under the 3:1
  -- a focus indicator needs (WCAG 2.2 SC 1.4.11) -- so dark carries its
  -- own accent; inverting ink and surface never fixed a hue chosen
  -- against a light page.
  s!"    --accent: {cssColor dk.accent};\n" ++
  s!"    --tint: {cssColor dk.tint};\n" ++
  s!"    --rule: {cssColor dk.rule};\n" ++
  "  }\n" ++
  "}\n" ++
  "*, *::before, *::after { box-sizing: border-box; }\n" ++
  "body {\n" ++
  "  margin: 0;\n" ++
  "  padding: 2.5rem 1.25rem 4rem;\n" ++
  "  background: var(--surface);\n" ++
  "  color: var(--ink);\n" ++
  "  font-family: var(--font-body);\n" ++
  "  font-size: 1.0625rem;\n" ++
  "  line-height: 1.55;\n" ++
  "  text-rendering: optimizeLegibility;\n" ++
  "  -webkit-font-smoothing: antialiased;\n" ++
  "}\n" ++
  "main { max-width: var(--measure); margin: 0 auto; }\n" ++
  "h1, h2, h3, h4 {\n" ++
  "  font-family: var(--font-sans);\n" ++
  "  font-weight: 600;\n" ++
  "  line-height: 1.2;\n" ++
  "  margin: 2.25rem 0 0.6rem;\n" ++
  "  text-wrap: balance;\n" ++
  "}\n" ++
  "h1 { font-size: 1.9rem; margin-top: 0; }\n" ++
  "h2 { font-size: 1.45rem; }\n" ++
  "h3 { font-size: 1.2rem; }\n" ++
  "p { margin: 0 0 1rem; }\n" ++
  "ul, ol { margin: 0 0 1rem; padding-left: 1.35rem; }\n" ++
  "li { margin: 0.25rem 0; }\n" ++
  "li::marker { color: var(--muted); }\n" ++
  -- The class-default list marking, per nesting level, matching the PDF
  -- backend (classes.dtx: bullet, bold en-dash, centered asterisk, centered
  -- dot; arabic., (alph), roman., Alph.). Descendant selectors count depth
  -- per list kind, as LaTeX's \@itemdepth/\@enumdepth do. `disc` and
  -- `decimal` are the browsers' own level-1 defaults, stated for symmetry.
  "ul { list-style-type: disc; }\n" ++
  "ul ul > li::marker { content: \"\u2013  \"; font-weight: 600; }\n" ++
  "ul ul ul > li::marker { content: \"\u2217  \"; }\n" ++
  "ul ul ul ul > li::marker { content: \"\u00b7  \"; }\n" ++
  "ol { list-style-type: decimal; }\n" ++
  "ol ol { list-style-type: lower-alpha; }\n" ++
  "ol ol > li::marker { content: \"(\" counter(list-item, lower-alpha) \")  \"; }\n" ++
  "ol ol ol { list-style-type: lower-roman; }\n" ++
  "ol ol ol > li::marker { content: counter(list-item, lower-roman) \".  \"; }\n" ++
  "ol ol ol ol { list-style-type: upper-alpha; }\n" ++
  "ol ol ol ol > li::marker { content: counter(list-item, upper-alpha) \".  \"; }\n" ++
  -- A link inherits the document's colour, as it does in the PDF: the anchor
  -- imposes nothing, the underline and focus outline carry the affordance.
  "a { color: inherit; text-decoration-thickness: 1px;\n" ++
  "    text-decoration-skip-ink: auto; text-underline-offset: 0.15em; }\n" ++
  "u { text-decoration: underline; text-decoration-skip-ink: auto;\n" ++
  "    text-underline-offset: 0.15em; }\n" ++
  "a:focus-visible { outline: 2px solid var(--accent); outline-offset: 2px; }\n" ++
  "code, pre { font-family: var(--font-mono); font-size: 0.925em; }\n" ++
  "pre { background: var(--tint); padding: 0.9rem 1rem; overflow-x: auto;\n" ++
  "      border-radius: 4px; }\n" ++
  ".centered { text-align: center; }\n" ++
  ".fill { flex: 1 1 auto; }\n" ++
  ".spaced { margin-top: var(--sep, 1.4rem); }\n" ++
  -- General rows keep the prior flex behavior. An exact pair switches to a
  -- grid that reserves the right max-content column before the left wraps.
  ".entry, .entry-row { display: flex; flex-wrap: wrap; column-gap: 0.4rem;\n" ++
  "  align-items: baseline; }\n" ++
  ".entry > .group + .group, .entry-row > .group + .group { margin-left: auto; }\n" ++
  ".entry > .group:last-child, .entry-row > .group:last-child { text-align: right; }\n" ++
  ".entry-pair { display: grid;\n" ++
  "  grid-template-columns: minmax(0, 1fr) max-content; }\n" ++
  ".entry-rows { display: flex; flex-direction: column; }\n" ++
  ".sans { font-family: var(--font-sans); }\n" ++
  ".ruled::after { content: \"\"; flex: 1; border-top: 1px solid var(--rule-color); }\n" ++
  -- The browser uses the face's own small caps when it has them and synthesises
  -- otherwise, which is the better of the two mechanisms; the PDF path can only
  -- synthesise.
  ".sc { font-variant-caps: small-caps; }\n" ++
  -- Slides, as the linear handout: one bordered section per frame, printing
  -- one per page. The interactive controller is the rest of M5.
  "section.slide { border: 1px solid var(--rule); border-radius: 8px;\n" ++
  "  padding: 1.4rem 1.8rem; margin: 1.4rem 0; break-inside: avoid; }\n" ++
  "section.slide > header h2 { margin: 0 0 0.8rem; font-size: 1.35rem; }\n" ++
  -- A standout frame inverts: the palette's standout keys override, and
  -- without them the page's own fg/bg swap — the same rule as the PDF path.
  "section.slide.standout { background: var(--standoutbg, var(--fg, #18181b));\n" ++
  "  color: var(--standoutfg, var(--bg, #fafaf9)); text-align: center;\n" ++
  "  font-size: 1.44em; font-weight: 600;\n" ++
  "  display: flex; flex-direction: column; justify-content: center; }\n" ++
  sizeRules ++
  ".math { font-family: \"Latin Modern Math\", \"STIX Two Math\", math; }\n" ++
  "@media print {\n" ++
  "  body { background: #fff; color: #000; padding: 0; }\n" ++
  "}\n" ++
  "@media (prefers-reduced-motion: reduce) {\n" ++
  "  * { animation: none !important; transition: none !important; }\n" ++
  "}\n" ++
  "@media (max-width: 30rem) {\n" ++
  "  .entry-pair { grid-template-columns: minmax(0, 1fr); }\n" ++
  "}"

private def styleClass : Style → String
  | .bold => "b"
  | .italic => "i"
  | .mono => "mono"
  | .smallcaps => "sc"
  | .emph => "em"
  | .sans => "sans"
  | .normal => "normal"
  | .size n => "size-" ++ n

mutual

/-- Inline content, pushed onto `acc`. Style maps onto the element that
carries the *meaning* where one exists (`<strong>`, `<em>`, `<code>`) and
onto a class otherwise. The accumulator threads through the sibling walk:
`inlineNode x ++ rest` copied the tail at every element. -/
private def inlineNodeInto (cfg : Config) (acc : Array Node) (x : Inline) : Array Node :=
  match x with
  | .text s => acc.push (Html.text s)
  | .math display src =>
    -- Until native MathML lands the source rides in a data attribute, so an
    -- optional client-side renderer can find it and nothing is faked.
    let tag := if display then "div" else "span"
    acc.push (Html.elem tag #[Html.text src]
      #[("class", if display then "math math-display" else "math"),
        ("data-tex", src)])
  | .styled st body =>
    let kids := inlineNodesInto cfg #[] body.toList
    match st with
    | .bold => acc.push (Html.elem "strong" kids)
    | .italic => acc.push (Html.elem "em" kids)
    | .emph => acc.push (Html.elem "em" kids)
    | .mono => acc.push (Html.elem "code" kids)
    | .normal => acc ++ kids
    | other => acc.push (Html.elem "span" kids #[("class", styleClass other)])
  | .colored c name body =>
    -- A named colour becomes a custom-property reference with the literal as
    -- fallback, so the token really is the styling API: a host page can
    -- restyle the document by redefining --primary.
    let value := match name with
      | some n => s!"color: var(--{n}, {cssColor c})"
      | none => s!"color: {cssColor c}"
    acc.push (Html.elem "span" (inlineNodesInto cfg #[] body.toList) #[("style", value)])
  | .link url body =>
    acc.push (Html.elem "a" (inlineNodesInto cfg #[] body.toList)
      #[("href", url), ("style", "color: inherit")])
  | .underline body =>
    -- skip-ink is the browser's native form of the PDF path's invariant: the
    -- rule breaks where a descender crosses it.
    acc.push (Html.elem "u" (inlineNodesInto cfg #[] body.toList))
  | .step n last body =>
    -- Every step is visible: the no-JS deck is a readable handout (PLAN M5).
    -- The range rides as data for the coming deck controller.
    acc.push (Html.elem "span" (inlineNodesInto cfg #[] body.toList)
      (#[("class", "step"), ("data-step", toString n)] ++
        (match last with
         | some u => #[("data-step-last", toString u)]
         | none => #[])))
  | .fill => acc.push (Html.elem "span" #[] #[("class", "fill")])
  -- Page furniture has no meaning in a continuous document.
  | .pageNumber => acc
  | .pageCount => acc
  | .linebreak extra =>
    -- Extra space after a break is vertical, so it is a sized block rather
    -- than a second <br>: a doubled <br> would depend on line-height.
    if extra == ({} : SymGlue) then acc.push (Html.elem "br" #[])
    else (acc.push (Html.elem "br" #[])).push
      (Html.elem "span" #[]
        #[("style", s!"display:block;height:{cssLength extra.width}")])

/-- The list companion keeps the recursion structural; a `flatMap` over the
children would hide the call behind a lambda. -/
private def inlineNodesInto (cfg : Config) (acc : Array Node) : List Inline → Array Node
  | [] => acc
  | x :: rest => inlineNodesInto cfg (inlineNodeInto cfg acc x) rest

end

private def inlines (cfg : Config) (xs : Array Inline) : Array Node :=
  inlineNodesInto cfg #[] xs.toList

/-- Does this paragraph use `\hfill`? If so it becomes a flex row, which is
the CSS equivalent of the stretch it asked for. -/
private def hasFill (xs : Array Inline) : Bool :=
  xs.any fun x => match x with
    | .fill => true
    | _ => false

/-- Split inline content at each `\\`. A stretched row is a column of rows, one
per break, because `\hfill` stretches within a line: a `<br>` cannot end a flex
line, so the break has to be structural. -/
private def splitAtBreaks (xs : Array Inline) : Array (Array Inline) := Id.run do
  let mut out : Array (Array Inline) := #[]
  let mut cur : Array Inline := #[]
  for x in xs do
    match x with
    | .linebreak _ =>
      out := out.push cur
      cur := #[]
    | other => cur := cur.push other
  return out.push cur

/-- Split one row at each `\hfill`. The exact two-group case gets a dedicated
column contract; rows with more groups keep the general flex semantics. -/
private def splitAtFills (xs : Array Inline) : Array (Array Inline) := Id.run do
  let mut out : Array (Array Inline) := #[]
  let mut cur : Array Inline := #[]
  for x in xs do
    match x with
    | .fill =>
      out := out.push cur
      cur := #[]
    | other => cur := cur.push other
  return out.push cur

private def fillRow (cfg : Config) (tag baseClass : String) (xs : Array Inline) : Node :=
  let groups := splitAtFills xs
  let rowClass := if groups.size == 2 then baseClass ++ " entry-pair" else baseClass
  Html.elem tag (groups.map fun group =>
    Html.elem "span" (inlines cfg group) #[("class", "group")])
    #[("class", rowClass)]

/-- Grid tracks from the declared widths: a per-mille width is a percentage
track, a widthless column an `fr` share of the leftover. With every width
declared the leftover spreads between the tracks, which is the PDF path's
gutter rule. -/
private def gridTracks (cols : Array (Option Nat × Array Block)) : String :=
  String.intercalate " " (cols.toList.map fun (w, _) =>
    match w with
    | some f =>
      if f % 10 == 0 then s!"{f / 10}%" else s!"{f / 10}.{f % 10}%"
    | none => "1fr")

mutual

def blockNode (cfg : Config) (b : Block) : Node :=
  match b with
  | .para content =>
    if hasFill content then
      let rows := splitAtBreaks content
      if rows.size == 1 then
        fillRow cfg "p" "entry" content
      else
        Html.elem "p" (rows.map fun row => fillRow cfg "span" "entry-row" row)
          #[("class", "entry-rows")]
    else
      Html.elem "p" (inlines cfg content)
  | .section level _ title =>
    let (tag, element) := match level with
      | 1 => ("h2", "section")
      | 2 => ("h3", "subsection")
      | _ => ("h4", "subsubsection")
    let st := (cfg.styles.find? element).getD {}
    let title := match st.font with
      | some tpl => fillTemplate tpl title
      | none => title
    Html.elem tag (inlines cfg title) (if st.rule.isSome then #[("class", "ruled")] else #[])
  | .list ordered items =>
    let tag := if ordered then "ol" else "ul"
    Html.elem tag (listItemsInto cfg #[] items.toList)
  | .center body =>
    Html.elem "div" (blockNodesInto cfg #[] body.toList) #[("class", "centered")]
  | .columns cols =>
    -- Side-by-side columns as a grid: the declared fractions become
    -- percentage tracks, so the HTML column really is as wide as the PDF's.
    Html.elem "div" (columnNodesInto cfg #[] cols.toList)
      #[("class", "columns"),
        ("style", s!"display: grid; grid-template-columns: {gridTracks cols}; " ++
          "justify-content: space-between; column-gap: 0.75rem")]
  | .step n last body =>
    -- Every step visible (the no-JS handout); the range rides as data.
    Html.elem "div" (blockNodesInto cfg #[] body.toList)
      (#[("class", "step"), ("data-step", toString n)] ++
        (match last with
         | some u => #[("data-step-last", toString u)]
         | none => #[]))
  | .note body =>
    -- Inert and hidden: available to a speaker view, invisible in the deck
    -- and in print.
    Html.elem "aside" (blockNodesInto cfg #[] body.toList)
      #[("class", "note"), ("hidden", "hidden")]
  | .spaced before body =>
    let style := s!"margin-top: {cssLength before.width}"
    Html.elem "div" (blockNodesInto cfg #[] body.toList)
      #[("class", "spaced"), ("style", style)]
  | .verbatim s =>
    -- `<pre>` preserves the raw lines; the escaper makes the content inert.
    Html.elem "pre" #[Html.elem "code"
      #[Html.text (String.intercalate "\n" (verbatimLines s).toList)]]
  | .frame title standout body =>
    -- One slide of the deck. With no controller yet this is the no-JS
    -- rendering the plan promises anyway: a linear readable handout, every
    -- slide a section.
    let header := if title.isEmpty then #[]
      else #[Html.elem "header" #[Html.elem "h2" (inlines cfg title)]]
    let cls := if standout then "slide standout" else "slide"
    Html.elem "section" (header ++ blockNodesInto cfg #[] body.toList) #[("class", cls)]

/-- The accumulator threads through the sibling walk, as in `inlineNodesInto`. -/
private def blockNodesInto (cfg : Config) (acc : Array Node) : List Block → Array Node
  | [] => acc
  | b :: rest => blockNodesInto cfg (acc.push (blockNode cfg b)) rest

private def columnNodesInto (cfg : Config) (acc : Array Node) :
    List (Option Nat × Array Block) → Array Node
  | [] => acc
  | (_, body) :: rest =>
    columnNodesInto cfg
      (acc.push (Html.elem "div" (blockNodesInto cfg #[] body.toList)
        #[("class", "column")])) rest

private def listItemsInto (cfg : Config) (acc : Array Node) : List (Array Block) → Array Node
  | [] => acc
  | item :: rest =>
    listItemsInto cfg (acc.push (Html.elem "li" (listItem cfg item.toList))) rest

-- A one-paragraph item carries its content directly: wrapping it in <p> is
-- what makes generated lists render with extra vertical space.
def listItem (cfg : Config) : List Block → Array Node
  | [.para content] => inlines cfg content
  | [] => #[]
  | b :: rest => blockNodesInto cfg #[blockNode cfg b] rest

end

/-- Emit a document. Returns the file and any diagnostics the backend itself
raises — running content is the notable one: page furniture cannot be honoured
in a continuous document, and dropping it silently would be the kind of quiet
failure this engine exists to avoid. -/
def emit (cfg : Config) (doc : Doc) : String × Array Diag := Id.run do
  let mut diags : Array Diag := #[]
  if doc.head.isSome || doc.foot.isSome then
    diags := diags.push {
      severity := .warning
      code := "W0007"
      message := "running head/foot is paged-media furniture; omitted from HTML"
      help := some "put a masthead in the document body if it should appear in both"
    }
  let title := doc.info.title.getD "Untitled"
  let mut head : Array Node := #[
    Html.elem "meta" #[] #[("charset", "utf-8")],
    Html.elem "meta" #[] #[("name", "viewport"),
      ("content", "width=device-width, initial-scale=1")],
    Html.elem "title" #[Html.text title]
  ]
  for (name, value) in [("author", doc.info.author), ("description", doc.info.subject),
      ("keywords", doc.info.keywords)] do
    if let some v := value then
      head := head.push (Html.elem "meta" #[] #[("name", name), ("content", v)])
  head := head.push (Html.elem "meta" #[] #[("name", "generator"), ("content", "leantex")])
  -- Element styles are the document's own design and ride along in every
  -- mode: they are declarations, not a framework.
  let styled := styleRules doc
  match cfg.css with
  | .own => head := head.push (Node.style (baseCss doc ++ "\n" ++ themeCss doc ++ styled))
  | .bulma =>
    -- Bind our tokens onto Bulma's own custom properties so a host page's
    -- theme and ours agree instead of fighting.
    head := head.push (Node.style (":root {\n" ++ tokenVars doc ++ "\n" ++
      "    --bulma-primary: var(--primary, var(--accent, #1d4ed8));\n" ++
      "    --bulma-body-family: var(--font-body, inherit);\n" ++
      "}\n" ++ styled))
  | .none => unless styled.isEmpty do head := head.push (Node.style styled)
  let bodyClass := match cfg.css with
    | .bulma => "content"
    | _ => ""
  let cfg := { cfg with styles := doc.styles }
  -- The themed section page: in a slides document with progress keys, a
  -- top-level section becomes its own deck section carrying the position.
  let themedSections := doc.docClass == "slides" &&
    (doc.palette.find? "progressfg").isSome
  let inner := if !themedSections then blockNodesInto cfg #[] doc.body.toList
    else Id.run do
      let total := doc.body.foldl (fun n b => match b with
        | .frame _ _ _ => n + 1 | _ => n) 0
      let mut seen := 0
      let mut acc : Array Node := #[]
      for b in doc.body do
        match b with
        | .frame _ _ _ =>
          seen := seen + 1
          acc := acc.push (blockNode cfg b)
        | .section 1 _ title =>
          let pct := (min seen total) * 100 / max total 1
          acc := acc.push (Html.elem "section" #[
            Html.elem "h2" (inlines cfg title),
            Html.elem "div" #[Html.elem "div" #[] #[("style", s!"width: {pct}%")]]
              #[("class", "progress")]]
            #[("class", "section-page")])
        | _ => acc := acc.push (blockNode cfg b)
      return acc
  let main := Html.elem "main" inner (if bodyClass.isEmpty then #[]
    else #[("class", bodyClass)])
  let mut body : Array Node := #[main]
  if let some tool := cfg.mathBoundary then
    body := body.push (Html.elem "script" #[]
      #[("data-math-boundary", tool), ("src", tool)])
  return (Html.document cfg.lang head body, diags)

end LeanTex.Core.HtmlDoc
