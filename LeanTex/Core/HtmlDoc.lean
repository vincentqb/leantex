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
  /-- The document's loaded images, from the driver: `<img>` carries the
  intrinsic pixel size so the page never reflows while loading. -/
  imgs : Image.Store := {}
  /-- The markdown twin's name, from the driver when it writes one beside
  the page: the head then links it as the alternate representation
  (`rel=alternate`, HTML §4.6.6.1; `text/markdown`, RFC 7763) — the
  llms.txt convention's discoverable form. -/
  mdHref : Option String := none

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

/-- The reduced-motion guard for one selector: under the reader's reduce
preference the transition is removed. `prefers-reduced-motion: reduce` is
the user's request that the system "minimize the amount of non-essential
motion" (CSS Media Queries 5 §12.1). -/
def reducedMotionGuard (sel : String) : String :=
  s!"@media (prefers-reduced-motion: reduce) \{ {sel} \{ transition: none; } }\n"

/-- A declared motion's CSS: the transition and, unconditionally, its own
reduced-motion guard. WCAG 2.2 SC 2.3.3 (Animation from Interactions)
requires motion animation triggered by interaction to be disableable, and
sufficient technique C39 is exactly this media query. The base stylesheet's
global guard already covers a `css = own` page, but a `css = none` page
ships only the declared rules, so the guard must travel with the
declaration itself. This is the engine's only site that spells
`transition:` into a document's styles (`motionSiteChecks` in Tests holds
the tree to that), and `motionCss_guarded` is the by-construction form. -/
def motionCss (sel : String) (ms : Nat) : String :=
  s!"{sel} \{ transition: color {ms}ms, outline-color {ms}ms; }\n" ++
    reducedMotionGuard sel

/-- A declared motion carries its reduced-motion form by construction: the
emitted CSS is definitionally a transition rule followed by the guard for
the same selector, so no call to the one transition-emitting site can
produce an unguarded transition (WCAG 2.2 SC 2.3.3; the guard's query is
CSS Media Queries 5 §12.1). -/
theorem motionCss_guarded (sel : String) (ms : Nat) :
    ∃ rule, motionCss sel ms = rule ++ reducedMotionGuard sel :=
  ⟨_, rfl⟩

/-- The declared reveal's CSS, shipped only when the emitted tree carries a
`reveal-scroll` element. Where the platform has scroll-driven animations
(CSS scroll-driven animations, `animation-timeline: scroll()`), the reveal
is declarative: the element fades in over the first `--reveal-range` of
scroll, whose default is one viewport, so the element appears as the first
screenful scrolls away. Where it does not, the element is simply visible.

That degradation is the whole design, and it is why no script is emitted
here. A compatibility shim is the stylesheet framework's job, not the
document engine's: the engine states what the page *means* and lets the
declarative platform — or the framework a document chooses — decide how
widely it works. Emitting script to paper over one engine's release
schedule buys a fade and costs a permanent escaping obligation, a payload
to audit, and a rule ("the backends emit no script") that would then hold
only approximately. A control that is always visible is not broken; it is
the honest floor. -/
def revealCss : String :=
  "@keyframes ltx-reveal { from { opacity: 0; visibility: hidden } \
to { opacity: 1; visibility: visible } }\n" ++
  "@supports (animation-timeline: scroll()) { .reveal-scroll { \
animation: ltx-reveal linear both; animation-timeline: scroll(); \
animation-range: 0 var(--reveal-range, 100vh); } }\n"


/-- A declared marker resolved to what a `::marker` rule can say: the text
it shows, and the CSS declarations its wrappers translate to. CSS
Pseudo-Elements 4 §4.1 lists the properties that apply to `::marker`: all
font properties, `color`, `content`, `white-space`, `unicode-bidi`,
`direction`, `text-combine-upright` — so a colour and a size step are
expressible, and what is not is arbitrary inline content (a link, an image,
math, a step), plus drawn decoration (`text-decoration` is not in the list,
so an underlined marker does not qualify). -/
structure MarkerCss where
  text : String
  decls : Array String := #[]
  deriving Repr, BEq

/-- What one style wrapper says in a `::marker` rule, when it says anything
(CSS Pseudo-Elements 4 §4.1: all font properties apply). The bold weight is
600, the same weight the base stylesheet's level-2 dash carries. An unknown
size name resolves to nothing, which makes the whole marker inexpressible
rather than silently unsized. -/
private def markerStyleDecls : Style → Option (Array String)
  | .bold => some #["font-weight: 600;"]
  | .italic => some #["font-style: italic;"]
  | .emph => some #["font-style: italic;"]
  | .mono => some #["font-family: var(--font-mono);"]
  | .sans => some #["font-family: var(--font-sans);"]
  | .smallcaps => some #["font-variant-caps: small-caps;"]
  | .normal => some #[]
  | .size name => (Ir.sizeScale.lookup name).map fun k =>
      #[s!"font-size: {decMilli k}em;"]

private def markerColorDecl (c : Ir.Color) (name : Option String) : String :=
  match name with
  | some n => s!"color: var(--{n}, {cssColor c});"
  | none => s!"color: {cssColor c};"

/-- The plain text of a marker whose every element is text — anything else
is not `::marker` content. Explicit arms: a new `Inline` constructor must
answer here (the obligation table; no wildcard in a backend's IR walk). -/
private def markerTextInto (acc : String) : List Inline → Option String
  | [] => some acc
  | .text s :: rest => markerTextInto (acc ++ s) rest
  | .math _ _ :: _ => none
  | .formula _ _ _ :: _ => none
  | .styled _ _ :: _ => none
  | .colored _ _ _ :: _ => none
  | .link _ _ :: _ => none
  | .underline _ :: _ => none
  | .fill :: _ => none
  | .pageNumber :: _ => none
  | .pageCount :: _ => none
  | .linebreak _ :: _ => none
  | .step _ _ _ :: _ => none
  | .image _ _ _ :: _ => none
  -- a `content` string cannot carry the icon's accessible name, so an icon
  -- marker is inexpressible here and diagnosed (W0331), never defaulted
  | .icon _ _ :: _ => none

mutual

/-- Resolve one marker element for `::marker`: a whole-content style wrapper
— it must wrap everything inside it, since one `::marker` rule styles the
whole marker — or plain text. `none` is the inexpressible remainder, which
the emitter must diagnose, never silently default (`styleRules`): the same
declaration then reaches both backends or the difference has a name.
Explicit arms (the obligation table; no wildcard in a backend's IR walk). -/
def markerCssOne (decls : Array String) : Inline → Option MarkerCss
  | .text s => some { text := s, decls := decls }
  | .styled st body =>
    match markerStyleDecls st with
    | some ds => markerCssList (decls ++ ds) body.toList
    | _ => none
  | .colored c name body =>
    markerCssList (decls.push (markerColorDecl c name)) body.toList
  | .math _ _ => none
  | .formula _ _ _ => none
  | .link _ _ => none
  | .underline _ => none
  | .fill => none
  | .pageNumber => none
  | .pageCount => none
  | .linebreak _ => none
  | .step _ _ _ => none
  | .image _ _ _ => none
  | .icon _ _ => none

def markerCssList (decls : Array String) : List Inline → Option MarkerCss
  | [x] => markerCssOne decls x
  | xs => (markerTextInto "" xs).map fun t => { text := t, decls := decls }

end

def markerCss? (m : Array Inline) : Option MarkerCss :=
  markerCssList #[] m.toList

private theorem markerTextInto_text (xs : List Inline) :
    ∀ acc t, markerTextInto acc xs = some t → t = acc ++ Ir.plainTextList xs := by
  induction xs with
  | nil =>
    intro acc t h
    simp [markerTextInto] at h
    simp [← h, Ir.plainTextList]
  | cons x rest ih =>
    intro acc t h
    cases x <;> simp [markerTextInto] at h
    rw [ih _ _ h]
    simp [Ir.plainTextList, Ir.plainTextOne, String.append_assoc]

mutual

/-- A marker `::marker` can express shows exactly the declared characters:
the emitted `content` is the marker's own plain text, so the HTML marker and
the PDF marker (which sets the same declared content as a line of its own)
can only differ where a diagnostic already names the substitution. -/
theorem markerCssOne_text (decls : Array String) (x : Inline) (r : MarkerCss)
    (h : markerCssOne decls x = some r) : r.text = Ir.plainTextOne x := by
  match x with
  | .text s =>
    simp [markerCssOne] at h
    simp [← h, Ir.plainTextOne]
  | .styled st body =>
    rw [markerCssOne] at h
    split at h
    · rw [Ir.plainTextOne]
      exact markerCssList_text _ body.toList r h
    · exact absurd h (by simp)
  | .colored c name body =>
    rw [markerCssOne] at h
    rw [Ir.plainTextOne]
    exact markerCssList_text _ body.toList r h
  | .math _ _ | .formula _ _ _ | .link _ _ | .underline _ | .fill
  | .pageNumber | .pageCount | .linebreak _ | .step _ _ _ | .image _ _ _
  | .icon _ _ =>
    simp [markerCssOne] at h

theorem markerCssList_text (decls : Array String) (xs : List Inline)
    (r : MarkerCss) (h : markerCssList decls xs = some r) :
    r.text = Ir.plainTextList xs := by
  match xs with
  | [x] =>
    rw [markerCssList] at h
    simp [Ir.plainTextList, markerCssOne_text decls x r h]
  | [] =>
    simp [markerCssList, markerTextInto] at h
    simp [← h, Ir.plainTextList]
  | x :: y :: rest =>
    rw [markerCssList] at h
    case x_1 => intro z hz; simp at hz
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨t, ht, hr⟩ := h
    rw [← hr]
    simpa using markerTextInto_text _ _ _ ht

end

theorem markerCss?_text (m : Array Inline) (r : MarkerCss)
    (h : markerCss? m = some r) : r.text = Ir.plainText m :=
  Ir.plainText.eq_def m ▸ markerCssList_text #[] m.toList r h

/-- A CSS string value: the two characters that could end the string or
start an escape are escaped (CSS Syntax 3 §4.3.7), so a declared marker's
characters can never break out of their `content` string. -/
def cssString (s : String) : String :=
  (s.replace "\\" "\\\\").replace "\"" "\\\""

/-- `\style` declarations as CSS on the element selectors. A declared marker
becomes a `::marker` rule when it is expressible there — plain text under
colour and font wrappers (`markerCss?`; CSS Pseudo-Elements 4 §4.1) — and
the inexpressible remainder is diagnosed by name (W0328), never silently
defaulted: the PDF sets the same declared content, so a silent fallback here
is a silent backend divergence (FINDINGS F1). A base list element styles
every nesting level (as the PDF path does), so its marker rule is emitted at
each depth — the depth-qualified selectors match the level defaults'
specificity and, standing later in the sheet, win. -/
def styleRules (doc : Doc) : String × Array Diag :=
  let sel : String → Option String
    | "titlepage" => some "h1"
    | "section" => some "h2" | "subsection" => some "h3" | "subsubsection" => some "h4"
    | "itemize" => some "ul" | "enumerate" => some "ol"
    | "itemize2" => some "ul ul" | "itemize3" => some "ul ul ul"
    | "itemize4" => some "ul ul ul ul"
    | "enumerate2" => some "ol ol" | "enumerate3" => some "ol ol ol"
    | "enumerate4" => some "ol ol ol ol"
    | "nav" => some "nav"
    | _ => none
  let markerSel : String → String
    | "ul" => "ul > li::marker, ul ul > li::marker, ul ul ul > li::marker, " ++
      "ul ul ul ul > li::marker"
    | "ol" => "ol > li::marker, ol ol > li::marker, ol ol ol > li::marker, " ++
      "ol ol ol ol > li::marker"
    | tag => s!"{tag} > li::marker"
  Id.run do
  let mut css := ""
  let mut diags : Array Diag := #[]
  for (element, st) in doc.styles.entries do
    let some tag := sel element | continue
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
    let mut liDecls :=
      (st.gap.map fun g => s!"{tag} > li \{ margin-top: {cssLength g.width}; }\n").toList
    if let some m := st.marker then
      match markerCss? m with
      | some r =>
        let body := String.join (r.decls.toList.map (" " ++ ·))
        liDecls := liDecls ++
          [s!"{markerSel tag} \{ content: \"{cssString r.text}  \";{body} }\n"]
      | none =>
        diags := diags.push (Diag.of .W0331
          s!"the declared '{element}' marker is not expressible in HTML; \
the level default marks these items"
          (help := some "marker = {...} reaches HTML as text with colour \
and font styling (CSS Pseudo-Elements 4 §4.1); a link, an image, math, or \
an overlay step does not"))
    -- Interaction states live on the element's links (the interactive
    -- content a hover or focus can land on; for `nav` that is `nav a`).
    -- The colour keeps its token spelling, like every named colour here,
    -- and a declared motion goes through `motionCss` — the guarded form is
    -- the only form the emitter has.
    let iSel := s!"{tag} a"
    let tokenColor (c : Ir.Color) (n : Option String) : String := match n with
      | some name => s!"var(--{name}, {cssColor c})"
      | none => cssColor c
    let interDecls :=
      (st.hover.map fun (c, n) =>
        s!"{iSel}:hover \{ color: {tokenColor c n}; }\n").toList ++
      (st.focus.map fun (c, n) =>
        s!"{iSel}:focus-visible \{ outline-color: {tokenColor c n}; }\n").toList ++
      (st.motion.map fun ms => motionCss iSel ms).toList
    let own := if decls.isEmpty then "" else s!"{tag} \{ {String.intercalate " " decls} }\n"
    -- Bound first: appending a call's result directly is the shape the
    -- cost gate rejects; a name makes the one-off append visible as one.
    let liCss := String.join liDecls
    let interCss := String.join interDecls
    css := css ++ own ++ liCss ++ interCss
  return (css, diags)

/-- Furniture the semantic palette keys turn on — one shared rule set for
every theme, so a theme stays a table of values. The conditions read the
resolved `Design`, the same record the PDF path consumes; a rule fires only
when the design carries the feature. The colour *values* stay CSS custom
properties rather than resolved literals, deliberately: a reader's
stylesheet can override a token, which is the HTML backend's contract. -/
def themeCss (doc : Doc) : String :=
  let d := Design.ofDoc doc
  (if d.bgDeclared then "body { background: var(--bg); }\n" else "") ++
  (if d.fgDeclared then "body { color: var(--fg); }\n" else "") ++
  (if d.frametitle.isSome then
    "section.slide > header { background: var(--frametitlebg);\n" ++
    "  color: var(--frametitlefg, var(--bg, #fff));\n" ++
    "  margin: -1.4rem -1.8rem 0.8rem; padding: 0.7rem 1.8rem;\n" ++
    "  border-radius: 7px 7px 0 0; }\n" ++
    "section.slide > header h2 { color: inherit; }\n" else "") ++
  (if d.progress.isSome then
    "section.section-page { text-align: center; padding: 2.5rem 0;\n" ++
    "  break-inside: avoid; }\n" ++
    "section.section-page h2 { display: inline-block; text-align: left;\n" ++
    "  min-width: 60%; margin: 0; }\n" ++
    ".progress { background: var(--progressbg, var(--rule)); height: 3px;\n" ++
    "  width: 60%; margin: 0.6rem auto 0; }\n" ++
    ".progress > div { background: var(--progressfg); height: 100%; }\n" else "") ++
  -- The chrome footer: colour from the muted key, size from the shared
  -- scale (`size-small` on the element), positions fixed by the declared
  -- side — each slot pinned to its edge, as `Layout.bandSlotX` pins the
  -- page's — so nothing a slot contains can move another. The band holds
  -- one line (`min-height: 1lh`, CSS Values 4 §6.1.3: the element's own
  -- line-height); a colliding slot paints under or over by declared
  -- priority (`z-index` from `BandSlot.rank`, set per span), never moves.
  (if doc.docClass == "slides" && doc.foot.isNone &&
      (doc.chrome.hasFooter || doc.body.any fun b => match b with
        | .framefoot xs => !xs.isEmpty
        | _ => false) then
    "section.slide > footer.slide-foot { position: relative;\n" ++
    "  min-height: 1lh; margin-top: 1.2rem; color: var(--muted); }\n" ++
    "footer.slide-foot > .band-left { position: absolute; left: 0;\n" ++
    "  white-space: nowrap; }\n" ++
    "footer.slide-foot > .band-right { position: absolute; right: 0;\n" ++
    "  white-space: nowrap; }\n" else "")

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

/-- A per-mille factor as CSS text: 1440 → `1.440`. -/
private def milliFactor (k : Nat) : String :=
  let pad (n : Nat) : String :=
    let s := toString n
    "".pushn '0' (3 - min 3 s.length) ++ s
  s!"{k / 1000}.{pad (k % 1000)}"

/-- One scale step as a CSS size: the same table the PDF sets from
(`Ir.sizeScale`), so a heading or a standout is the size the scale says,
never a re-spelled decimal. -/
private def scaleSize (name : String) (unit : String) : String :=
  milliFactor ((Ir.sizeScale.lookup name).getD 1000) ++ unit

/-- Screen prose leading, per-mille. Screen body text wants more lead than
the print ratio (`Ir.leadingMilli`, 6/5); Butterick's band for body text is
120–145% (Practical Typography, "Line spacing"), and the stylesheet takes
its top. The old 1.55 sat outside the band, undeclared. -/
def bodyLeadingMilli : Nat := 1450

/-- The screen leading stays inside Butterick's 120–145% band, and never
under the engine's own print leading — the stylesheet's body text cannot
drift out of the sourced range without failing the build. -/
theorem body_leading_in_band :
    Ir.leadingMilli ≤ bodyLeadingMilli ∧
    1200 ≤ bodyLeadingMilli ∧ bodyLeadingMilli ≤ 1450 := by decide

/-- Size rules generated from the IR's scale, so the two backends cannot drift
apart on what `\Huge` means. `em` rather than `rem`: sizes nest. -/
private def sizeRules : String :=
  String.join (Ir.sizeScale.map fun (name, k) =>
    s!".size-{name} \{ font-size: {milliFactor k}em; }\n")

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
  s!"  line-height: {milliFactor bodyLeadingMilli};\n" ++
  "  text-rendering: optimizeLegibility;\n" ++
  "  -webkit-font-smoothing: antialiased;\n" ++
  "}\n" ++
  "main { max-width: var(--measure); margin: 0 auto; }\n" ++
  -- Headings from the IR's own scale — the sizes the PDF sets
  -- (`Layout.sectionSize`, classes.dtx §Sectioning: the title at LARGE, a
  -- section at Large, a subsection at large), so `heading_hierarchy`'s
  -- ordering covers this backend for free; the line height is the
  -- engine's one leading ratio. Hand-picked decimals here once drifted a
  -- rounding step from the scale sixty lines above the rules generated
  -- from it.
  "h1, h2, h3, h4 {\n" ++
  "  font-family: var(--font-sans);\n" ++
  "  font-weight: 600;\n" ++
  s!"  line-height: {milliFactor Ir.leadingMilli};\n" ++
  "  margin: 2.25rem 0 0.6rem;\n" ++
  "  text-wrap: balance;\n" ++
  "}\n" ++
  s!"h1 \{ font-size: {scaleSize "LARGE" "rem"}; margin-top: 0; }\n" ++
  s!"h2 \{ font-size: {scaleSize "Large" "rem"}; }\n" ++
  s!"h3 \{ font-size: {scaleSize "large" "rem"}; }\n" ++
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
  -- booktabs' formal table: the three rule weights and their paddings come
  -- from the sourced constants in Ir (booktabs.dtx §The code), emitted
  -- here so the two backends cannot drift; each is overridable through
  -- its token (`--heavyrulewidth` etc. land in `tokenVars` when declared).
  -- Borders take `currentColor`, as the PDF path draws rules in `fg`.
  "table.booktabs { border-collapse: collapse; }\n" ++
  s!"table.booktabs td \{ padding: 0 var(--tabcolsep, {cssLength Ir.tabColSep});\n" ++
  "  vertical-align: top; }\n" ++
  "table.booktabs.nopadl tr > td:first-child { padding-left: 0; }\n" ++
  "table.booktabs.nopadr tr > td:last-child { padding-right: 0; }\n" ++
  s!"tr.bt-heavy-above > td \{ border-top: var(--heavyrulewidth, {cssLength Ir.heavyRuleWidth}) solid;\n" ++
  s!"  padding-top: var(--belowrulesep, {cssLength Ir.belowRuleSep}); }\n" ++
  s!"tr.bt-light-above > td \{ border-top: var(--lightrulewidth, {cssLength Ir.lightRuleWidth}) solid;\n" ++
  s!"  padding-top: var(--belowrulesep, {cssLength Ir.belowRuleSep}); }\n" ++
  s!"tr.bt-heavy-below > td \{ border-bottom: var(--heavyrulewidth, {cssLength Ir.heavyRuleWidth}) solid;\n" ++
  s!"  padding-bottom: var(--aboverulesep, {cssLength Ir.aboveRuleSep}); }\n" ++
  s!"tr.bt-light-below > td \{ border-bottom: var(--lightrulewidth, {cssLength Ir.lightRuleWidth}) solid;\n" ++
  s!"  padding-bottom: var(--aboverulesep, {cssLength Ir.aboveRuleSep}); }\n" ++
  s!"tr.bt-pre > td \{ padding-bottom: var(--aboverulesep, {cssLength Ir.aboveRuleSep}); }\n" ++
  s!"td.bt-cmid \{ border-top: var(--cmidrulewidth, {cssLength Ir.cmidRuleWidth}) solid;\n" ++
  s!"  padding-top: var(--belowrulesep, {cssLength Ir.belowRuleSep}); }\n" ++
  -- Float and caption gaps: the same tokens the PDF path reads, defaults
  -- held to the rhythm by `Layout.caption_gaps_rhythm`.
  s!"figure.float \{ margin: var(--floatsep, {cssLength Ir.floatSepDefault.width}) auto; }\n" ++
  "figure.float > table { margin-left: auto; margin-right: auto; }\n" ++
  "figure.float > img { display: block; margin: 0 auto; }\n" ++
  s!"figure.float > figcaption \{ margin-top: var(--captionsep, {cssLength Ir.captionSepDefault.width});\n" ++
  "  text-align: center; text-wrap: balance; }\n" ++
  s!"figure.float > figcaption:first-child \{ margin-top: 0;\n" ++
  s!"  margin-bottom: var(--captionsep, {cssLength Ir.captionSepDefault.width}); }\n" ++
  -- Slides, as the linear handout: one bordered section per frame, printing
  -- one per page. The interactive controller is the rest of M5.
  "section.slide { border: 1px solid var(--rule); border-radius: 8px;\n" ++
  "  padding: 1.4rem 1.8rem; margin: 1.4rem 0; break-inside: avoid; }\n" ++
  "section.slide > header h2 { margin: 0 0 0.8rem; font-size: 1.35rem; }\n" ++
  -- A standout frame inverts: the palette's standout keys override, and
  -- without them the page's own fg/bg swap — the same rule as the PDF path.
  -- Its size is the scale's own Large step (`\Large\bfseries`, the shipped
  -- bundles' standout template), never a re-spelled decimal.
  "section.slide.standout { background: var(--standoutbg, var(--fg, #18181b));\n" ++
  "  color: var(--standoutfg, var(--bg, #fafaf9)); text-align: center;\n" ++
  s!"  font-size: {scaleSize "Large" "em"}; font-weight: 600;\n" ++
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
  | .image src size alt =>
    -- The typed tree and the escaper carry the attributes; the intrinsic
    -- pixel size rides as width/height so the page never reflows while the
    -- file loads, and the requested size becomes CSS. A fraction of the
    -- text width is a percentage — HTML's measure is the container. A
    -- `\textheight` fraction has no CSS analog and the intrinsic size
    -- stands. `height: auto` (or width) keeps the browser on the intrinsic
    -- ratio, the same invariant the PDF path proves.
    let info? := (cfg.imgs.find? src).bind fun k => (cfg.imgs.get? k).bind (·.info)
    -- A bare graphicx name resolved to a file with an extension: the link
    -- must name the file on disk, not the spelling in the source.
    let href := match (cfg.imgs.find? src).bind fun k => cfg.imgs.get? k with
      | some entry => if entry.href.isEmpty then src else entry.href
      | none => src
    let cssDim (l : Image.Len) : Option String :=
      if l.tw != 0 && l.sp == 0 && l.th == 0 then
        some (decMilli (l.tw * 100) ++ "%")
      else if l.sp != 0 && l.tw == 0 && l.th == 0 then
        some s!"{Dim.Sp.toPtString l.sp}pt"
      else none
    let wCss := size.width.bind cssDim
    let hCss := size.height.bind cssDim
    let style : Option String :=
      match wCss, hCss with
      | some w, some h =>
        some (s!"width: {w}; height: {h}" ++
          (if size.keepAspect then "; object-fit: contain" else ""))
      | some w, none => some s!"width: {w}; height: auto"
      | none, some h => some s!"height: {h}; width: auto"
      | none, none =>
        if size.width.isNone && size.height.isNone &&
            (size.scaleNum != 1 || size.scaleDen != 1) then
          info?.map fun inf =>
            s!"width: {Dim.Sp.toPtString (inf.width * size.scaleNum / size.scaleDen)}pt; \
height: auto"
        else none
    let attrs := #[("src", href), ("alt", alt)] ++
      (match info? with
       | some inf => #[("width", toString inf.pxW), ("height", toString inf.pxH)]
       | none => #[]) ++
      (match style with
       | some st => #[("style", st)]
       | none => #[])
    acc.push (Html.elem "img" #[] attrs)
  | .math display src =>
    -- Until native MathML lands the source rides in a data attribute, so an
    -- optional client-side renderer can find it and nothing is faked.
    let tag := if display then "div" else "span"
    acc.push (Html.elem tag #[Html.text src]
      #[("class", if display then "math math-display" else "math"),
        ("data-tex", src)])
  | .formula display src _ =>
    -- The HTML backend is unchanged by the M6 PDF slice: an elaborated
    -- formula still ships its source for the `--math-boundary` renderer.
    -- Native MathML from the parsed atoms is what M6 still owes here.
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
  | .icon c label =>
    -- The glyph is a Private Use Area scalar assistive technology cannot
    -- read, so it is hidden (`aria-hidden`) and the accessible name rides
    -- the wrapper: `role="img"` names the composite and makes the glyph
    -- span presentational (WCAG 2.2 SC 1.1.1; WAI-ARIA 1.2 §img — children
    -- of an img role are presentational). The `icon` class is the styling
    -- hook a stylesheet uses to name the icon face.
    acc.push (Html.elem "span"
      #[Html.elem "span" #[Html.text (String.ofList [c])] #[("aria-hidden", "true")]]
      #[("class", "icon"), ("role", "img"), ("aria-label", label)])
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

/-- The heading tag a section level takes: level 0 is the document title —
`h1` is "for a top-level section" (HTML §4.3.6) — and each deeper level
takes the next tag, so an IR outline without gaps ships as a page outline
without gaps (§4.3.11's conformance rule). One fact, shared with the
markdown backend's `#` count; `heading_renderings_agree` in Tests pins the
agreement. -/
def headingTag : Nat → String
  | 0 => "h1"
  | 1 => "h2"
  | 2 => "h3"
  | _ => "h4"

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
    let element := match level with
      | 0 => "titlepage"
      | 1 => "section"
      | 2 => "subsection"
      | _ => "subsubsection"
    let tag := headingTag level
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
  -- A quotation is HTML's own construct: `<blockquote>` carries the
  -- set-off semantics that the PDF path expresses as margins.
  | .quote body =>
    Html.elem "blockquote" (blockNodesInto cfg #[] body.toList)
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
  | .pagebreak =>
    -- A continuous medium has no page to break; the boundary leaves no
    -- element behind.
    Html.text ""
  | .spaced before body =>
    let style := s!"margin-top: {cssLength before.width}"
    Html.elem "div" (blockNodesInto cfg #[] body.toList)
      #[("class", "spaced"), ("style", style)]
  | .verbatim covered s =>
    -- `<pre>` preserves the raw lines; the escaper makes the content inert.
    -- The covered shade never reaches HTML (dimming is the PDF handout's;
    -- the HTML deck keeps every step visible), but honesty if it ever does.
    Html.elem "pre" #[Html.elem "code"
      #[Html.text (String.intercalate "\n" (verbatimLines s).toList)]]
      (match covered with
       | some c => #[("style", s!"color: {cssColor c}")]
       | none => #[])
  | .rule color name thickness =>
    -- The title page's separator: an <hr> carrying the palette variable,
    -- so a host page can override it as it can any colour.
    let c := match name with
      | some n => s!"var(--{n}, {cssColor color})"
      | none => cssColor color
    Html.elem "hr" #[] #[("class", "separator"),
      ("style", s!"border: none; height: {cssLength thickness.width}; background: {c}")]
  | .frame title standout _ body =>
    -- One slide of the deck. With no controller yet this is the no-JS
    -- rendering the plan promises anyway: a linear readable handout, every
    -- slide a section.
    let header := if title.isEmpty then #[]
      else #[Html.elem "header" #[Html.elem "h2" (inlines cfg title)]]
    let cls := if standout then "slide standout" else "slide"
    Html.elem "section" (header ++ blockNodesInto cfg #[] body.toList) #[("class", cls)]
  | .framefoot _ =>
    -- A state change for the deck walk in `emit`, not content: nothing to
    -- render where one stands alone.
    Html.text ""
  | .only targets body =>
    -- `emit` already kept this node for HTML (`Ir.keepFor "html"`): by here
    -- it is a transparent group. The target set rides as data, so a reader
    -- of the page can see the provenance of single-surface content.
    Html.elem "div" (blockNodesInto cfg #[] body.toList)
      #[("data-backend", String.intercalate "," targets.toList)]
  | .nav spec body =>
    -- The navigation landmark (ARIA's `navigation` role comes with the
    -- element itself). A declared label names the instance (`aria-label`;
    -- ARIA Authoring Practices, Landmark Regions) and `emit` counts only
    -- unlabeled navs toward W0325. A declared pin becomes `position:
    -- fixed` at the declared corner and offset (CSS Positioned Layout 3
    -- §3.3); the reveal rides as the `reveal-scroll` class plus its range,
    -- resolved by `revealCss` at the page level.
    let labelAttrs : Array (String × String) :=
      match spec.label with
      | some l => #[("aria-label", l)]
      | none => #[]
    let pinAttrs : Array (String × String) :=
      match spec.pin with
      | some pin =>
        let v := if pin.top then "top" else "bottom"
        let h := if pin.left then "left" else "right"
        let off := cssLength pin.offset.width
        let style := s!"position: fixed; {v}: {off}; {h}: {off}" ++
          (match pin.revealBy with
           | some g => s!"; --reveal-range: {cssLength g.width}"
           | none => "")
        (if pin.reveal then #[("class", "reveal-scroll")] else #[]).push
          ("style", style)
      | none => #[]
    Html.elem "nav" (blockNodesInto cfg #[] body.toList) (labelAttrs ++ pinAttrs)
  | .logo _ =>
    -- Paged-media furniture; `blockNodesInto` skips it (and `emit` says
    -- so), so this arm only closes the match.
    Html.text ""
  | .picture pic =>
    -- The picture as inline SVG: the same evaluated shapes the PDF paints,
    -- through the typed tree so every label passes the escaper. SVG's y
    -- grows downward, so the transform is the PDF path's: flip against the
    -- box's top. Lengths are pt, the unit the viewBox declares.
    let ((px0, py0), (px1, py1)) := pic.bbox
    let w := px1 - px0
    let h := py1 - py0
    let kids := pic.shapes.map fun shape =>
      match shape with
      | .rect rx ry rw rh color =>
        Html.elem "rect" #[] #[
          ("x", (min rx (rx + rw) - px0).toPtString),
          ("y", (py1 - max ry (ry + rh)).toPtString),
          ("width", (max rw (-rw)).toPtString),
          ("height", (max rh (-rh)).toPtString),
          ("fill", cssColor color)]
      | .label lx ly text color scale =>
        Html.elem "text" #[Html.text text] #[
          ("x", (lx - px0).toPtString),
          ("y", (py1 - ly).toPtString),
          ("fill", cssColor color),
          ("font-size", (Ir.baseFontSize * (scale : Int) / 1000).toPtString),
          ("text-anchor", "middle"),
          ("dominant-baseline", "central")]
    Html.elem "svg" kids #[
      ("viewBox", s!"0 0 {w.toPtString} {h.toPtString}"),
      ("width", s!"{w.toPtString}pt"),
      ("height", s!"{h.toPtString}pt"),
      ("role", "img"),
      ("class", "picture")]
  -- booktabs' formal table. Rules land as border classes on the row they
  -- precede (`-below` on the last row for a rule written after it), and
  -- the stylesheet draws each class at the sourced weight with its
  -- declared padding — `Ir.heavyRuleWidth` and friends drive both
  -- backends from one site. A `gap` rule and `\cmidrule` end-trimming
  -- have no HTML spelling yet; the PDF path carries both.
  | .table cols padL padR rows rules =>
    let ruleAt (i : Nat) : Array Ir.TableRule :=
      rules.foldl (fun out (k, r) => if k == i then out.push r else out) #[]
    let drawn (r : Ir.TableRule) : Bool := match r with
      | .gap _ => false
      | _ => true
    let colEls := cols.filterMap fun c =>
      match c.width with
      | .frac f => some (Html.elem "col" #[] #[("style", s!"width: {decMilli (f * 100)}%")])
      | .abs w => some (Html.elem "col" #[] #[("style", s!"width: {w.toPtString}pt")])
      | .natural => some (Html.elem "col" #[] #[])
    let rowEls := rows.mapIdx fun i row =>
      let cls := Id.run do
        let mut cls : Array String := #[]
        for r in ruleAt i do
          match r with
          | .top | .bottom => cls := cls.push "bt-heavy-above"
          | .mid => cls := cls.push "bt-light-above"
          | _ => pure ()
        if i + 1 == rows.size then
          for r in ruleAt rows.size do
            match r with
            | .top | .bottom => cls := cls.push "bt-heavy-below"
            | .mid => cls := cls.push "bt-light-below"
            | _ => pure ()
        else if (ruleAt (i + 1)).any drawn then
          cls := cls.push "bt-pre"
        return String.intercalate " " cls.toList
      let cmids := (ruleAt i).foldl (fun out r => match r with
        | .cmid a b _ _ => out.push (a, b)
        | _ => out) (#[] : Array (Nat × Nat))
      let cells := row.mapIdx fun j cell =>
        let al := match (cols[j]?.map (·.align)).getD .left with
          | .center => #[("style", "text-align: center")]
          | .right => #[("style", "text-align: right")]
          | .left => #[]
        let attrs := if cmids.any (fun (a, b) => a ≤ j + 1 && j + 1 ≤ b)
          then al.push ("class", "bt-cmid") else al
        Html.elem "td" (inlines cfg cell) attrs
      Html.elem "tr" cells (if cls.isEmpty then #[] else #[("class", cls)])
    let cls := "booktabs" ++ (if padL then "" else " nopadl")
      ++ (if padR then "" else " nopadr")
    Html.elem "table" (#[Html.elem "colgroup" colEls] ++ rowEls) #[("class", cls)]
  -- `<figure>`/`<figcaption>` is HTML's own construct for a captioned
  -- object; the caption keeps its source-order side. The gaps are the
  -- same tokens the PDF path reads (`--floatsep`, `--captionsep`), with
  -- the rhythm defaults from `caption_gaps_rhythm` as fallbacks.
  | .float kind capAbove body caption =>
    let capNode : Array Node :=
      if caption.isEmpty then #[]
      else #[Html.elem "figcaption" (inlines cfg caption)]
    let kids := blockNodesInto cfg #[] body.toList
    let cls := match kind with
      | .table => "float table-float"
      | .figure => "float"
    Html.elem "figure" (if capAbove then capNode ++ kids else kids ++ capNode)
      #[("class", cls)]

/-- The accumulator threads through the sibling walk, as in `inlineNodesInto`. -/
private def blockNodesInto (cfg : Config) (acc : Array Node) : List Block → Array Node
  | [] => acc
  | .logo _ :: rest => blockNodesInto cfg acc rest
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

/-- Facts of the emitted tree that the landmark and anchor checks judge:
the `<nav>` landmarks, the `id` anchors, and the in-page link targets
(`href="#..."`), collected in one walk over the typed tree. The artifact is
judged, never the IR — a backend conditional may have dropped a nav or an
anchor on the way here, and only the tree knows what this page carries. -/
private structure PageFacts where
  ids : Array String := #[]
  fragmentRefs : Array String := #[]
  /-- Unlabeled `<nav>` landmarks: a labeled one is distinguishable, so
  only these count toward W0325 (ARIA Landmark Regions). -/
  navs : Nat := 0
  /-- Elements carrying the `reveal-scroll` class: the page-level reveal
  CSS and script ship exactly when one is here — judged over the tree, so
  a reveal a conditional dropped ships nothing. -/
  reveals : Nat := 0

mutual

private def pageFactsOne (acc : PageFacts) : Node → PageFacts
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem tag attrs kids =>
    let acc := if tag == "nav" && attrs.all (·.1 != "aria-label") then
        { acc with navs := acc.navs + 1 } else acc
    let acc := if attrs.any (fun kv => kv.1 == "class" && kv.2 == "reveal-scroll") then
        { acc with reveals := acc.reveals + 1 } else acc
    let acc := attrs.foldl (init := acc) fun a kv =>
      if kv.1 == "id" then { a with ids := a.ids.push kv.2 }
      else if kv.1 == "href" && kv.2.startsWith "#" then
        { a with fragmentRefs := a.fragmentRefs.push kv.2 }
      else a
    pageFactsList acc kids.toList

private def pageFactsList (acc : PageFacts) : List Node → PageFacts
  | [] => acc
  | k :: rest => pageFactsList (pageFactsOne acc k) rest

end

/-- Unicode `White_Space` (PropList.txt, maintained under UAX #44): the
closed set 0009–000D, 0020, 0085, 00A0, 1680, 2000–200A, 2028, 2029, 202F,
205F, 3000. HTML forbids only ASCII whitespace in an id (§3.2.6), a subset
of this set; treating every White_Space character as a separator also keeps
the thin spaces the engine itself emits for `\,`/`\:`/`\;` out of anchors. -/
def isWhiteSpaceUni (c : Char) : Bool :=
  let n := c.toNat
  (0x09 ≤ n && n ≤ 0x0D) || n == 0x20 || n == 0x85 || n == 0xA0 ||
  n == 0x1680 || (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 || n == 0x2029 ||
  n == 0x202F || n == 0x205F || n == 0x3000

/-- One character of an anchor: ASCII letters and digits lowercased, every
other non-ASCII scalar kept (`none` marks a separator). HTML §3.2.6 places
no restriction on an id beyond non-emptiness and the absence of ASCII
whitespace, and the WHATWG URL fragment percent-encode set (§1.3) excludes
non-ASCII — U+00A0–U+10FFFD are URL code points (§4.3) — so `Café`'s é
belongs in its anchor rather than degrading to a hyphen. The keep-check
runs on the already-lowered character, which is what makes
`slugCharKeep_not_whitespace` a case split over its own guards. -/
def slugCharKeep (k : Char) : Option Char :=
  if isWhiteSpaceUni k then none
  else if k.isAlpha || k.isDigit then some k
  else if 0x80 ≤ k.toNat then some k
  else none

def slugChar (c : Char) : Option Char :=
  slugCharKeep (if c.isAlpha || c.isDigit then c.toLower else c)

/-- The slug walk: separators collapse to one hyphen, emitted only between
kept characters, so no leading or trailing hyphen can exist by construction. -/
def slugGo (acc : Array Char) (sep : Bool) : List Char → Array Char
  | [] => acc
  | c :: rest =>
    match slugChar c with
    | some k =>
      if sep && !acc.isEmpty then slugGo ((acc.push '-').push k) false rest
      else slugGo (acc.push k) false rest
    | none => slugGo acc true rest

/-- An anchor id from a title's own text. Every static site generator derives
ids this way, so an in-page `\href{#experience}` has a target by construction
rather than by a label the author must remember to declare. Non-emptiness —
the other half of HTML §3.2.6's requirement — is `sectionize`'s job: an
all-separator title takes the id `section`. Not done, stated rather than
hidden: Unicode normalisation (UAX #15 NFC) — a composed and a decomposed
`é` make two different anchors; PLAN carries the debt. -/
def slug (title : Array Inline) : String :=
  String.ofList (slugGo #[] false (Ir.plainText title).toList).toList

theorem slugCharKeep_not_whitespace (k k' : Char) (h : slugCharKeep k = some k') :
    isWhiteSpaceUni k' = false := by
  unfold slugCharKeep at h
  split at h
  · exact absurd h (by simp)
  · next hws =>
    have hws' : isWhiteSpaceUni k = false := by simpa using hws
    split at h
    · cases h; exact hws'
    · split at h
      · cases h; exact hws'
      · exact absurd h (by simp)

theorem slugChar_not_whitespace (c k : Char) (h : slugChar c = some k) :
    isWhiteSpaceUni k = false :=
  slugCharKeep_not_whitespace _ _ h

theorem slugGo_no_whitespace (l : List Char) (acc : Array Char) (sep : Bool)
    (hacc : ∀ c ∈ acc.toList, isWhiteSpaceUni c = false) :
    ∀ c ∈ (slugGo acc sep l).toList, isWhiteSpaceUni c = false := by
  induction l generalizing acc sep with
  | nil => simpa [slugGo] using hacc
  | cons c rest ih =>
    simp only [slugGo]
    split
    · next k hk =>
      have hkw := slugChar_not_whitespace c k hk
      split
      · apply ih
        intro d hd
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hd
        rcases hd with (hd | hd) | hd
        · exact hacc d hd
        · subst hd; decide
        · subst hd; exact hkw
      · apply ih
        intro d hd
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hd
        rcases hd with hd | hd
        · exact hacc d hd
        · subst hd; exact hkw
    · exact ih acc true hacc

/-- The addressability half of HTML §3.2.6's id contract, proved in the
stronger Unicode form: no character of a slug is `White_Space`, so in
particular none is ASCII whitespace ("The value must not contain any ASCII
whitespace"). Non-emptiness is discharged at the one use site. -/
theorem slug_no_whitespace (title : Array Inline) :
    ∀ c ∈ (slug title).toList, isWhiteSpaceUni c = false := by
  intro c hc
  simp only [slug, String.toList_ofList] at hc
  exact slugGo_no_whitespace _ _ _ (by simp) c hc

/-- An article's top-level sections become `<section id="...">` containers:
the heading and everything up to the next level-1 heading. The id gives every
section an anchor and a styling handle, and the container is what HTML 5 says
a heading-introduced region is (§4.3.3). Content before the first section
stays a direct child of `<main>`.

Ids are unique by construction — a section takes the first of `base`,
`base-2`, `base-3`, … not already assigned, which `getElementById` semantics
require — and distinct titles are meant to produce distinct anchors. When
they cannot (two different titles fold to the same slug), the collision is
named as W0327 rather than resolved silently: an in-page link written from
the second title's text would reach the first section without any error. A
repeated identical title takes its number quietly, as every static site
generator does. -/
private def sectionize (cfg : Config) (blocks : Array Block) :
    Array Node × Array Diag := Id.run do
  let close (out cur : Array Node) : Option String → Array Node
    | some id => out.push (Html.elem "section" cur #[("id", id)])
    | none => out ++ cur
  let mut out : Array Node := #[]
  let mut cur : Array Node := #[]
  let mut openId : Option String := none
  -- Each assigned id with the plain text of the title that holds it.
  let mut taken : Array (String × String) := #[]
  let mut diags : Array Diag := #[]
  for b in blocks do
    match b with
    | .section 1 _ title =>
      out := close out cur openId
      let text := Ir.plainText title
      let base := slug title
      let base := if base.isEmpty then "section" else base
      -- k assigned ids can block at most k candidates, so the first free
      -- one is always found among the k+1 checked here.
      let mut id := base
      let mut clash : Option String := none
      for n in [2 : taken.size + 3] do
        match taken.find? (·.1 == id) with
        | some (_, holder) =>
          if holder != text && clash.isNone then
            clash := some holder
          id := s!"{base}-{n}"
        | none => break
      if let some holder := clash then
        diags := diags.push (Diag.of .W0327
          s!"sections {holder.quote} and {text.quote} share the \
anchor '{base}'; the second becomes '{id}'"
          (help := some s!"an in-page link '#{base}' reaches only the first; \
retitle one section, or link to '#{id}'"))
      taken := taken.push (id, text)
      openId := some id
      cur := #[blockNode cfg b]
    | _ => cur := cur.push (blockNode cfg b)
  return (close out cur openId, diags)

/-- Emit a document as its typed tree — head and body nodes — plus any
diagnostics the backend itself raises; `emit` renders it. The tree is the
page before serialization: what the cross-backend agreement census judges
against the PDF's `Layout.Out`, so a divergence is caught on structure, not
by parsing the rendering back. -/
def emitTree (cfg : Config) (doc : Doc) :
    Array Node × Array Node × Array Diag := Id.run do
  -- The page's view of the document: backend conditionals resolve here, at
  -- the backend's entry (`Ir.keepFor_covers` is why dropping cannot lose
  -- content), so every walk below — sectioning, the deck chrome, the
  -- landmark and anchor checks — sees only what this page carries.
  let doc := { doc with body := Ir.keepFor "html" doc.body }
  let mut diags : Array Diag := #[]
  if doc.head.isSome || doc.foot.isSome then
    diags := diags.push (Diag.of .W0007
      "running head/foot is paged-media furniture; omitted from HTML"
      (help := "body content reaches both backends: move the masthead there"))
  if doc.logo.isSome || doc.body.any (fun b => match b with
      | .logo c => !c.isEmpty
      | _ => false) then
    diags := diags.push (Diag.of .W0007
      "the \\logo is paged-media furniture; omitted from HTML"
      (help := "body content reaches both backends: move the image there"))
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
  -- The declared web identity, each fact emitted once per surface. The
  -- canonical URL is `rel=canonical` (RFC 6596); the icon `rel=icon`
  -- (HTML §4.6.6.8). The Open Graph set is a projection of facts already
  -- declared once — og:title/og:description/og:url/og:image restate title,
  -- subject, url, image — never asked for again, which is how the drift
  -- the site-port found ("Experience" vs "Professional Experience")
  -- becomes unrepresentable. It appears only when the document declares a
  -- web identity (url or image): ogp.me requires og:url for a valid
  -- object, and og:type's own default, `website`, is emitted explicitly
  -- because ogp.me lists it among the four required properties. X's card
  -- crawler falls back to og:* for title/description/image, so the one
  -- twitter-specific tag is the card kind itself (developer.x.com, cards
  -- markup): `summary`, the base card.
  if let some url := doc.info.url then
    head := head.push (Html.elem "link" #[] #[("rel", "canonical"), ("href", url)])
  if let some icon := doc.info.favicon then
    head := head.push (Html.elem "link" #[] #[("rel", "icon"), ("href", icon)])
  if let some md := cfg.mdHref then
    head := head.push (Html.elem "link" #[]
      #[("rel", "alternate"), ("type", "text/markdown"), ("href", md)])
  if doc.info.url.isSome || doc.info.image.isSome then
    let og (p v : String) : Node :=
      Html.elem "meta" #[] #[("property", p), ("content", v)]
    if let some t := doc.info.title then
      head := head.push (og "og:title" t)
    if let some s := doc.info.subject then
      head := head.push (og "og:description" s)
    if let some u := doc.info.url then
      head := head.push (og "og:url" u)
    if let some i := doc.info.image then
      head := head.push (og "og:image" i)
    head := head.push (og "og:type" "website")
    head := head.push (Html.elem "meta" #[]
      #[("name", "twitter:card"), ("content", "summary")])
  -- JSON-LD: the machine-readable projection of the same record, carried
  -- as a data block — a script with a non-JavaScript type is data, not
  -- behaviour (HTML §4.12.1), so the no-script architecture holds. The
  -- shape is schema.org's WebPage (name, description, url, image) with
  -- the author as a bare Person. Every value goes through the certified
  -- JSON escaper: `escapeJson_no_quote` says no value can end its own
  -- string, `escapeJson_no_lt` that the payload can never contain
  -- `</script` and so survives the raw-payload guard verbatim. The typed
  -- \person/\organization declaration the site-port report asks for is
  -- recorded in PLAN as owed; this emits only what the existing
  -- declarations already support.
  if doc.info.url.isSome then
    let jstr (s : String) : String := "\"" ++ Html.escapeJson s ++ "\""
    let field (k : String) : Option String → List String
      | some v => [s!"  {jstr k}: {jstr v}"]
      | none => []
    let author := match doc.info.author with
      | some a =>
        [s!"  {jstr "author"}: \{{jstr "@type"}: {jstr "Person"}, {jstr "name"}: {jstr a}}"]
      | none => []
    let fields :=
      [s!"  {jstr "@context"}: {jstr "https://schema.org"}",
       s!"  {jstr "@type"}: {jstr "WebPage"}"] ++
      field "name" doc.info.title ++ field "description" doc.info.subject ++
      field "url" doc.info.url ++ field "image" doc.info.image ++ author
    head := head.push (Node.script #[("type", "application/ld+json")]
      ("{\n" ++ String.intercalate ",\n" fields ++ "\n}"))
  head := head.push (Html.elem "meta" #[] #[("name", "generator"), ("content", "leantex")])
  -- Element styles are the document's own design and ride along in every
  -- mode: they are declarations, not a framework. A marker the sheet cannot
  -- express is named here (W0328), not silently defaulted.
  let (styled, styleDiags) := styleRules doc
  diags := diags ++ styleDiags
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
  -- The declared sheet comes after the inline styles: at equal specificity
  -- the later rule wins, so the document's own stylesheet can restyle the
  -- defaults instead of fighting them.
  if let some href := doc.output.stylesheet then
    head := head.push (Html.elem "link" #[] #[("rel", "stylesheet"), ("href", href)])
  let bodyClass := match cfg.css with
    | .bulma => "content"
    | _ => ""
  let cfg := { cfg with styles := doc.styles }
  -- The themed section page: in a slides document with progress keys, a
  -- top-level section becomes its own deck section carrying the position.
  let themedSections := doc.docClass == "slides" &&
    (Design.ofDoc doc).progress.isSome
  -- The chrome footer: every frame section closes with the section in
  -- force and its own frame number, in the muted key at the scale's small
  -- step — the same declarations the PDF path reads. A `\framefoot` note
  -- takes the left slot for the frames that follow.
  let hasFrameFoot := doc.body.any fun b => match b with
    | .framefoot xs => !xs.isEmpty
    | _ => false
  let chromeFoot := doc.docClass == "slides" && doc.foot.isNone &&
    (doc.chrome.hasFooter || hasFrameFoot)
  let (inner, sectionDiags) := if doc.docClass == "article" then
      sectionize cfg doc.body
    else if !themedSections && !chromeFoot then
      (blockNodesInto cfg #[] doc.body.toList, #[])
    else Id.run do
      -- The one numbering: the same array the PDF path threads
      -- (`Ir.frameNumbers`, T2–T4). This walk indexes it and counts
      -- nothing, so the two backends cannot disagree.
      let nums := doc.frameNumbers
      let total := doc.frameCount
      let mut done := 0
      let mut curSection : Array Inline := #[]
      let mut frameFoot : Option (Array Inline) := none
      let mut acc : Array Node := #[]
      let mut walkDiags : Array Diag := #[]
      for h : i in [0:doc.body.size] do
        let b := doc.body[i]
        match b with
        | .framefoot xs =>
          frameFoot := if xs.isEmpty then none else some xs
          -- A continuous page has no physical page number: the placeholder
          -- renders as nothing here while the PDF resolves it, so the drop
          -- is named — a divergence is declared or reported.
          if Ir.hasPhysicalPage xs && walkDiags.isEmpty then
            walkDiags := walkDiags.push (Diag.of .W0007
              "\\pagenumber in a \\framefoot is paged-media furniture; \
omitted from HTML"
              (help := some "the deck has no physical pages; \\framenumber \
via \\chrome is the sequence both backends share"))
        | .frame _ _ _ _ =>
          let num := nums[i]?.getD none
          done := num.getD done
          let node := blockNode cfg b
          let node := if chromeFoot then
              match num, node with
              | some n, .elem tag attrs kids =>
                -- The one slot band (`Ir.Chrome.footBand`): the same
                -- function the PDF's final pass consumes, so the two
                -- backends resolve the same slots and can only diverge by
                -- rendering them. Fixed positions come from the declared
                -- side (the stylesheet pins `band-left`/`band-right` to the
                -- edges, as `Layout.bandSlotX` does); the paint order is
                -- the declared priority, `z-index` carrying `rank` so a
                -- colliding lower-priority slot is painted under, in place,
                -- exactly as on the page.
                let band := doc.chrome.footBand frameFoot curSection n total
                Node.elem tag attrs (kids.push (Html.elem "footer"
                  (band.map fun s => Html.elem "span" (inlines cfg s.content)
                    #[("class", match s.side with
                        | .left => "band-left"
                        | .right => "band-right"),
                      ("style", s!"z-index: {s.rank}")])
                  #[("class", "slide-foot size-small")]))
              | _, other => other
            else node
          acc := acc.push node
        | .section 1 starred title =>
          curSection := title
          if themedSections then
            -- No clamp, as on the PDF path: `done ≤ total` by theorem
            -- over the numbering both walks read; a deck with no
            -- countable frame draws no bar.
            let kids := #[Html.elem "h2" (inlines cfg title)]
            let kids := if total == 0 then kids else
              kids.push (Html.elem "div"
                #[Html.elem "div" #[] #[("style", s!"width: {done * 100 / total}%")]]
                #[("class", "progress")])
            acc := acc.push (Html.elem "section" kids #[("class", "section-page")])
          else
            acc := acc.push (blockNode cfg (.section 1 starred title))
        | _ => acc := acc.push (blockNode cfg b)
      return (acc, walkDiags)
  diags := diags ++ sectionDiags
  let main := Html.elem "main" inner (if bodyClass.isEmpty then #[]
    else #[("class", bodyClass)])
  let mut body : Array Node := #[main]
  if let some tool := cfg.mathBoundary then
    body := body.push (Html.elem "script" #[]
      #[("data-math-boundary", tool), ("src", tool)])
  -- The landmark and anchor contracts, judged over the emitted tree.
  let facts := pageFactsList {} body.toList
  if facts.navs > 1 then
    -- One unlabeled landmark per role: "if a specific landmark role is
    -- used more than once on a page, provide each instance a unique label"
    -- (W3C ARIA Authoring Practices, Landmark Regions, Step 3 and the
    -- Navigation role). The engine has no label mechanism yet, so a second
    -- unlabeled <nav> is indistinguishable to assistive technology.
    diags := diags.push (Diag.of .W0325
      s!"{facts.navs} unlabeled <nav> landmarks on one page are \
indistinguishable to assistive technology"
      (help := some "repeated landmarks need unique labels (ARIA Landmark \
Regions): give each one a name, \\begin{nav}[label = Site]"))
  if facts.reveals > 0 then
    -- Declared reveals resolve at the page level: the CSS (declarative
    -- where the platform has scroll-driven animations) and the constant
    -- script fallback ship exactly when the tree carries one.
    head := head.push (Node.style revealCss)
  -- Every navigation target exists: an in-page link resolves to an anchor
  -- this page emits, or it is named here rather than shipped broken. '#'
  -- and any-ASCII-case 'top' always resolve — the HTML spec's fragment
  -- navigation scrolls both to the top of the document ("select the
  -- indicated part": an empty fragment, or a decoded fragment that is an
  -- ASCII case-insensitive match for 'top').
  let mut checked : Array String := #[]
  for fref in facts.fragmentRefs do
    let frag := (fref.drop 1).toString
    let isTop := frag.isEmpty || frag.map Char.toLower == "top"
    unless isTop || facts.ids.contains frag || checked.contains fref do
      checked := checked.push fref
      diags := diags.push (Diag.of .W0326
        s!"in-page link '{fref}' has no target anchor on this page"
        (help := some (if facts.ids.isEmpty then
            "this page has no anchors: a level-1 \\section title becomes \
one in the article class"
          else s!"anchors on this page: \
{String.intercalate ", " (facts.ids.toList.map ("#" ++ ·))}")))
  return (head, body, diags)

/-- Emit a document. Returns the file and any diagnostics the backend itself
raises — running content is the notable one: page furniture cannot be honoured
in a continuous document, and dropping it silently would be the kind of quiet
failure this engine exists to avoid. -/
def emit (cfg : Config) (doc : Doc) : String × Array Diag :=
  let (head, body, diags) := emitTree cfg doc
  (Html.document cfg.lang head body, diags)

end LeanTex.Core.HtmlDoc
